import OAI.Analysis.CircleDomains.Topology.CompactLineJump
import OAI.Analysis.CircleDomains.Sobolev.ParallelJumpIntegral
import OAI.Analysis.CircleDomains.Modulus.FiniteCircleLinePayment

namespace OAI

/-! Planar integration of the actual disk-filling errors. A locally
integrable gradient majorant is used only on the square containing the test. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology
namespace CircleDomainRigidity

 theorem planar_filled_horizontal_jump_of_density
    {I : Type*} [Fintype I] (c : I → ℂ) (r value A : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {L : ℝ} (hL : 0 < L) (hsub : ∀ i, closedBall (c i) (r i) ⊆ ball 0 L)
    {v F ρ G : ℂ → ℝ}
    (hv : ContDiffOn ℝ 1 v (⋃ i, closedBall (c i) (r i))ᶜ)
    (hρ : Integrable ρ)
    (hmajor : ∀ z ∈ (⋃ i, closedBall (c i) (r i))ᶜ,
      |z.re| ≤ L → |z.im| ≤ L → euclideanGradientNorm v z ≤ ρ z)
    (hF : EqOn F (clipScalar ∘ v) (⋃ i, closedBall (c i) (r i))ᶜ)
    (hfill : ∀ i, EqOn F (fun _ => clipScalar (value i)) (closedBall (c i) (r i)))
    (hcluster : ∀ i p t, p ∈ closedBall (c i) (r i) →
      MapClusterPt t (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p) v → |t - value i| ≤ A i)
    (hrep : ∀ᵐ z ∂(volume : Measure ℂ),
      deriv (F ∘ horizontalLine z.im) z.re = G z)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ ball 0 L)
    (hint : Integrable (fun z => F z * fderiv ℝ φ z 1))
    (hdint : Integrable (fun z => G z * φ z))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ z, |φ z| ≤ C) :
    |(∫ z, F z * fderiv ℝ φ z 1) + (∫ z, G z * φ z)| ≤
      4 * C * ∑ i, r i * A i := by
  let e := Complex.equivRealProdCLM.symm
  have hmp := Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd
  let f : ℝ × ℝ → ℝ := fun p => F (e p) * fderiv ℝ φ (e p) 1
  let g : ℝ × ℝ → ℝ := fun p => G (e p) * φ (e p)
  have hf : Integrable f := (hmp.integrable_comp hint.aestronglyMeasurable).mpr hint
  have hg : Integrable g := (hmp.integrable_comp hdint.aestronglyMeasurable).mpr hdint
  have hρp : Integrable (fun p : ℝ × ℝ => ρ (e p)) :=
    (hmp.integrable_comp hρ.aestronglyMeasurable).mpr hρ
  have hp : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      deriv (F ∘ horizontalLine p.2) p.1 = G (e p) :=
    hmp.quasiMeasurePreserving.ae hrep
  rw [Measure.volume_eq_prod] at hp
  have hpy := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hp)
  have hU : IsOpen (⋃ i, closedBall (c i) (r i))ᶜ :=
    (isClosed_iUnion_of_finite (fun _ => isClosed_closedBall)).isOpen_compl
  have hφd (x y : ℝ) : deriv (φ ∘ horizontalLine y) x = fderiv ℝ φ (horizontalLine y x) 1 :=
    ((hφ.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt x
      (hasDerivAt_horizontalLine x y)).deriv
  have hsline (y : ℝ) : tsupport (φ ∘ horizontalLine y) ⊆ Ioo (-L) L := by
    intro x hx
    have hz := hsupp (tsupport_comp_subset_preimage φ (continuous_horizontalLine y) hx)
    have ha : |x| < L := (Complex.abs_re_le_norm (horizontalLine y x)).trans_lt
      (by simpa only [mem_ball, dist_zero_right, horizontalLine] using hz)
    exact abs_lt.mp ha
  have hend (y : ℝ) (x : ℝ) (hx : |x| = L) : x ∈ diskLineDomain c r y := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    have hz := hsub j hj
    have ha := Complex.abs_re_le_norm (horizontalLine y x)
    have hb : ‖horizontalLine y x‖ < L := by simpa only [mem_ball, dist_zero_right, horizontalLine] using hz
    change |x| ≤ _ at ha
    rw [hx] at ha
    exact (not_lt_of_ge ha) hb
  have hline : ∀ᵐ y : ℝ,
      |(∫ x : ℝ, f (x, y)) + (∫ x : ℝ, g (x, y))| ≤
        2 * C * ∑ j, (Icc ((c j).im - r j) ((c j).im + r j)).indicator (fun _ => A j) y := by
    filter_upwards [hf.prod_left_ae, hg.prod_left_ae, hρp.prod_left_ae, hpy] with y hfy hgy hρy hry
    by_cases hy : y ∈ Icc (-L) L
    · have h₁ : (∫ x, (F ∘ horizontalLine y) x * deriv (φ ∘ horizontalLine y) x) =
          ∫ x, f (x, y) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x =>
          congrArg (fun t => F (horizontalLine y x) * t) (hφd x y)
      have h₂ : (∫ x, deriv (F ∘ horizontalLine y) x * (φ ∘ horizontalLine y) x) =
          ∫ x, g (x, y) := by
        apply integral_congr_ae
        filter_upwards [hry] with x hx
        exact congrArg (fun t => t * φ (horizontalLine y x)) hx
      have hi₁ : Integrable (fun x => (F ∘ horizontalLine y) x * deriv (φ ∘ horizontalLine y) x) := by
        apply hfy.congr
        exact Eventually.of_forall fun x =>
          congrArg (fun t => F (horizontalLine y x) * t) (hφd x y).symm
      have hi₂ : Integrable (fun x => deriv (F ∘ horizontalLine y) x * (φ ∘ horizontalLine y) x) := by
        apply hgy.congr
        filter_upwards [hry] with x hx
        exact congrArg (fun t => t * φ (horizontalLine y x)) hx.symm
      have ht := filled_line_integration_through_disks_univ c r value A hr hA hdisj
        (by linarith : -L < L) (hend y (-L) (by rw [abs_neg, abs_of_pos hL]))
        (hend y L (abs_of_pos hL))
        (hv.comp (contDiff_horizontalLine y).contDiffOn (fun _ hx => hx)) hρy
        (by
          intro x hx
          exact (horizontal_derivative_le_gradient
            ((hv.contDiffAt (hU.mem_nhds hx.2)).differentiableAt (by norm_num))).trans
            (hmajor _ hx.2 (abs_le.mpr hx.1) (abs_le.mpr hy)))
        (fun x hx => hF hx) (fun j x hx => hfill j hx)
        (fun j p t hp ht => hcluster j _ t hp (horizontal_cluster_is_planar ht))
        (hφ.comp (contDiff_horizontalLine y)) (hsline y) hi₁ hi₂ hC (fun x => hbound _)
      change |(∫ x, (F ∘ horizontalLine y) x * deriv (φ ∘ horizontalLine y) x) +
        (∫ x, deriv (F ∘ horizontalLine y) x * (φ ∘ horizontalLine y) x)| ≤ _ at ht
      rw [h₁, h₂] at ht
      exact ht
    · have hz (x : ℝ) : horizontalLine y x ∉ tsupport φ := by
        intro hx
        have hn : |y| < L := (Complex.abs_im_le_norm (horizontalLine y x)).trans_lt
          (by simpa only [mem_ball, dist_zero_right] using hsupp hx)
        exact hy ⟨(abs_lt.mp hn).1.le, (abs_lt.mp hn).2.le⟩
      have hfzero (x : ℝ) : f (x, y) = 0 := by
        change F _ * fderiv ℝ φ (horizontalLine y x) 1 = 0
        rw [fderiv_of_notMem_tsupport ℝ (hz x), zero_apply, mul_zero]
      have hgzero (x : ℝ) : g (x, y) = 0 := by
        change _ * φ (horizontalLine y x) = 0
        rw [image_eq_zero_of_notMem_tsupport (hz x), mul_zero]
      simp only [hfzero, hgzero, integral_zero, zero_add, abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hC)
        (Finset.sum_nonneg fun j _ => indicator_nonneg (fun _ _ => hA j) y)
  have hb := integral_bound_of_parallel_disk_errors c r A hr C hf hg hline
  have hfint : (∫ p, f p) = ∫ z, F z * fderiv ℝ φ z 1 := hmp.integral_comp' (fun z : ℂ => F z * fderiv ℝ φ z 1)
  have hgint : (∫ p, g p) = ∫ z, G z * φ z := hmp.integral_comp' (fun z : ℂ => G z * φ z)
  rw [hfint, hgint] at hb
  exact hb

end CircleDomainRigidity

end OAI
