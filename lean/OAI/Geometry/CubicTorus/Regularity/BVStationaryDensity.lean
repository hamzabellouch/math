import Mathlib
import OAI.Geometry.CubicTorus.Reflection.BVConeSecondaryFlux
import OAI.Geometry.CubicTorus.Estimates.BVLocalScaling

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_moving_limit_comparison {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : ℕ → MovingCenter.InteriorCenter) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hrlim : Tendsto r atTop (𝓝 0))
    {A B : Set Cover} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {R : ℝ} (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b ≤ 1) (hbR : b ≤ R)
    (hAB : A ∆ B ⊆ Metric.ball (0 : Cover) a) :
    coverLocalPerimeter A (Metric.ball (0 : Cover) b) ≤
      coverLocalPerimeter B (Metric.closedBall (0 : Cover) b) := by
  by_cases htop : coverLocalPerimeter B (Metric.closedBall (0 : Cover) b) = ⊤
  · rw [htop]; exact le_top
  let L := (coverLocalPerimeter B (Metric.closedBall (0 : Cover) b)).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hper : coverLocalPerimeter B (Metric.closedBall (0 : Cover) b) ≤ ENNReal.ofReal L :=
    (ENNReal.ofReal_toReal htop).ge
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hE hmin.1.2.ne
  obtain ⟨η,C,hη,hC,hcomp⟩ := MovingCenter.isMinimizerAt_scaled_set_replacement hV hE hmin hμ
  obtain ⟨K,hKpos,hK⟩ := smoothTransition_exists_deriv_bound
  let D : ℕ → ℝ := fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
    |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  apply iSup_le
  intro hFs
  apply iSup_le
  intro hFb
  apply iSup_le
  intro hFn
  obtain ⟨t,ht,hFt⟩ := exists_lt_subset_ball isClosed_closure hFb
  let q : ℝ := max a t
  have hq : 0 < q := ha.trans_le (le_max_left _ _)
  have hqb : q < b := max_lt hab ht
  have hFq : tsupport F ⊆ Metric.ball (0 : Cover) q := hFt.trans (Metric.ball_subset_ball (le_max_right _ _))
  have hsmall : ∀ᶠ i in atTop, r i < 3/8 ∧ r i*b < 1/4 ∧ (r i*b)^3*(Real.pi*8/3) < η := by
    have hs1 : Tendsto (fun i ↦ r i*b) atTop (𝓝 0) := by simpa using hrlim.mul_const b
    have hs2 : Tendsto (fun i ↦ (r i*b)^3*(Real.pi*8/3)) atTop (𝓝 0) := by
      simpa using (hs1.pow 3).mul_const (Real.pi*8/3)
    exact (hrlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<3/8))).and
      ((hs1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/4))).and
        (hs2.eventually (gt_mem_nhds hη)))
  have hineq : ∀ᶠ i in atTop,
      (∫ x, blowupCharacteristic E (c i) (r i) x*divergence F x) ≤
        L+2*K*b*(D i+r i)/(b^2-q^2)+C*r i*b^3 := by
    filter_upwards [hsmall] with i hi
    have herr : (∫ x in Metric.ball (0 : Cover) b,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) < D i+r i := by
      have hm := setIntegral_mono_set (blowup_error_integrable hE hA (c i) (r i) R)
        (ae_of_all _ fun x ↦ abs_nonneg _)
        ((Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hbR)).eventuallyLE)
      exact lt_of_le_of_lt hm (lt_add_of_pos_right _ (hr i))
    have hh := hcomp (c i) A B hA hB q b L K (r i) (D i+r i) hq hqb (hr i) hi.2.1 hi.2.2 hL hK hper
      (hAB.trans (Metric.ball_subset_ball (le_max_left _ _))) herr
    apply (blowup_flux_le_scaled_mass hE hμ (c i) (hr i) (hqb.le.trans hb1)
      (MovingCenter.closedBall_interior hi.1) hF hFq hFn).trans
    apply (div_le_iff₀ (sq_pos_of_pos (hr i))).mpr
    exact hh.trans_eq (by ring)
  have hf := moving_blowup_flux_tendsto hE (fun i ↦ (c i : Cover)) r hA hconv hF
    (hFb.trans (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hbR)))
  have hlim : Tendsto (fun i ↦ L+2*K*b*(D i+r i)/(b^2-q^2)+C*r i*b^3) atTop (𝓝 L) := by
    have hh := ((tendsto_const_nhds (x := L)).add
      (((tendsto_const_nhds (x := 2*K*b)).mul (hconv.add hrlim)).div_const (b^2-q^2))).add
        (((tendsto_const_nhds (x := C)).mul hrlim).mul_const (b^3))
    simpa only [zero_add,mul_zero,zero_mul,zero_div,add_zero] using hh
  exact (ENNReal.ofReal_le_ofReal (le_of_tendsto_of_tendsto hf hlim hineq)).trans_eq
    (ENNReal.ofReal_toReal htop)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_moving_limit_perimeter {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ M : ℝ, 0 < M ∧ ∀ (c : ℕ → MovingCenter.InteriorCenter) (r : ℕ → ℝ),
      (∀ i, 0 < r i) → Tendsto r atTop (𝓝 0) →
      ∀ A : Set Cover, MeasurableSet A → ∀ R : ℝ,
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
        |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) →
      ∀ b : ℝ, 0 < b → b ≤ 1 → b ≤ R →
      coverLocalPerimeter A (Metric.ball (0 : Cover) b) ≤ ENNReal.ofReal (M*b^2) := by
  obtain ⟨S,M,hS,hM,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hE hmin.1.2.ne
  refine ⟨M,hM,?_⟩
  intro c r hr hrlim A hA R hconv b hb hb1 hbR
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  apply iSup_le
  intro hFs
  apply iSup_le
  intro hs
  apply iSup_le
  intro hn
  have hsmall : ∀ᶠ i in atTop, r i < 3/8 ∧ r i*b < S := by
    have ht : Tendsto (fun i ↦ r i*b) atTop (𝓝 0) := by simpa using hrlim.mul_const b
    exact (hrlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<3/8))).and
      (ht.eventually (gt_mem_nhds hS))
  have hineq : ∀ᶠ i in atTop, (∫ x, blowupCharacteristic E (c i) (r i) x*divergence F x) ≤ M*b^2 := by
    filter_upwards [hsmall] with i hi
    apply (blowup_flux_le_scaled_mass hE hμ (c i) (hr i) hb1
      (MovingCenter.closedBall_interior hi.1) hF hs hn).trans
    apply (div_le_iff₀ (sq_pos_of_pos (hr i))).mpr
    exact (harea μ hμ _ _ (mul_pos (hr i) hb) hi.2.le).trans_eq (by ring)
  have ht := moving_blowup_flux_tendsto hE (fun i ↦ (c i : Cover)) r hA hconv hF
    (hs.trans (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hbR)))
  exact ENNReal.ofReal_le_ofReal (le_of_tendsto ht hineq)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma radial_cone_secondary_unit_line {A B : Set Cover} (hA : MeasurableSet A)
    (hB : MeasurableSet B)
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    (p : Cover) (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (p+r i • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0))
    (t : ℝ) (ht : |t| ≤ 1/4) :
    ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) (1/4) →
      (x+t • (‖p‖⁻¹ • p) ∈ B ↔ x ∈ B) := by
  have hpn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp0
  have ht' : |t*‖p‖⁻¹| * ‖p‖ ≤ 1/4 := by
    simpa only [abs_mul,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg p)),mul_assoc,
      inv_mul_cancel₀ hpn,mul_one] using ht
  simpa only [smul_smul,add_comm] using radial_cone_secondary_line_invariance hA hB
    (fun ψ hψ hs ↦ cone_radial_euler hA hcone hψ hs) p hp r hr hrlim
      (by simpa only [add_comm] using hconv) (t*‖p‖⁻¹) ht'

theorem actual_cone_secondary_product_comparison {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
      atTop (𝓝 0))
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    (p : Cover) (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) (hs1 : ∀ i, s i ≤ 1) (hslim : Tendsto s atTop (𝓝 0)) :
    ∃ B : Set Cover, MeasurableSet B ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
        |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (φ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      (∃ M : ℝ, 0 < M ∧ ∀ b : ℝ, 0 < b → b ≤ 1 →
        coverLocalPerimeter B (Metric.ball (0 : Cover) b) ≤ ENNReal.ofReal (M*b^2)) ∧
      (∀ D : Set Cover, MeasurableSet D → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
        B ∆ D ⊆ Metric.ball (0 : Cover) a →
        coverLocalPerimeter B (Metric.ball (0 : Cover) b) ≤
          coverLocalPerimeter D (Metric.closedBall (0 : Cover) b)) ∧
      (∃ C : Set (Fin 2 → ℝ), MeasurableSet C ∧
        ∀ᵐ z : ℝ × (Fin 2 → ℝ) ∂volume,
          |z.1| < 1/16 → ‖normalProductChart (‖p‖⁻¹ • p) (0,z.2)‖ < 1/16 →
            (normalProductChart (‖p‖⁻¹ • p) z ∈ B ↔ z.2 ∈ C)) := by
  obtain ⟨B,hB,φ,hφ,hBconv,c,q,hc,hq,hqlim,hactual⟩ :=
    actual_tangent_secondary_representation hV hE hmin r hr hrlim hA hconv p hp s hs hs1 hslim
  let c' : ℕ → MovingCenter.InteriorCenter := fun i ↦ ⟨c i,hc i⟩
  obtain ⟨M,hM,hper⟩ := isMinimizerAt_moving_limit_perimeter hV hE hmin
  have hn : ‖‖p‖⁻¹ • p‖ = 1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg p)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp0)]
  refine ⟨B,hB,φ,hφ,hBconv,⟨M,hM,?_⟩,?_,?_⟩
  · intro b hb hb1
    exact hper c' q hq hqlim B hB 1 hactual b hb hb1 hb1
  · intro D hD a b ha hab hb1 hBD
    exact isMinimizerAt_moving_limit_comparison hV hE hmin c' q hq hqlim
      hB hD hactual ha hab hb1 hb1 hBD
  · apply line_invariant_local_product hB hn
    intro t ht
    exact radial_cone_secondary_unit_line hA hB hcone p hp hp0
      (fun i ↦ s (φ i)) (fun i ↦ hs (φ i)) (hslim.comp hφ.tendsto_atTop) hBconv t ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalScalarTest_plane_derivative (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {χ : ℝ → ℝ} {φ : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Cover) (u : Plane) :
    fderiv ℝ (normalScalarTest a n χ φ) x (normalPlaneEmbedding n u) =
      χ ⟪n,x-a⟫*fderiv ℝ φ (normalPlaneCoordinates n (x-a)) u := by
  have hf := normalScalarTest_contDiff a n hχ hφ
  have hl : HasDerivAt (fun t : ℝ ↦ x+t • normalPlaneEmbedding n u)
      (normalPlaneEmbedding n u) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (normalPlaneEmbedding n u)).const_add x
  have hd := ((hf.differentiable (by simp)) (x+(0 : ℝ) • normalPlaneEmbedding n u)).hasFDerivAt.comp_hasDerivAt 0 hl
  have hl' : HasDerivAt (fun t : ℝ ↦ normalPlaneCoordinates n (x-a)+t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add (normalPlaneCoordinates n (x-a))
  have hd' := (((hφ.differentiable (by simp)) (normalPlaneCoordinates n (x-a)+(0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt 0 hl').const_mul (χ ⟪n,x-a⟫)
  have he : (fun t : ℝ ↦ normalScalarTest a n χ φ (x+t • normalPlaneEmbedding n u)) =
      (fun t : ℝ ↦ χ ⟪n,x-a⟫*φ (normalPlaneCoordinates n (x-a)+t • u)) :=
    funext (normalScalarTest_plane_line a hn χ φ x u)
  have hd0 : HasDerivAt (fun t : ℝ ↦ normalScalarTest a n χ φ (x+t • normalPlaneEmbedding n u))
      (fderiv ℝ (normalScalarTest a n χ φ) x (normalPlaneEmbedding n u)) 0 := by
    simpa only [Function.comp_def,zero_smul,add_zero] using hd
  rw [he] at hd0
  simpa using hd0.unique hd'

lemma divergence_planar_product_test {n : Cover} (hn : ‖n‖ = 1)
    {χ : ℝ → ℝ} {φ : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (u : Plane) (x : Cover) :
    divergence (fun z ↦ normalScalarTest 0 n χ φ z • normalPlaneEmbedding n u) x =
      χ ⟪n,x⟫*fderiv ℝ φ (normalPlaneCoordinates n x) u := by
  rw [divergence_smul_const ((normalScalarTest_contDiff 0 n hχ hφ).differentiable (by simp) x),
    normalScalarTest_plane_derivative 0 hn hχ hφ]
  simp only [sub_zero]

lemma line_product_euclidean {B : Set Cover} {C : Set (Fin 2 → ℝ)} (hC : MeasurableSet C)
    {n : Cover}
    (hprod : ∀ᵐ z : ℝ × (Fin 2 → ℝ) ∂volume,
      |z.1| < 1/16 → ‖normalProductChart n (0,z.2)‖ < 1/16 →
        (normalProductChart n z ∈ B ↔ z.2 ∈ C)) :
    ∃ D : Set Plane, MeasurableSet D ∧
      ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
        (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ D) := by
  let D : Set Plane := WithLp.ofLp ⁻¹' C
  have hm : MeasurePreserving (fun z : ℝ × Plane ↦ (z.1,WithLp.ofLp z.2)) := by
    change MeasurePreserving (Prod.map id (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm) volume volume
    simpa only [Measure.volume_eq_prod] using (MeasurePreserving.id (volume : Measure ℝ)).prod
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))
  refine ⟨D,hC.preimage (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurable,?_⟩
  filter_upwards [hm.quasiMeasurePreserving.ae hprod] with z hz ht hy
  have hy' : ‖normalProductChart n (0,WithLp.ofLp z.2)‖ < 1/16 := by
    change ‖normalPlaneEmbedding n z.2‖ < 1/16
    rwa [normalPlaneEmbedding_norm]
  change 0+normalProductChart n (z.1,WithLp.ofLp z.2) ∈ B ↔ WithLp.ofLp z.2 ∈ C
  rw [zero_add]
  exact hz ht hy'

theorem planar_product_flux {B : Set Cover} {C : Set Plane} (hB : MeasurableSet B)
    (hC : MeasurableSet C) {n : Cover} (hn : ‖n‖ = 1)
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    {χ : ℝ → ℝ} {φ : Plane → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsχ : tsupport χ ⊆ Icc (-(1/32 : ℝ)) (1/32))
    (hsφ : tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32)) (u : Plane) :
    (∫ x in B, divergence (fun z ↦ normalScalarTest 0 n χ φ z • normalPlaneEmbedding n u) x) =
      (∫ t, χ t)*(∫ y in C, fderiv ℝ φ y u) := by
  let F : Cover → Cover := fun z ↦ normalScalarTest 0 n χ φ z • normalPlaneEmbedding n u
  rw [← integral_indicator hB]
  rw [← (normalColumnChart_measurePreserving 0 n).integral_comp']
  change (∫ z : ℝ × Plane, B.indicator (divergence F) (normalColumnChart 0 n z)) = _
  have he : (fun z : ℝ × Plane ↦ B.indicator (divergence F) (normalColumnChart 0 n z)) =ᵐ[volume]
      (fun z ↦ χ z.1*C.indicator (fun y ↦ fderiv ℝ φ y u) z.2) := by
    filter_upwards [hprod] with z hz
    have hdiv : divergence F (normalColumnChart 0 n z) = χ z.1*fderiv ℝ φ z.2 u := by
      rw [divergence_planar_product_test hn hχ hφ]
      rw [← sub_zero (normalColumnChart 0 n z),normalColumnChart_height 0 hn,
        normalColumnChart_projection 0 hn]
    by_cases ht : |z.1| < 1/16
    · by_cases hy : ‖z.2‖ < 1/16
      · by_cases hc : z.2 ∈ C
        · rw [indicator_of_mem ((hz ht hy).mpr hc),indicator_of_mem hc,hdiv]
        · rw [indicator_of_notMem hc,mul_zero,indicator_of_notMem (mt (hz ht hy).mp hc)]
      · have hnot : z.2 ∉ tsupport φ := by
          intro hh
          have hh' : ‖z.2‖ ≤ 1/32 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hsφ hh
          exact hy (by linarith)
        have hd : fderiv ℝ φ z.2 u = 0 := by rw [fderiv_of_notMem_tsupport ℝ hnot]; rfl
        simp only [hd,mul_zero] at hdiv
        by_cases hc : z.2 ∈ C <;> by_cases hb : normalColumnChart 0 n z ∈ B <;>
          simp [hc,hb,hdiv,hd]
    · have hc : χ z.1 = 0 := image_eq_zero_of_notMem_tsupport (by
        intro hh
        have h := hsχ hh
        exact ht (abs_lt.mpr ⟨by linarith [h.1],by linarith [h.2]⟩))
      simp only [hc,zero_mul] at hdiv ⊢
      by_cases hb : normalColumnChart 0 n z ∈ B <;> simp [hb,hdiv]
  rw [integral_congr_ae he,Measure.volume_eq_prod,integral_prod_mul,integral_indicator hC]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem weakCMC_moving_blowup_limit_stationary {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R : ℝ} (hR : 1 < R)
    (hc : ∀ i, Metric.closedBall (c i) (r i) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hlim : Tendsto (fun i ↦ blowupNormalMeasure μ (c i) (r i) R) l (𝓝 ν))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have ht := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) (blowupTangentTest hF hFs)
  have hf := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) (blowupFluxTest hF.continuous hFs)
  have hh := (hrlim.mul_const H).mul hf
  simp only [zero_mul] at hh
  have he (i) := weakCMC_blowup_identity hμ hH hF hs (c i) (hr i) hR (hc i)
  exact tendsto_nhds_unique ht (hh.congr (fun i ↦ (he i).symm))

theorem moving_blowup_normal_limit_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R : ℝ} (hR : 1 < R)
    (hc : ∀ i, Metric.closedBall (c i) (r i) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    {l : Filter ℕ} [NeBot l] {ν : FiniteMeasure BlowupNormalBundle}
    (hν : Tendsto (fun i ↦ blowupNormalMeasure μ (c i) (r i) R) l (𝓝 ν))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
      ∫ x in A, divergence F x := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have hf := moving_blowup_flux_tendsto hE c r hA hconv hF hs
  have hweak := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν) (blowupFluxTest hF.continuous hFs)
  have he (i) : (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(blowupNormalMeasure μ (c i) (r i) R : Measure BlowupNormalBundle)) =
      ∫ x, blowupCharacteristic E (c i) (r i) x*divergence F x := by
    rw [integral_blowup_test μ (c i) (hr i) (continuous_blowupFluxTest hF.continuous)
      (fun z hz ↦ by
        have hn : z.1 ∉ tsupport F := fun hh ↦ hz (Metric.closedBall_subset_ball hR (hs hh))
        simp [image_eq_zero_of_notMem_tsupport hn])]
    change (r i)⁻¹^2*(∫ z, ⟪(z.2 : Cover),F ((r i)⁻¹ • ((z.1 : Cover)-c i))⟫ ∂(μ : Measure NormalBundle)) = _
    rw [show (r i)⁻¹^2 = ((r i)^2)⁻¹ by ring]
    rw [← div_eq_inv_mul,normalMeasure_scaled_flux hE hμ hF hs (c i) (hr i) (hc i)]
    simp only [blowupCharacteristic,add_comm (c i)]
  exact tendsto_nhds_unique (hweak.congr fun i ↦ he i) hf

theorem moving_blowup_normal_cluster {μ : FiniteMeasure NormalBundle}
    (c : ℕ → Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ i, cellBallMass μ (c i) (r i*R) ≤ A*(r i)^2) :
    ∃ ν : FiniteMeasure BlowupNormalBundle,
      (ν.mass : ℝ) ≤ A ∧ ν ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0 ∧
      MapClusterPt ν atTop (fun i ↦ blowupNormalMeasure μ (c i) (r i) R) := by
  have hm (i) : (blowupNormalMeasure μ (c i) (r i) R).mass ≤ Real.toNNReal A := by
    rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ hA,blowupNormalMeasure_mass]
    calc
      _ ≤ (r i)⁻¹^2*(A*(r i)^2) := mul_le_mul_of_nonneg_left (hb i) (sq_nonneg _)
      _ = A := by field_simp [(hr i).ne']
  have hK : IsCompact (Metric.closedBall (0 : Cover) R ×ˢ (univ : Set NormalSphere)) :=
    (isCompact_closedBall _ _).prod isCompact_univ
  obtain ⟨ν,hν,hcl⟩ := (isCompact_setOfPred_finiteMeasure_le_of_isCompact
    (Real.toNNReal A) hK).exists_mapClusterPt
      (show Filter.map (fun i ↦ blowupNormalMeasure μ (c i) (r i) R) atTop ≤
        𝓟 {ν | ν.mass ≤ Real.toNNReal A ∧
          ν ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0} from
        tendsto_principal.mpr (Eventually.of_forall fun i ↦
          ⟨hm i,blowupNormalMeasure_supported μ (c i) (hr i) R⟩))
  refine ⟨ν,?_,hν.2,hcl⟩
  simpa only [Real.coe_toNNReal _ hA] using (NNReal.coe_le_coe.mpr hν.1)

theorem isMinimizerAt_moving_paired_normal_limit {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    (c : ℕ → MovingCenter.InteriorCenter) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hrlim : Tendsto r atTop (𝓝 0)) {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0)) :
    ∃ (ν : FiniteMeasure BlowupNormalBundle) (k : ℕ) (U : Ultrafilter ℕ),
      (U : Filter ℕ) ≤ atTop ∧
      Tendsto (fun i ↦ blowupNormalMeasure μ (c (i+k)) (r (i+k)) 2) U (𝓝 ν) ∧
      ν ((Metric.closedBall (0 : Cover) 2 ×ˢ univ)ᶜ) = 0 ∧
      ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
        (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 ∧
        (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x := by
  obtain ⟨S,B,hS,hB,harea⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  have hsmall : 0 < min (3/16 : ℝ) (S/2) := by positivity
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hrlim.eventually (gt_mem_nhds hsmall))
  let q : ℕ → ℝ := fun i ↦ r (i+k)
  let d : ℕ → Cover := fun i ↦ c (i+k)
  have hq (i) : 0 < q i := hr _
  have hqb (i) : q i < min (3/16 : ℝ) (S/2) := hk _ (by omega)
  have hchart (i) : Metric.closedBall (d i) (q i*2) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    MovingCenter.closedBall_interior (c := c (i+k)) (by
      have hh := (hqb i).trans_le (min_le_left _ _)
      linarith)
  have hmass (i) : cellBallMass μ (d i) (q i*2) ≤ (B*4)*(q i)^2 := by
    rw [cellBallMass_eq_spatialNormalMeasure μ (d i) _ (Metric.ball_subset_closedBall.trans (hchart i))]
    have hh := harea μ hμ (quotientMap (d i)) (q i*2) (mul_pos (hq i) (by norm_num)) (by
      have hh := (hqb i).trans_le (min_le_right _ _)
      linarith)
    convert hh using 1
    ring
  obtain ⟨ν,_,hsup,hcl⟩ := moving_blowup_normal_cluster d q hq (by positivity : 0 ≤ B*4) hmass
  obtain ⟨U,hU,hν⟩ := mapClusterPt_iff_ultrafilter.mp hcl
  have hqlim : Tendsto q (U : Filter ℕ) (𝓝 0) :=
    (hrlim.comp (tendsto_add_atTop_nat k)).mono_left hU
  have hc1 (i) : Metric.closedBall (d i) (q i) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    (Metric.closedBall_subset_closedBall (by have hh := hq i; linarith)).trans (hchart i)
  have hconv' : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (d i) (q i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        (U : Filter ℕ) (𝓝 0) := (hconv.comp (tendsto_add_atTop_nat k)).mono_left hU
  refine ⟨ν,k,U,hU,hν,hsup,?_⟩
  intro F hF hs
  exact ⟨weakCMC_moving_blowup_limit_stationary hμ hH d q hq (by norm_num) hc1 hqlim hν hF hs,
    moving_blowup_normal_limit_flux hE hμ d q hq (by norm_num) hc1 hν hA hconv' hF hs⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def euclideanRadialMass (ν : FiniteMeasure BlowupNormalBundle) (a : Cover) (ε r : ℝ) : ℝ :=
  ∫ z, radialDensityWeight a r ε z.1 ∂(ν : Measure BlowupNormalBundle)

def euclideanBallMass (ν : FiniteMeasure BlowupNormalBundle) (a : Cover) (r : ℝ) : ℝ :=
  (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball a r}

lemma integrable_euclideanRadialWeight (μ : FiniteMeasure BlowupNormalBundle) (a : Cover) (r ε : ℝ) :
    Integrable (fun z : BlowupNormalBundle ↦ radialDensityWeight a r ε z.1) (μ : Measure BlowupNormalBundle) := by
  apply Integrable.of_bound (((radialDensityWeight_contDiff a r ε).continuous.comp continuous_fst).measurable.aestronglyMeasurable) 1
  exact ae_of_all _ (fun z ↦ by
    change |radialDensityWeight a r ε z.1| ≤ 1
    rw [abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact Real.smoothTransition.le_one _)

lemma integrable_euclideanRadialSlope (μ : FiniteMeasure BlowupNormalBundle) (a : Cover) (r ε : ℝ) :
    Integrable (fun z : BlowupNormalBundle ↦ radialDensitySlope a r ε z.1) (μ : Measure BlowupNormalBundle) := by
  obtain ⟨K, _, hK⟩ := smoothTransition_exists_deriv_bound
  apply Integrable.of_bound (((continuous_radialDensitySlope a r ε).comp continuous_fst).measurable.aestronglyMeasurable) (K/|ε|)
  apply ae_of_all
  intro z
  change |radialDensitySlope a r ε z.1| ≤ K/|ε|
  simp only [radialDensitySlope,abs_div]
  exact div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hK ((r^2-‖z.1-a‖^2)/ε)) (abs_nonneg _)

lemma hasDerivAt_euclideanRadialMass (μ : FiniteMeasure BlowupNormalBundle) (a : Cover)
    {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    HasDerivAt (euclideanRadialMass μ a ε)
      (∫ z, 2 * r * radialDensitySlope a r ε z.1 ∂(μ : Measure BlowupNormalBundle)) r := by
  obtain ⟨K, hK, hb⟩ := smoothTransition_exists_deriv_bound
  have hs : Ioo (r - 1) (r + 1) ∈ 𝓝 r := Ioo_mem_nhds (by linarith) (by linarith)
  have hm (s : ℝ) : AEStronglyMeasurable
      (fun z : BlowupNormalBundle ↦ radialDensityWeight a s ε z.1) (μ : Measure BlowupNormalBundle) :=
    (integrable_euclideanRadialWeight μ a s ε).aestronglyMeasurable
  have hm' : AEStronglyMeasurable
      (fun z : BlowupNormalBundle ↦ 2 * r * radialDensitySlope a r ε z.1) (μ : Measure BlowupNormalBundle) :=
    ((integrable_euclideanRadialSlope μ a r ε).const_mul _).aestronglyMeasurable
  have hb' : ∀ᵐ z ∂(μ : Measure BlowupNormalBundle), ∀ s ∈ Ioo (r - 1) (r + 1),
      ‖2 * s * radialDensitySlope a s ε z.1‖ ≤ 2 * (|r| + 1) * K / ε := by
    filter_upwards [] with z s hs
    have hsr : |s| ≤ |r| + 1 := by
      rw [abs_le]
      constructor <;> nlinarith [le_abs_self r, neg_abs_le r, hs.1, hs.2]
    have hsl : |radialDensitySlope a s ε z.1| ≤ K / ε := by
      simp only [radialDensitySlope, abs_div, abs_of_pos hε]
      exact div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hb ((s ^ 2 - ‖(z.1 : Cover) - a‖ ^ 2) / ε)) hε.le
    simp only [Real.norm_eq_abs, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
    calc
      2 * |s| * |radialDensitySlope a s ε z.1| ≤ 2 * (|r| + 1) * (K / ε) :=
        mul_le_mul (by nlinarith) hsl (abs_nonneg _) (by positivity)
      _ = _ := by ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs (Eventually.of_forall hm)
    (integrable_euclideanRadialWeight μ a r ε) hm' hb' (integrable_const _)
    (Eventually.of_forall fun z s _ ↦ hasDerivAt_radialDensityWeight a z.1 s ε)).2

lemma euclideanRadialMass_nonneg (μ : FiniteMeasure BlowupNormalBundle) (a : Cover) (ε r : ℝ) :
    0 ≤ euclideanRadialMass μ a ε r :=
  integral_nonneg (fun _ ↦ radialDensityWeight_nonneg _ _ _ _)

theorem stationary_euclideanRadialMass_ode {ν : FiniteMeasure BlowupNormalBundle}
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0)
    (a : Cover) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hc : Metric.closedBall a r ⊆ Metric.closedBall (0 : Cover) 1) :
    2 * euclideanRadialMass ν a ε r ≤ r * deriv (euclideanRadialMass ν a ε) r := by
  let F := radialDensityField a r ε
  have hf := radialDensityField_contDiff a r ε
  have hs := radialDensityField_hasCompactSupport (a := a) hr.le hε
  have hid := hstat F hf ((radialDensityField_tsupport hr.le hε).trans hc)
  have ht : Integrable (fun z : BlowupNormalBundle ↦ tangentialDivergence F z.1 z.2)
      (ν : Measure BlowupNormalBundle) :=
    BoundedContinuousFunction.integrable _ (blowupTangentTest hf hs)
  have hw := integrable_euclideanRadialWeight ν a r ε
  have hsl := integrable_euclideanRadialSlope ν a r ε
  have hbound := integral_mono (hw.const_mul 2) (ht.add (hsl.const_mul (2*r^2)))
    (fun z : BlowupNormalBundle ↦ radialDensityField_dilation_bound z.2.property a z.1 hr.le hε)
  simp only [Pi.add_apply] at hbound
  rw [integral_const_mul,integral_add ht (hsl.const_mul _),integral_const_mul,hid] at hbound
  rw [(hasDerivAt_euclideanRadialMass ν a hε r).deriv,integral_const_mul]
  change 2 * euclideanRadialMass ν a ε r ≤ _ at hbound
  nlinarith

lemma euclideanRadialMass_tendsto (ν : FiniteMeasure BlowupNormalBundle) (a : Cover)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ε : ℝ ↦ euclideanRadialMass ν a ε r) (𝓝[>] 0) (𝓝 (euclideanBallMass ν a r)) := by
  have hm (ε : ℝ) := (integrable_euclideanRadialWeight ν a r ε).aestronglyMeasurable
  have hb (ε : ℝ) : ∀ᵐ z ∂(ν : Measure BlowupNormalBundle), ‖radialDensityWeight a r ε z.1‖ ≤ (1 : ℝ) := by
    filter_upwards [] with z
    rw [Real.norm_eq_abs,abs_of_nonneg (radialDensityWeight_nonneg _ _ _ _)]
    exact Real.smoothTransition.le_one _
  have ht := tendsto_integral_filter_of_dominated_convergence (fun _ : BlowupNormalBundle ↦ (1 : ℝ))
    (Eventually.of_forall hm) (Eventually.of_forall hb) (integrable_const _)
    (Eventually.of_forall fun z : BlowupNormalBundle ↦ radialDensityWeight_tendsto a z.1 hr)
  have he : (fun z : BlowupNormalBundle ↦ (Metric.ball a r).indicator (fun _ : Cover ↦ (1 : ℝ)) z.1) =
      {z : BlowupNormalBundle | z.1 ∈ Metric.ball a r}.indicator 1 := by
    ext z
    by_cases hz : z.1 ∈ Metric.ball a r
    · rw [indicator_of_mem hz,indicator_of_mem (show z ∈ {z : BlowupNormalBundle | z.1 ∈ Metric.ball a r} from hz)]; rfl
    · rw [indicator_of_notMem hz,indicator_of_notMem (show z ∉ {z : BlowupNormalBundle | z.1 ∈ Metric.ball a r} from hz)]
  rw [he,integral_indicator_one (s := {z : BlowupNormalBundle | z.1 ∈ Metric.ball a r})
    (Metric.isOpen_ball.measurableSet.preimage measurable_fst)] at ht
  simpa only [smul_eq_mul,mul_one,euclideanRadialMass,euclideanBallMass] using ht

theorem stationary_euclideanBallMass_monotone {ν : FiniteMeasure BlowupNormalBundle}
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0)
    (a : Cover) {R : ℝ} (hc : Metric.closedBall a R ⊆ Metric.closedBall (0 : Cover) 1) :
    MonotoneOn (fun r : ℝ ↦ euclideanBallMass ν a r/r^2) (Ioc 0 R) := by
  have hs (ε : ℝ) (hε : 0 < ε) : MonotoneOn (fun r : ℝ ↦ euclideanRadialMass ν a ε r/r^2) (Ioc 0 R) := by
    have ho (r : ℝ) (hr : r ∈ Ioc 0 R) :
        (2 - 0 * r) * euclideanRadialMass ν a ε r ≤ r * deriv (euclideanRadialMass ν a ε) r := by
      have hh := stationary_euclideanRadialMass_ode hstat a hr.1 hε
        ((Metric.closedBall_subset_closedBall hr.2).trans hc)
      simpa only [zero_mul,sub_zero] using hh
    have hh := cmcDensityRatio_monotoneOn (k := 0) (R := R)
      (m := euclideanRadialMass ν a ε) (d := fun r ↦ deriv (euclideanRadialMass ν a ε) r)
      (fun r _ ↦ (hasDerivAt_euclideanRadialMass ν a hε r).differentiableAt.hasDerivAt) ho
    simpa using hh
  intro r hr s hs' hrs
  have hlr := (euclideanRadialMass_tendsto ν a hr.1).div_const (r^2)
  have hls := (euclideanRadialMass_tendsto ν a hs'.1).div_const (s^2)
  apply le_of_tendsto_of_tendsto hlr hls
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hs ε hε hr hs' hrs

theorem stationary_euclideanBallMass_density {ν : FiniteMeasure BlowupNormalBundle}
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0)
    (a : Cover) {R : ℝ} (hR : 0 < R)
    (hc : Metric.closedBall a R ⊆ Metric.closedBall (0 : Cover) 1) :
    ∃ θ : ℝ, 0 ≤ θ ∧ Tendsto (fun r : ℝ ↦ euclideanBallMass ν a r/r^2) (𝓝[>] 0) (𝓝 θ) := by
  apply exists_density_of_cmc_monotone (m := euclideanBallMass ν a) (k := 0) hR (fun _ _ ↦ ENNReal.toReal_nonneg)
  simpa using stationary_euclideanBallMass_monotone hstat a hc

lemma stationary_euclideanBallMass_upper {ν : FiniteMeasure BlowupNormalBundle}
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0)
    (a : Cover) {R : ℝ} (hR : 0 < R)
    (hc : Metric.closedBall a R ⊆ Metric.closedBall (0 : Cover) 1)
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    euclideanBallMass ν a r ≤ (euclideanBallMass ν a R/R^2)*r^2 := by
  exact (div_le_iff₀ (sq_pos_of_pos hr)).mp
    (stationary_euclideanBallMass_monotone hstat a hc ⟨hr,hrR⟩ ⟨hR,le_rfl⟩ hrR)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def euclideanNormalMap (c : Cover) (r : ℝ) (z : BlowupNormalBundle) : BlowupNormalBundle :=
  (r⁻¹ • ((z.1 : Cover)-c),z.2)

lemma continuous_euclideanNormalMap (c : Cover) (r : ℝ) :
    Continuous (euclideanNormalMap c r) := by
  have hx : Continuous (fun z : BlowupNormalBundle ↦ (z.1 : Cover)) :=
    continuous_fst
  exact ((hx.sub continuous_const).const_smul r⁻¹).prodMk continuous_snd

def euclideanNormalMeasure (μ : FiniteMeasure BlowupNormalBundle) (c : Cover) (r R : ℝ) :
    FiniteMeasure BlowupNormalBundle :=
  Real.toNNReal (r⁻¹^2) •
    (μ.restrict {z | (z.1 : Cover) ∈ Metric.ball c (r*R)}).map (euclideanNormalMap c r)

lemma euclideanNormalMeasure_mass (μ : FiniteMeasure BlowupNormalBundle) (c : Cover) (r R : ℝ) :
    ((euclideanNormalMeasure μ c r R).mass : ℝ) = r⁻¹^2*euclideanBallMass μ c (r*R) := by
  change (((Real.toNNReal (r⁻¹^2) •
    (μ.restrict {z | (z.1 : Cover) ∈ Metric.ball c (r*R)}).map (euclideanNormalMap c r)) univ) : ℝ) = _
  rw [FiniteMeasure.smul_apply,FiniteMeasure.map_apply _
    (continuous_euclideanNormalMap c r).measurable MeasurableSet.univ]
  rw [Set.preimage_univ,FiniteMeasure.restrict_apply _ _ MeasurableSet.univ,univ_inter]
  change (Real.toNNReal (r⁻¹^2) : ℝ) *
    (((μ : Measure BlowupNormalBundle) {z | (z.1 : Cover) ∈ Metric.ball c (r*R)}).toNNReal : ℝ) = _
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

lemma euclideanNormalMap_mem (c : Cover) {r : ℝ} (hr : 0 < r) (R : ℝ)
    (z : BlowupNormalBundle) :
    (euclideanNormalMap c r z).1 ∈ Metric.ball (0 : Cover) R ↔
      (z.1 : Cover) ∈ Metric.ball c (r*R) := by
  simp only [euclideanNormalMap,Metric.mem_ball,dist_eq_norm,sub_zero,norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  rw [← div_eq_inv_mul,div_lt_iff₀ hr]
  rw [mul_comm R r]

lemma euclideanNormalMeasure_supported (μ : FiniteMeasure BlowupNormalBundle) (c : Cover)
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    euclideanNormalMeasure μ c r R ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0 := by
  have hm : MeasurableSet ((Metric.closedBall (0 : Cover) R ×ˢ (univ : Set NormalSphere))ᶜ) :=
    (Metric.isClosed_closedBall.measurableSet.prod MeasurableSet.univ).compl
  have he : (euclideanNormalMap c r ⁻¹' ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ)) ∩
      {z : BlowupNormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*R)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.1 ⟨Metric.ball_subset_closedBall ((euclideanNormalMap_mem c hr R z).mpr hz.2),mem_univ _⟩
  unfold euclideanNormalMeasure
  rw [FiniteMeasure.smul_apply,
    FiniteMeasure.map_apply _ (continuous_euclideanNormalMap c r).measurable hm,
    FiniteMeasure.restrict_apply _ _ (hm.preimage (continuous_euclideanNormalMap c r).measurable),he]
  simp [FiniteMeasure.coeFn_def]

theorem euclideanNormalMeasure_cluster {μ : FiniteMeasure BlowupNormalBundle}
    (c : Cover) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {R A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ i, euclideanBallMass μ c (r i*R) ≤ A*(r i)^2) :
    ∃ ν : FiniteMeasure BlowupNormalBundle,
      (ν.mass : ℝ) ≤ A ∧ ν ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0 ∧
      MapClusterPt ν atTop (fun i ↦ euclideanNormalMeasure μ c (r i) R) := by
  have hm (i) : (euclideanNormalMeasure μ c (r i) R).mass ≤ Real.toNNReal A := by
    rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ hA,euclideanNormalMeasure_mass]
    calc
      _ ≤ (r i)⁻¹^2*(A*(r i)^2) := mul_le_mul_of_nonneg_left (hb i) (sq_nonneg _)
      _ = A := by field_simp [(hr i).ne']
  have hK : IsCompact (Metric.closedBall (0 : Cover) R ×ˢ (univ : Set NormalSphere)) :=
    (isCompact_closedBall _ _).prod isCompact_univ
  obtain ⟨ν,hν,hcl⟩ := (isCompact_setOfPred_finiteMeasure_le_of_isCompact
    (Real.toNNReal A) hK).exists_mapClusterPt
      (show Filter.map (fun i ↦ euclideanNormalMeasure μ c (r i) R) atTop ≤
        𝓟 {ν | ν.mass ≤ Real.toNNReal A ∧
          ν ((Metric.closedBall (0 : Cover) R ×ˢ univ)ᶜ) = 0} from
        tendsto_principal.mpr (Eventually.of_forall fun i ↦
          ⟨hm i,euclideanNormalMeasure_supported μ c (hr i) R⟩))
  refine ⟨ν,?_,hν.2,hcl⟩
  simpa only [Real.coe_toNNReal _ hA] using (NNReal.coe_le_coe.mpr hν.1)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma integral_euclideanNormalMeasure (μ : FiniteMeasure BlowupNormalBundle) (c : Cover)
    (r R : ℝ) {g : BlowupNormalBundle → ℝ} (hg : Continuous g) :
    (∫ z, g z ∂(euclideanNormalMeasure μ c r R : Measure BlowupNormalBundle)) =
      r⁻¹^2 * ∫ z in {z : BlowupNormalBundle | (z.1 : Cover) ∈ Metric.ball c (r*R)},
        g (euclideanNormalMap c r z) ∂(μ : Measure BlowupNormalBundle) := by
  rw [euclideanNormalMeasure,FiniteMeasure.toMeasure_smul,integral_smul_nnreal_measure,
    FiniteMeasure.toMeasure_map,integral_map
      (continuous_euclideanNormalMap c r).measurable.aemeasurable hg.measurable.aestronglyMeasurable]
  change (Real.toNNReal (r⁻¹^2) : ℝ) * _ = _
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  rfl

lemma integral_euclidean_normal_test (μ : FiniteMeasure BlowupNormalBundle) (c : Cover)
    {r R : ℝ} (hr : 0 < r) {g : BlowupNormalBundle → ℝ} (hg : Continuous g)
    (hzero : ∀ z, z.1 ∉ Metric.ball (0 : Cover) R → g z = 0) :
    (∫ z, g z ∂(euclideanNormalMeasure μ c r R : Measure BlowupNormalBundle)) =
      r⁻¹^2 * ∫ z, g (euclideanNormalMap c r z) ∂(μ : Measure BlowupNormalBundle) := by
  rw [integral_euclideanNormalMeasure μ c r R hg]
  congr 1
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact hzero _ (by rwa [euclideanNormalMap_mem c hr R z])

lemma stationary_euclidean_normal_identity {ν : FiniteMeasure BlowupNormalBundle}
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0)
    (p : Cover) {r R : ℝ} (hr : 0 < r) (hR : 1 < R)
    (hc : Metric.closedBall p r ⊆ Metric.closedBall (0 : Cover) 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(euclideanNormalMeasure ν p r R : Measure BlowupNormalBundle)) = 0 := by
  rw [integral_euclidean_normal_test ν p hr (continuous_blowupTangentTest hF)
    (fun z hz ↦ tangentialDivergence_zero_of_notMem_tsupport
      (fun h ↦ hz (Metric.closedBall_subset_ball hR (hs h))) z.2)]
  have hid := hstat (scaledTestField p r F) (scaledTestField_contDiff hF p r)
    ((scaledTestField_tsupport hs p hr).trans hc)
  simp only [tangentialDivergence_scaledTestField (hF.differentiable (by simp)) p _ _ hr.ne'] at hid
  change r⁻¹^2 * (∫ z, tangentialDivergence F (r⁻¹ • (z.1-p)) z.2 ∂(ν : Measure BlowupNormalBundle)) = 0
  rw [hid,mul_zero]

theorem stationary_euclidean_normal_limit {ν : FiniteMeasure BlowupNormalBundle}
    (hstat : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0)
    (p : Cover) (hp : ‖p‖ < 1) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0)) {R : ℝ} (hR : 1 < R)
    {σ : FiniteMeasure BlowupNormalBundle}
    (hσ : Tendsto (fun i ↦ euclideanNormalMeasure ν p (r i) R) l (𝓝 σ))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(σ : Measure BlowupNormalBundle)) = 0 := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have hweak := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hσ) (blowupTangentTest hF hFs)
  have he : (fun i ↦ ∫ z, tangentialDivergence F z.1 z.2 ∂(euclideanNormalMeasure ν p (r i) R : Measure BlowupNormalBundle)) =ᶠ[l] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hrlim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < 1-‖p‖))] with i hi
    apply stationary_euclidean_normal_identity hstat p (hr i) hR _ hF hs
    intro x hx
    have hx' : ‖x-p‖ ≤ r i := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    have hn := norm_add_le (x-p) p
    rw [sub_add_cancel] at hn
    simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith : ‖x‖ ≤ 1)
  exact tendsto_nhds_unique hweak (tendsto_const_nhds.congr' he.symm)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace BoundedContinuousFunction
namespace CubicTorus

lemma euclidean_normal_scaled_flux {A : Set Cover} (hA : MeasurableSet A)
    {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (p : Cover) {r R : ℝ} (hr : 0 < r) (hR : 1 < R)
    (hc : Metric.closedBall p r ⊆ Metric.closedBall (0 : Cover) 1)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(euclideanNormalMeasure ν p r R : Measure BlowupNormalBundle)) =
      ∫ x, A.indicator (fun _ ↦ (1 : ℝ)) (r • x+p)*divergence F x := by
  rw [integral_euclidean_normal_test ν p hr (continuous_blowupFluxTest hF.continuous)
    (fun z hz ↦ by
      have hn : z.1 ∉ tsupport F := fun hh ↦ hz (Metric.closedBall_subset_ball hR (hs hh))
      simp [image_eq_zero_of_notMem_tsupport hn])]
  have hid := hflux (scaledTestField p r F) (scaledTestField_contDiff hF p r)
    ((scaledTestField_tsupport hs p hr).trans hc)
  simp only [scaledTestField,inner_smul_right,integral_const_mul] at hid
  have hscale := integral_cover_affine_scaling
    (fun x ↦ A.indicator (fun _ ↦ (1 : ℝ)) x*divergence (scaledTestField p r F) x) p hr
  have hdiv (x : Cover) : divergence (scaledTestField p r F) (r • x+p) = divergence F x := by
    rw [divergence_scaledTestField (hF.differentiable (by simp)) p _ hr.ne']
    simp [hr.ne']
  simp_rw [hdiv] at hscale
  have heq : (∫ x in A, divergence (scaledTestField p r F) x) =
      ∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x*divergence (scaledTestField p r F) x := by
    simp only [← indicator_mul_left,one_mul,integral_indicator hA]
  rw [heq,hscale] at hid
  change r⁻¹^2 * (∫ z, ⟪(z.2 : Cover), F (r⁻¹ • (z.1-p))⟫ ∂(ν : Measure BlowupNormalBundle)) = _
  calc
    _ = (r*(∫ z, ⟪(z.2 : Cover), F (r⁻¹ • (z.1-p))⟫ ∂(ν : Measure BlowupNormalBundle)))/r^3 := by field_simp
    _ = _ := by rw [hid]; field_simp

theorem euclidean_normal_limit_flux {A B : Set Cover} (hA : MeasurableSet A)
    (hB : MeasurableSet B) {ν : FiniteMeasure BlowupNormalBundle}
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (p : Cover) (hp : ‖p‖ < 1) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0)) {R : ℝ} (hR : 1 < R)
    {σ : FiniteMeasure BlowupNormalBundle}
    (hσ : Tendsto (fun i ↦ euclideanNormalMeasure ν p (r i) R) l (𝓝 σ))
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)-B.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) :
    (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(σ : Measure BlowupNormalBundle)) = ∫ x in B, divergence F x := by
  have hFs : HasCompactSupport F := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hs
  have hweak := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hσ) (blowupFluxTest hF.continuous hFs)
  have hstrong := local_indicator_pairing_tendsto hA hB p r hconv (continuous_divergence hF)
    ((divergence_tsupport_subset F).trans hs)
  have he : (fun i ↦ ∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(euclideanNormalMeasure ν p (r i) R : Measure BlowupNormalBundle)) =ᶠ[l]
      (fun i ↦ ∫ x, A.indicator (fun _ ↦ (1 : ℝ)) (r i • x+p)*divergence F x) := by
    filter_upwards [hrlim.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < 1-‖p‖))] with i hi
    apply euclidean_normal_scaled_flux hA hflux p (hr i) hR _ hF hs
    intro x hx
    have hx' : ‖x-p‖ ≤ r i := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
    have hn := norm_add_le (x-p) p
    rw [sub_add_cancel] at hn
    simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith : ‖x‖ ≤ 1)
  exact tendsto_nhds_unique (hweak.congr' he) hstrong

end CubicTorus

end
end

end

end OAI
