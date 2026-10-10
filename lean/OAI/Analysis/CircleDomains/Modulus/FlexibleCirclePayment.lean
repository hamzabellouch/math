import OAI.Analysis.CircleDomains.Modulus.LocalizedCirclePayment

namespace OAI

/-! Line payment is independent of which endpoint carries the value zero. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem line_payment_through_disks_one_zero
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {y a b : ℝ} (hab : a < b)
    (ha : a ∈ diskLineDomain c r y) (hb : b ∈ diskLineDomain c r y)
    {f ρ : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (diskLineDomain c r y))
    (hone : f a = 1) (hzero : f b = 0)
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hmajor : ∀ x ∈ Icc a b ∩ diskLineDomain c r y, |deriv f x| ≤ ρ x)
    (hcluster : ∀ i p q u v,
      (⟨p, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
      (⟨q, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[diskLineDomain c r y] p) f →
      MapClusterPt v (𝓝[diskLineDomain c r y] q) f → |v - u| ≤ A i) :
    1 ≤ (∫ x, ρ x) +
      ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y := by
  apply line_payment_through_disks c r A hr hA hdisj hab ha hb (f := fun x => 1 - f x)
    (contDiffOn_const.sub hf) (by simp [hone]) (by simp [hzero]) hρ hpos
  · intro x hx
    simpa only [deriv_const_sub, abs_neg] using hmajor x hx
  · intro i p q u v hp hq hu hv
    have hc : Continuous (fun t : ℝ => 1 - t) := continuous_const.sub continuous_id
    have hu' : MapClusterPt (1 - u) (𝓝[diskLineDomain c r y] p) f := by
      simpa only [Function.comp_def, sub_sub_cancel] using hu.continuousAt_comp hc.continuousAt
    have hv' : MapClusterPt (1 - v) (𝓝[diskLineDomain c r y] q) f := by
      simpa only [Function.comp_def, sub_sub_cancel] using hv.continuousAt_comp hc.continuousAt
    have h := hcluster i p q (1 - u) (1 - v) hp hq hu' hv'
    rw [show (1 - v) - (1 - u) = u - v by ring, abs_sub_comm] at h
    exact h

theorem parallel_line_payment_in_region_either_order
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ) {L : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i) (hL : 0 ≤ L)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v (⋃ i, closedBall (c i) (r i))ᶜ)
    {W : Set ℂ} (hW : MeasurableSet W) (hWB : W ⊆ closedBall 0 L)
    (henergy : IntegrableOn (euclideanGradientEnergy v) W)
    (hcluster : ∀ i p q u w, p ∈ closedBall (c i) (r i) → q ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p) v →
      MapClusterPt w (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] q) v → |w - u| ≤ A i)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ a b : ℝ, a < b ∧ a ∈ diskLineDomain c r y ∧
      b ∈ diskLineDomain c r y ∧ horizontalLine y a ∈ closedBall 0 L ∧
      horizontalLine y b ∈ closedBall 0 L ∧ ((v (horizontalLine y a) = 0 ∧ v (horizontalLine y b) = 1) ∨
        (v (horizontalLine y a) = 1 ∧ v (horizontalLine y b) = 0)) ∧
      ∀ x ∈ Icc a b ∩ diskLineDomain c r y, horizontalLine y x ∈ W) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ z in W, euclideanGradientEnergy v z) +
      ∑ i, 2 * r i * A i := by
  let U := (⋃ i, closedBall (c i) (r i))ᶜ
  let E := W
  let ρ := E.indicator (euclideanGradientNorm v)
  have hU : IsOpen U := (isClosed_iUnion_of_finite (fun i => isClosed_closedBall)).isOpen_compl
  have hE : MeasurableSet E := hW
  have hρ : MemLp ρ 2 volume := memLp_indicator_euclideanGradientNorm hE henergy
  have hρpos : ∀ z, 0 ≤ ρ z := fun _ => indicator_nonneg
    (fun z _ => Real.sqrt_nonneg (euclideanGradientEnergy v z)) _
  have hρsupport : support ρ ⊆ closedBall 0 L := by
    intro z hz
    by_contra h
    exact hz (indicator_of_notMem (fun he : z ∈ E => h (hWB he)) _)
  have hρint := (integral_le_disk_L2 hL hρ hρpos hρsupport).1
  have hp : Integrable (fun p : ℝ × ℝ => ρ ⟨p.1, p.2⟩) :=
    ((Complex.volume_preserving_equiv_real_prod.symm
      Complex.measurableEquivRealProd).integrable_comp hρint.aestronglyMeasurable).mpr hρint
  have hJsub : J ⊆ Icc (-L) L := by
    intro y hy
    obtain ⟨a, _, _, _, _, ha, _⟩ := hcross y hy
    simpa only [Complex.zero_im, zero_sub, zero_add] using
      (horizontal_line_meets_closedBall (0 : ℂ)).mp ⟨a, ha⟩
  have hJfinite : volume J ≠ ⊤ := ne_of_lt ((measure_mono hJsub).trans_lt measure_Icc_lt_top)
  have hpay : ∀ᵐ y ∂volume.restrict J, 1 ≤ (∫ x : ℝ, ρ ⟨x, y⟩) +
      ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y := by
    filter_upwards [ae_restrict_of_ae hp.prod_left_ae, ae_restrict_mem hJ] with y hiy hy
    obtain ⟨a, b, hab, haD, hbD, haB, hbB, hvalues, hsegment⟩ := hcross y hy
    have hf : ContDiffOn ℝ 1 (v ∘ horizontalLine y) (diskLineDomain c r y) :=
      hv.comp (contDiff_horizontalLine y).contDiffOn (fun _ hx => hx)
    have hmajor : ∀ x ∈ Icc a b ∩ diskLineDomain c r y,
        |deriv (v ∘ horizontalLine y) x| ≤ ρ (horizontalLine y x) := by
      intro x hx
      have hxE : horizontalLine y x ∈ E := hsegment x hx
      change |deriv (v ∘ horizontalLine y) x| ≤ E.indicator (euclideanGradientNorm v) (horizontalLine y x)
      rw [indicator_of_mem hxE]
      exact horizontal_derivative_le_gradient ((hv.contDiffAt (hU.mem_nhds hx.2)).differentiableAt (by norm_num))
    have hcl : ∀ i p q u w,
        (⟨p, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
        (⟨q, y⟩ : ℂ) ∈ closedBall (c i) (r i) →
        MapClusterPt u (𝓝[diskLineDomain c r y] p) (v ∘ horizontalLine y) →
        MapClusterPt w (𝓝[diskLineDomain c r y] q) (v ∘ horizontalLine y) → |w - u| ≤ A i := by
      intro i p q u w hp hq hu hw
      exact hcluster i _ _ u w hp hq (horizontal_cluster_is_planar hu)
        (horizontal_cluster_is_planar hw)
    rcases hvalues with ⟨hzero, hone⟩ | ⟨hone, hzero⟩
    · exact line_payment_through_disks c r A hr hA hdisj hab haD hbD hf hzero hone hiy
        (fun x => hρpos _) hmajor hcl
    · exact line_payment_through_disks_one_zero c r A hr hA hdisj hab haD hbD hf hone hzero hiy
        (fun x => hρpos _) hmajor hcl
  have h := integrated_parallel_line_payment c r A hJfinite hr hA hL hρ hρpos hρsupport hpay
  have hsq : (fun z => ρ z ^ 2) = E.indicator (euclideanGradientEnergy v) := by
    funext z
    by_cases hz : z ∈ E
    · simp only [ρ, indicator_of_mem hz, euclideanGradientNorm_sq]
    · simp only [ρ, indicator_of_notMem hz, zero_pow (by norm_num : 2 ≠ 0)]
  rw [hsq, integral_indicator hE] at h
  exact h


end CircleDomainRigidity

end

end OAI
