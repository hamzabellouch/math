import OAI.Analysis.CircleDomains.Sobolev.RotatedRealEnergy
import OAI.Analysis.CircleDomains.Modulus.FlexibleCirclePayment

namespace OAI

/-! Localized line payment in any fixed direction, with unchanged source energy and hole costs. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

/-- A line in the direction chosen by a unit complex multiplier. -/
def rotatedLine (a : Circle) (y x : ℝ) : ℂ := rotation a (horizontalLine y x)

theorem rotated_line_payment_in_region
    (a : Circle) {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ) {L : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i) (hL : 0 ≤ L)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hsub : ∀ i, closedBall (c i) (r i) ⊆ closedBall 0 L)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v (⋃ i, closedBall (c i) (r i))ᶜ)
    {W : Set ℂ} (hW : MeasurableSet W) (hWU : W ⊆ (⋃ i, closedBall (c i) (r i))ᶜ)
    (hWB : W ⊆ closedBall 0 L) (henergy : IntegrableOn (euclideanGradientEnergy v) W)
    (hcluster : ∀ i p q u w, p ∈ closedBall (c i) (r i) → q ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p) v →
      MapClusterPt w (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] q) v → |w - u| ≤ A i)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ s t : ℝ, s ≠ t ∧
      rotatedLine a y s ∈ (⋃ i, closedBall (c i) (r i))ᶜ ∧
      rotatedLine a y t ∈ (⋃ i, closedBall (c i) (r i))ᶜ ∧
      rotatedLine a y s ∈ closedBall 0 L ∧ rotatedLine a y t ∈ closedBall 0 L ∧
      v (rotatedLine a y s) = 0 ∧ v (rotatedLine a y t) = 1 ∧
      ∀ x ∈ uIcc s t, rotatedLine a y x ∈ (⋃ i, closedBall (c i) (r i))ᶜ →
        rotatedLine a y x ∈ W) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ z in W, euclideanGradientEnergy v z) + 2 * L * Real.sqrt (∑ i, A i ^ 2) := by
  let R := rotation a
  let U := (⋃ i, closedBall (c i) (r i))ᶜ
  let V := (⋃ i, closedBall (R.symm (c i)) (r i))ᶜ
  have hU : IsOpen U := (isClosed_iUnion_of_finite fun _ => isClosed_closedBall).isOpen_compl
  have hVU : V = R ⁻¹' U := by
    simp only [V, U, preimage_compl, preimage_iUnion, R.preimage_closedBall]
  have hvV : ContDiffOn ℝ 1 (v ∘ R) V := by
    rw [hVU]
    exact hv.comp R.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hx => hx)
  obtain ⟨hiV, heV⟩ := integral_energy_rotation_on a hU hv hW hWU henergy
  have hball (z : ℂ) : z ∈ R ⁻¹' closedBall (0 : ℂ) L ↔ z ∈ closedBall 0 L := by
    simp only [R.preimage_closedBall, map_zero]
  have hdV : Pairwise (Disjoint on fun i => closedBall (R.symm (c i)) (r i)) := by
    intro i j hij
    simpa only [R.preimage_closedBall] using (hdisj hij).preimage R
  have hclV : ∀ i p q u w, p ∈ closedBall (R.symm (c i)) (r i) →
      q ∈ closedBall (R.symm (c i)) (r i) →
      MapClusterPt u (𝓝[V] p) (v ∘ R) → MapClusterPt w (𝓝[V] q) (v ∘ R) →
      |w - u| ≤ A i := by
    intro i p q u w hp hq hu hw
    apply hcluster i (R p) (R q) u w
    · change p ∈ R ⁻¹' closedBall (c i) (r i)
      rwa [R.preimage_closedBall]
    · change q ∈ R ⁻¹' closedBall (c i) (r i)
      rwa [R.preimage_closedBall]
    · apply MapClusterPt.of_comp _ hu
      rw [hVU]
      exact tendsto_nhdsWithin_iff.mpr
        ⟨R.continuous.continuousAt.mono_left nhdsWithin_le_nhds, self_mem_nhdsWithin⟩
    · apply MapClusterPt.of_comp _ hw
      rw [hVU]
      exact tendsto_nhdsWithin_iff.mpr
        ⟨R.continuous.continuousAt.mono_left nhdsWithin_le_nhds, self_mem_nhdsWithin⟩
  have hp : (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ z in R ⁻¹' W, euclideanGradientEnergy (v ∘ R) z) + ∑ i, 2 * r i * A i :=
    parallel_line_payment_in_region_either_order
      (fun i => R.symm (c i)) r A hr hA hL hdV hvV
      (hW.preimage R.continuous.measurable)
      (fun z hz => (hball z).mp (hWB hz)) hiV hclV hJ ?_
  · rw [heV] at hp
    have ht := parallel_disk_tolls_le_square_norm c r A hr hL hdisj hsub
    rw [integral_parallel_disk_tolls c r A hr] at ht
    exact hp.trans (add_le_add le_rfl ht)
  intro y hy
  obtain ⟨s, t, hst, hs, ht, hsB, htB, hs0, ht1, hseg⟩ := hcross y hy
  have hmem (x : ℝ) : horizontalLine y x ∈ V ↔ rotatedLine a y x ∈ U := by
    rw [hVU]
    rfl
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · refine ⟨s, t, hlt, (hmem s).mpr hs, (hmem t).mpr ht,
      (hball _).mp hsB, (hball _).mp htB, Or.inl ⟨hs0, ht1⟩, ?_⟩
    intro x hx
    exact hseg x (Icc_subset_uIcc hx.1) ((hmem x).mp hx.2)
  · refine ⟨t, s, hgt, (hmem t).mpr ht, (hmem s).mpr hs,
      (hball _).mp htB, (hball _).mp hsB, Or.inr ⟨ht1, hs0⟩, ?_⟩
    intro x hx
    exact hseg x (Icc_subset_uIcc' hx.1) ((hmem x).mp hx.2)

end CircleDomainRigidity

end

end OAI
