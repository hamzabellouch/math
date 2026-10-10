import OAI.Analysis.CircleDomains.Sobolev.AxisSwapEnergy

namespace OAI

/-! The finite-circle payment estimate in the second Cartesian direction. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def verticalLine (x y : ℝ) : ℂ := ⟨x, y⟩

@[simp] theorem axisSwap_horizontalLine (x y : ℝ) :
    axisSwap (horizontalLine x y) = verticalLine x y := by
  apply Complex.ext <;> simp [horizontalLine, verticalLine]

theorem vertical_line_payment_on_finite_disk_complement
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ) {L : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hA : ∀ i, 0 ≤ A i) (hL : 0 ≤ L)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hsub : ∀ i, closedBall (c i) (r i) ⊆ closedBall 0 L)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v (⋃ i, closedBall (c i) (r i))ᶜ)
    (henergy : IntegrableOn (euclideanGradientEnergy v) (⋃ i, closedBall (c i) (r i))ᶜ)
    (hcluster : ∀ i p q u w, p ∈ closedBall (c i) (r i) → q ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p) v →
      MapClusterPt w (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] q) v → |w - u| ≤ A i)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ x ∈ J, ∃ a b : ℝ, a < b ∧
      verticalLine x a ∈ (⋃ i, closedBall (c i) (r i))ᶜ ∧
      verticalLine x b ∈ (⋃ i, closedBall (c i) (r i))ᶜ ∧
      verticalLine x a ∈ closedBall 0 L ∧ verticalLine x b ∈ closedBall 0 L ∧
      v (verticalLine x a) = 0 ∧ v (verticalLine x b) = 1) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ z in (⋃ i, closedBall (c i) (r i))ᶜ, euclideanGradientEnergy v z) +
      2 * L * Real.sqrt (∑ i, A i ^ 2) := by
  let U := (⋃ i, closedBall (c i) (r i))ᶜ
  let V := (⋃ i, closedBall (axisSwap (c i)) (r i))ᶜ
  have hU : IsOpen U := (isClosed_iUnion_of_finite fun _ => isClosed_closedBall).isOpen_compl
  have hVU : V = axisSwap ⁻¹' U := by
    simp only [V, U, preimage_compl, preimage_iUnion, axisSwap_preimage_closedBall]
  have hV : IsOpen V := hVU ▸ hU.preimage axisSwap.continuous
  have hvV : ContDiffOn ℝ 1 (v ∘ axisSwap) V := by
    rw [hVU]
    exact hv.comp axisSwap.toContinuousLinearEquiv.contDiff.contDiffOn (fun _ hx => hx)
  obtain ⟨hiV, heV⟩ := integral_energy_axisSwap hU hv henergy
  rw [← hVU] at hiV heV
  have hdisjV : Pairwise (Disjoint on fun i => closedBall (axisSwap (c i)) (r i)) := by
    intro i j hij
    simpa only [axisSwap_preimage_closedBall] using (hdisj hij).preimage axisSwap
  have hsubV (i : I) : closedBall (axisSwap (c i)) (r i) ⊆ closedBall 0 L := by
    intro z hz
    have hz' : axisSwap z ∈ closedBall (c i) (r i) := by
      change z ∈ axisSwap ⁻¹' closedBall (c i) (r i)
      rwa [axisSwap_preimage_closedBall]
    have hb := hsub i hz'
    simpa only [mem_closedBall, dist_zero_right, axisSwap.norm_map] using hb
  have hclusterV : ∀ i p q u w,
      p ∈ closedBall (axisSwap (c i)) (r i) → q ∈ closedBall (axisSwap (c i)) (r i) →
      MapClusterPt u (𝓝[V] p) (v ∘ axisSwap) →
      MapClusterPt w (𝓝[V] q) (v ∘ axisSwap) → |w - u| ≤ A i := by
    intro i p q u w hp hq hu hw
    have hp' : axisSwap p ∈ closedBall (c i) (r i) := by
      change p ∈ axisSwap ⁻¹' closedBall (c i) (r i)
      rwa [axisSwap_preimage_closedBall]
    have hq' : axisSwap q ∈ closedBall (c i) (r i) := by
      change q ∈ axisSwap ⁻¹' closedBall (c i) (r i)
      rwa [axisSwap_preimage_closedBall]
    apply hcluster i _ _ u w hp' hq'
    · apply MapClusterPt.of_comp _ hu
      rw [hVU]
      exact tendsto_nhdsWithin_iff.mpr
        ⟨axisSwap.continuous.continuousAt.mono_left nhdsWithin_le_nhds, self_mem_nhdsWithin⟩
    · apply MapClusterPt.of_comp _ hw
      rw [hVU]
      exact tendsto_nhdsWithin_iff.mpr
        ⟨axisSwap.continuous.continuousAt.mono_left nhdsWithin_le_nhds, self_mem_nhdsWithin⟩
  have hcrossV : ∀ x ∈ J, ∃ a b : ℝ, a < b ∧
      a ∈ diskLineDomain (fun i => axisSwap (c i)) r x ∧
      b ∈ diskLineDomain (fun i => axisSwap (c i)) r x ∧
      horizontalLine x a ∈ closedBall 0 L ∧ horizontalLine x b ∈ closedBall 0 L ∧
      (v ∘ axisSwap) (horizontalLine x a) = 0 ∧
      (v ∘ axisSwap) (horizontalLine x b) = 1 := by
    intro x hx
    obtain ⟨a, b, hab, ha, hb, haL, hbL, ha0, hb1⟩ := hcross x hx
    have hmem (y : ℝ) : horizontalLine x y ∈ V ↔ verticalLine x y ∈ U := by
      rw [hVU]
      simp only [mem_preimage, axisSwap_horizontalLine]
    have hball (y : ℝ) : horizontalLine x y ∈ closedBall (0 : ℂ) L ↔
        verticalLine x y ∈ closedBall (0 : ℂ) L := by
      have he := axisSwap_preimage_closedBall (0 : ℂ) L
      simpa only [map_zero, mem_preimage, axisSwap_horizontalLine] using
        (Set.ext_iff.mp he (horizontalLine x y)).symm
    exact ⟨a, b, hab, (hmem a).mpr ha, (hmem b).mpr hb,
      (hball a).mpr haL, (hball b).mpr hbL,
      by simpa only [comp_apply, axisSwap_horizontalLine] using ha0,
      by simpa only [comp_apply, axisSwap_horizontalLine] using hb1⟩
  have hpay := parallel_line_payment_on_finite_disk_complement_square_norm
    (fun i => axisSwap (c i)) r A hr hA hL hdisjV hsubV hvV
    (hiV.mono_set inter_subset_left) hclusterV hJ hcrossV
  have hmono : (∫ z in V ∩ closedBall 0 L, euclideanGradientEnergy (v ∘ axisSwap) z) ≤
      ∫ z in V, euclideanGradientEnergy (v ∘ axisSwap) z :=
    setIntegral_mono_set hiV (ae_of_all _ (fun z => euclideanGradientEnergy_nonneg _ z))
      (Eventually.of_forall fun _ hz => hz.1)
  rw [heV] at hmono
  exact hpay.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmono)
      (mul_nonneg (Real.sqrt_nonneg _) hL)) le_rfl)

end CircleDomainRigidity

end

end OAI
