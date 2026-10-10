import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightChamberLimits

namespace OAI

/-! # From weight-sign agreement to chamber-image agreement -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

def PreservesPositiveWeightRays (α : I → W →L[ℝ] ℝ) (A : W ≃ₗ[ℝ] W) : Prop :=
  ∀ i, ∃ (j : I) (r : ℝ), 0 < r ∧
    (α i).toLinearMap.comp A.toLinearMap = r • (α j).toLinearMap

theorem generic_of_mem_weightChamber (α : I → W →L[ℝ] ℝ)
    {σ : I → Bool} {w : W} (hw : w ∈ weightChamber α σ) : ∀ i, α i w ≠ 0 := by
  intro i hi
  have hh := hw i
  cases hs : σ i <;> simp [orientedWeight, hs, hi] at hh

theorem weightSigns_eq_of_mem_chamber (α : I → W →L[ℝ] ℝ)
    {σ : I → Bool} {w : W} (hw : w ∈ weightChamber α σ) : weightSigns α w = σ := by
  funext i
  have hh := hw i
  cases hs : σ i with
  | false =>
    have hn : α i w < 0 := by simpa [orientedWeight, hs] using hh
    simp [weightSigns, not_lt.mpr hn.le]
  | true =>
    have hp : 0 < α i w := by simpa [orientedWeight, hs] using hh
    simp [weightSigns, hp]

theorem mem_weightChamber_signs_iff (α : I → W →L[ℝ] ℝ) {w x : W}
    (hw : ∀ i, α i w ≠ 0) :
    x ∈ weightChamber α (weightSigns α w) ↔ ∀ i, 0 < α i x * α i w := by
  constructor
  · intro hx i
    have hi := hx i
    by_cases hp : 0 < α i w
    · have hxi : 0 < α i x := by simpa [orientedWeight, weightSigns, hp] using hi
      exact mul_pos hxi hp
    · have hn : α i w < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hw i)
      have hxi : α i x < 0 := by simpa [orientedWeight, weightSigns, hp] using hi
      exact mul_pos_of_neg_of_neg hxi hn
  · intro hx i
    by_cases hp : 0 < α i w
    · have hxi : 0 < α i x := by nlinarith [hx i]
      simpa [orientedWeight, weightSigns, hp] using hxi
    · have hn : α i w < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hw i)
      have hxi : α i x < 0 := by nlinarith [hx i]
      simpa [orientedWeight, weightSigns, hp] using hxi

theorem positive_weight_products_map (α : I → W →L[ℝ] ℝ) (A : W ≃ₗ[ℝ] W)
    (hA : PreservesPositiveWeightRays α A) {x w : W}
    (h : ∀ i, 0 < α i x * α i w) : ∀ i, 0 < α i (A x) * α i (A w) := by
  intro i
  obtain ⟨j, r, hr, he⟩ := hA i
  have hx := LinearMap.congr_fun he x
  have hw := LinearMap.congr_fun he w
  change α i (A x) = r * α j x at hx
  change α i (A w) = r * α j w at hw
  rw [hx, hw]
  have hp := mul_pos (mul_pos hr hr) (h j)
  nlinarith only [hp]

theorem generic_weights_map (α : I → W →L[ℝ] ℝ) (A : W ≃ₗ[ℝ] W)
    (hA : PreservesPositiveWeightRays α A) {w : W} (hw : ∀ i, α i w ≠ 0) :
    ∀ i, α i (A w) ≠ 0 := by
  intro i
  obtain ⟨j, r, hr, he⟩ := hA i
  have hh := LinearMap.congr_fun he w
  change α i (A w) = r * α j w at hh
  rw [hh]
  exact mul_ne_zero hr.ne' (hw j)

theorem image_weightChamber (α : I → W →L[ℝ] ℝ) (A : W ≃ₗ[ℝ] W)
    (hA : PreservesPositiveWeightRays α A) (hAi : PreservesPositiveWeightRays α A.symm)
    {w : W} (hw : ∀ i, α i w ≠ 0) :
    A '' weightChamber α (weightSigns α w) =
      weightChamber α (weightSigns α (A w)) := by
  have haw := generic_weights_map α A hA hw
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_weightChamber_signs_iff α haw).mpr
      (positive_weight_products_map α A hA ((mem_weightChamber_signs_iff α hw).mp hx))
  · intro hy
    refine ⟨A.symm y, ?_, A.apply_symm_apply y⟩
    apply (mem_weightChamber_signs_iff α hw).mpr
    have hh := positive_weight_products_map α A.symm hAi
      ((mem_weightChamber_signs_iff α haw).mp hy)
    simpa only [A.symm_apply_apply] using hh

variable [FiniteDimensional ℝ W]

theorem image_closedWeightChamber (α : I → W →L[ℝ] ℝ) (A : W ≃ₗ[ℝ] W)
    (hA : PreservesPositiveWeightRays α A) (hAi : PreservesPositiveWeightRays α A.symm)
    {w : W} (hw : ∀ i, α i w ≠ 0) :
    A '' closedWeightChamber α (weightSigns α w) =
      closedWeightChamber α (weightSigns α (A w)) := by
  have hmem : w ∈ weightChamber α (weightSigns α w) :=
    (mem_weightChamber_signs_iff α hw).mpr (fun i => mul_self_pos.mpr (hw i))
  have haw := generic_weights_map α A hA hw
  have hmemA : A w ∈ weightChamber α (weightSigns α (A w)) :=
    (mem_weightChamber_signs_iff α haw).mpr (fun i => mul_self_pos.mpr (haw i))
  rw [← closure_weightChamber α _ ⟨w, hmem⟩,
    ← closure_weightChamber α _ ⟨A w, hmemA⟩]
  have he := A.toContinuousLinearEquiv.toHomeomorph.image_closure
    (weightChamber α (weightSigns α w))
  change A '' closure (weightChamber α (weightSigns α w)) =
    closure (A '' weightChamber α (weightSigns α w)) at he
  rw [he, image_weightChamber α A hA hAi hw]

/-- Equal signs on one generic direction identify the full chamber images. -/
theorem image_closedWeightChamber_eq_of_signs
    (α : I → W →L[ℝ] ℝ) (A B : W ≃ₗ[ℝ] W)
    (hA : PreservesPositiveWeightRays α A) (hAi : PreservesPositiveWeightRays α A.symm)
    (hB : PreservesPositiveWeightRays α B) (hBi : PreservesPositiveWeightRays α B.symm)
    {w : W} (hw : ∀ i, α i w ≠ 0)
    (hsign : ∀ i, 0 < α i (A w) ↔ 0 < α i (B w)) :
    A '' closedWeightChamber α (weightSigns α w) =
      B '' closedWeightChamber α (weightSigns α w) := by
  rw [image_closedWeightChamber α A hA hAi hw, image_closedWeightChamber α B hB hBi hw]
  congr 1
  funext i
  simp only [weightSigns, hsign i]

end PolycyclicRecognition

end

end OAI
