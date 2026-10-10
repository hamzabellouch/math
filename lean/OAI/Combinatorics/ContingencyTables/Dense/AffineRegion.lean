import OAI.Combinatorics.ContingencyTables.Transport.AffinePenalty
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace OAI

/-!
# Inner and relaxed affine feasibility regions

The strict feasible point yields the two homothetic inclusions used in
the dense rejection proof. Volume scaling follows from the Lebesgue/Haar
change-of-variables theorem.
-/

namespace ContingencyTables.AffinePenalty

open MeasureTheory
open scoped BigOperators Pointwise

noncomputable section

variable {I G : Type*} [Fintype I]

def region (offset : G → ℝ) (coeff : G → I → ℝ) (γ : ℝ) : Set (I → ℝ) :=
  {x | ∀ g, γ ≤ affineValue (offset g) (coeff g) x}

theorem inner_region_map (offset : G → ℝ) (coeff : G → I → ℝ)
    (center : I → ℝ) (η α : ℝ) (hα : 0 ≤ α) (hα₁ : α ≤ 1)
    (hc : center ∈ region offset coeff η) :
    (fun x => (1 - α) • x + α • center) '' region offset coeff 0 ⊆
      region offset coeff (α * η) := by
  rintro y ⟨x, hx, rfl⟩ g
  rw [affineValue_combine _ _ _ _ _ _ (by ring)]
  have ha := mul_nonneg (sub_nonneg.mpr hα₁) (hx g)
  have hb := mul_le_mul_of_nonneg_left (hc g) hα
  linarith

theorem relaxed_region_pullback (offset : G → ℝ) (coeff : G → I → ℝ)
    (center : I → ℝ) (d γ : ℝ) (hd : 0 < d) (hγ : 0 ≤ γ)
    (hc : center ∈ region offset coeff (1 / (2 * d)))
    (x : I → ℝ) (hx : x ∈ region offset coeff (-γ)) :
    (1 / (1 + 2 * d * γ)) • x + (2 * d * γ / (1 + 2 * d * γ)) • center ∈
      region offset coeff 0 := by
  have hden : 0 < 1 + 2 * d * γ := by positivity
  have hab : 1 / (1 + 2 * d * γ) + 2 * d * γ / (1 + 2 * d * γ) = 1 := by
    field_simp [ne_of_gt hden]
  intro g
  rw [affineValue_combine _ _ _ _ _ _ hab]
  calc
    0 = (1 / (1 + 2 * d * γ)) * (-γ) +
        (2 * d * γ / (1 + 2 * d * γ)) * (1 / (2 * d)) := by
      field_simp [ne_of_gt hd, ne_of_gt hden]
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hx g) (by positivity))
      (mul_le_mul_of_nonneg_left (hc g) (by positivity))

theorem relaxed_region_subset_expansion (offset : G → ℝ) (coeff : G → I → ℝ)
    (center : I → ℝ) (d γ : ℝ) (hd : 0 < d) (hγ : 0 ≤ γ)
    (hc : center ∈ region offset coeff (1 / (2 * d))) :
    region offset coeff (-γ) ⊆
      (fun z => center + (1 + 2 * d * γ) • (z - center)) '' region offset coeff 0 := by
  intro x hx
  refine ⟨_, relaxed_region_pullback offset coeff center d γ hd hγ hc x hx, ?_⟩
  have hden : 1 + 2 * d * γ ≠ 0 := ne_of_gt (by positivity : 0 < 1 + 2 * d * γ)
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hden]
  ring

private theorem volume_image_translate (c : I → ℝ) (S : Set (I → ℝ)) :
    volume ((fun x => c + x) '' S) = volume S := by
  have heq : (fun x => c + x) '' S = (fun x => -c + x) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨-c + x, hx, by simp⟩
  rw [heq, measure_preimage_add]

theorem volume_homothety (center : I → ℝ) (a : ℝ) (ha : 0 ≤ a) (S : Set (I → ℝ)) :
    volume ((fun z => center + a • (z - center)) '' S) =
      ENNReal.ofReal (a ^ Fintype.card I) * volume S := by
  have heq : (fun z => center + a • (z - center)) '' S =
      (fun z => center + z) '' (a • ((fun z => -center + z) '' S)) := by
    simp only [← Set.image_smul, Set.image_image]
    congr 1
    funext z
    rw [sub_eq_neg_add]
  rw [heq, volume_image_translate, Measure.addHaar_smul_of_nonneg volume ha,
    volume_image_translate, Module.finrank_fintype_fun_eq_card]

theorem relaxed_region_volume (offset : G → ℝ) (coeff : G → I → ℝ)
    (center : I → ℝ) (d γ : ℝ) (hd : 0 < d) (hγ : 0 ≤ γ)
    (hc : center ∈ region offset coeff (1 / (2 * d))) :
    volume (region offset coeff (-γ)) ≤
      ENNReal.ofReal ((1 + 2 * d * γ) ^ Fintype.card I) * volume (region offset coeff 0) := by
  calc
    _ ≤ volume ((fun z => center + (1 + 2 * d * γ) • (z - center)) '' region offset coeff 0) :=
      measure_mono (relaxed_region_subset_expansion offset coeff center d γ hd hγ hc)
    _ = _ := volume_homothety center _ (by positivity) _

end

end ContingencyTables.AffinePenalty

end OAI
