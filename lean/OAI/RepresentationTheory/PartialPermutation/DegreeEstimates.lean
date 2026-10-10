import Mathlib

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

namespace PartialPermutation

lemma exists_degree_le_rpow {b D : ℕ} (hb : 0 < b) (hD : 0 < D)
    (d : Fin b → ℕ) (hprod : ∏ i, d i ≤ D) :
    ∃ i, (d i : ℝ) ≤ (D : ℝ) ^ (1 / (b : ℝ)) := by
  classical
  by_contra h
  push Not at h
  have hb' : (b : ℝ) ≠ 0 := by positivity
  have hD' : (0 : ℝ) < D := by positivity
  have hp : ∏ _ : Fin b, (D : ℝ) ^ (1 / (b : ℝ)) < ∏ i, (d i : ℝ) := by
    apply Finset.prod_lt_prod₀
    · intro i hi; positivity
    · intro i hi; exact (h i).le
    · exact ⟨⟨0, hb⟩, Finset.mem_univ _, h _⟩
  have he : ∏ _ : Fin b, (D : ℝ) ^ (1 / (b : ℝ)) = D := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD'.le]
    simp [hb']
  rw [he, ← Nat.cast_prod] at hp
  exact (not_lt_of_ge (Nat.cast_le.mpr hprod)) hp

lemma degree_sq_div_le {b D d : ℕ} (hD : 0 < D)
    (hd : (d : ℝ) ≤ (D : ℝ) ^ (1 / (b : ℝ))) :
    (d : ℝ) ^ 2 / D ≤ ((D : ℝ) ^ (-(1 / 2 : ℝ) + 1 / b)) ^ 2 := by
  have hD' : (0 : ℝ) < D := by positivity
  rw [div_le_iff₀ hD']
  calc
    (d : ℝ) ^ 2 ≤ ((D : ℝ) ^ (1 / (b : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hd 2
    _ = ((D : ℝ) ^ (-(1 / 2 : ℝ) + 1 / b)) ^ 2 * D := by
      rw [← Real.rpow_two, ← Real.rpow_two, ← Real.rpow_mul hD'.le,
        ← Real.rpow_mul hD'.le]
      nth_rw 3 [← Real.rpow_one (D : ℝ)]
      rw [← Real.rpow_add hD']
      congr 1
      ring

end PartialPermutation

end

end OAI
