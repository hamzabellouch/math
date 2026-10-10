import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroSet
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothZeroCountFamily

namespace OAI

/-! # Connecting zero enumerations to actual analytic multiplicities

This is a representation condition: an enumeration may list a zero no more
times than its analytic multiplicity. The numerical zero bound itself is
proved in `CharacterFullZeroCount`, not assumed here.
-/

namespace Ostmann

open scoped Classical BigOperators

def ComplexZeroEnumeration.RespectsMultiplicity {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) : Prop :=
  ∀ (S : Finset ℕ) (z : ℂ),
    (S.filter (fun i => Z.zeros i = z)).card ≤ analyticOrderNatAt χ.L z

theorem ComplexZeroEnumeration.count_zero_eq_card {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (T : ℝ) : Z.count 0 T = (Z.heightIndices T).card := by
  unfold ComplexZeroEnumeration.count
  congr 1
  apply Finset.filter_true_of_mem
  intro i _
  exact (Z.in_strip i).1.le

theorem ComplexZeroEnumeration.count_bound_of_multiplicity {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (hZ : Z.RespectsMultiplicity) (T : ℝ) (hT : 0 ≤ T) :
    (Z.count 0 T : ℝ) ≤ (32 / Real.log (14 / 13)) * (T + 1) *
      Real.log ((χ.modulus : ℝ) * (T + 2)) := by
  let S := Z.heightIndices T
  let F := S.image Z.zeros
  have hcard : S.card = ∑ z ∈ F, (S.filter fun i => Z.zeros i = z).card :=
    Finset.card_eq_sum_card_image Z.zeros S
  have hbound : (S.card : ℝ) ≤ ∑ z ∈ F, (characterZeroOrder χ z : ℝ) := by
    rw [hcard, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro z hz
    have hh := hZ S z
    rw [characterZeroOrder_eq_nat]
    exact_mod_cast hh
  rw [Z.count_zero_eq_card]
  apply hbound.trans
  apply χ.full_zero_sum_rate T hT F
  intro z hz
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨(Z.in_strip i).1, (Z.in_strip i).2, (Z.mem_heightIndices T i).mp hi⟩

/-- For multiplicity-respecting enumerations, only the actual explicit formula
remains in this analytic package. The zero count, Mellin decay and absolute
convergence are all derived. -/
noncomputable def smoothExplicitFormula_of_multiplicity {Z : ∀ χ, ComplexZeroEnumeration χ}
    (hZ : ∀ χ, (Z χ).RespectsMultiplicity) (E : ℝ) (hE : 0 < E)
    (hformula : ∀ χ : PrimitiveComplexCharacter, ∀ X : ℝ, 2 ≤ X →
      ‖smoothMangoldtMean χ.modulus χ.character X +
        (∑' i, smoothZeroTerm Z χ X i) + smoothTrivialZeroTerm χ‖ ≤
          E / Real.sqrt X * Real.log (2 * (χ.modulus : ℝ))) :
    PublishedSmoothExplicitFormula Z :=
  smoothExplicitFormula_of_individual E (32 / Real.log (14 / 13)) hE
    (div_pos (by norm_num) (Real.log_pos (by norm_num)))
    (fun χ T hT => (Z χ).count_bound_of_multiplicity (hZ χ) T hT) hformula

end Ostmann

end OAI
