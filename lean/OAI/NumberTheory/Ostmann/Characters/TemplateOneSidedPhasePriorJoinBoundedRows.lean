import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinRowsExtension

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries TemplateOneSidedPrior PrimeDyadicCover
attribute [local instance] Classical.propDecidable

def boundedSourceUnary {A : ℕ} (E : Finset (PrimeUpTo A))
    (U : PrimeUpTo A → ℂ) (p : PrimeUpTo A) : ℂ :=
  if p ∈ E then U p else 0

theorem boundedSourceUnary_norm_le_one {A : ℕ} (E : Finset (PrimeUpTo A))
    (U : PrimeUpTo A → ℂ) (hU : ∀ p ∈ E,‖U p‖ ≤ 1) (p : PrimeUpTo A) :
    ‖boundedSourceUnary E U p‖ ≤ 1 := by
  unfold boundedSourceUnary
  split_ifs with hp
  · exact hU p hp
  · simp

theorem sourceTest_boundedSourceUnary_norm_le_one {A : ℕ}
    (E : Finset (PrimeUpTo A)) (U : PrimeUpTo A → ℂ)
    (hU : ∀ p ∈ E,‖U p‖ ≤ 1) (n : ℕ) :
    ‖sourceTest (boundedSourceUnary E U) n‖ ≤ 1 :=
  sourceTest_norm_le_one _ (boundedSourceUnary_norm_le_one E U hU) n

theorem sourceTest_eq_boundedSourceUnary_on_mass {A : ℕ} (Q H : ℕ)
    (E : Finset (PrimeUpTo A)) (i : Index H) (U : PrimeUpTo A → ℂ)
    (x : Fin Q × Fin (2*lower Q H i+1)) (hx : sourceRowMass Q H E i x ≠ 0) :
    sourceTest U (rowValue Q (2*lower Q H i+1) x) =
      sourceTest (boundedSourceUnary E U) (rowValue Q (2*lower Q H i+1) x) := by
  obtain ⟨p,hp,he⟩ := sourceRowMass_ne_zero_exists_source Q H E i x hx
  rw [← he,sourceTest_val,sourceTest_val,boundedSourceUnary,ite_eq_left hp]

theorem source_oneSidedMean_eq_boundedSourceUnary {A : ℕ} {κ : Type*} [Fintype κ]
    (Q H : ℕ) (E : Finset (PrimeUpTo A)) (i : Index H)
    (ν : κ → ℝ) (U : PrimeUpTo A → ℂ) (V : κ → ℂ)
    (F : (Fin Q × Fin (2*lower Q H i+1)) → κ → ℂ) :
    oneSidedMean (sourceRowMass Q H E i) ν
      (fun x => sourceTest U (rowValue Q (2*lower Q H i+1) x)) V F =
    oneSidedMean (sourceRowMass Q H E i) ν
      (fun x => sourceTest (boundedSourceUnary E U) (rowValue Q (2*lower Q H i+1) x)) V F := by
  unfold oneSidedMean
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hm : sourceRowMass Q H E i x = 0
  · simp only [hm,Complex.ofReal_zero,zero_mul]
  · dsimp only
    rw [sourceTest_eq_boundedSourceUnary_on_mass Q H E i U x hm]

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
