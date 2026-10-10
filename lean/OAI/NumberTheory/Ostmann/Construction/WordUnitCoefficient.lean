import OAI.NumberTheory.Ostmann.Construction.WordUnitPeriod

namespace OAI

/-! # Exact residue support for all inherited word units -/

namespace Ostmann

open scoped Classical

noncomputable def WordRangeDecoration.unitAt {σ : Type*} {n : ℕ}
    (U : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (i : Fin U.count) : HistoryUnitGuard σ :=
  (U.unitGuards template t ht .prime)[i.val]'(by rw [U.unitGuards_length]; exact i.isLt)

theorem WordRangeDecoration.unitAt_mem {σ : Type*} {n : ℕ}
    (U : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (i : Fin U.count) :
    U.unitAt template t ht i ∈ U.unitGuards template t ht .prime := List.getElem_mem _

noncomputable def wordUnitNumerators {σ : Type*} {m : ℕ} (G : Fin m → HistoryUnitGuard σ) :=
  fun i => (G i).formula.cleared.numerator

noncomputable def wordUnitDenominators {σ : Type*} {m : ℕ} (G : Fin m → HistoryUnitGuard σ) :=
  fun i => (G i).formula.cleared.denominator

def wordUnitModuli {σ : Type*} {m : ℕ} (G : Fin m → HistoryUnitGuard σ) := fun i => (G i).modulus

theorem WordRangeDecoration.unitAt_all {σ : Type*} {n : ℕ}
    (U : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : σ → ℤ) :
    (∀ i, (U.unitAt template t ht i).Holds x) ↔
      ∀ g ∈ U.unitGuards template t ht .prime, g.Holds x := by
  constructor
  · intro h g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    have hi' : i < U.count := by rwa [U.unitGuards_length] at hi
    exact h ⟨i, hi'⟩
  · intro h i
    exact h _ (U.unitAt_mem template t ht i)

theorem WordRangeDecoration.unitAt_period {σ : Type*} {n : ℕ}
    (U : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hU : U.WordsBounded B) :
    ∀ i, wordUnitDenominators (U.unitAt template t ht) i *
      (wordUnitModuli (U.unitAt template t ht) i : ℤ) ∣ (wordTransferFullPeriod n t B : ℤ) := by
  intro i
  exact U.unitGuards_period template t ht B hB hwords hU _ (U.unitAt_mem template t ht i)

theorem guardedHistoryAmplitude_extra_units {σ : Type*} {r s n t : ℕ}
    (N : Fin r → MvPolynomial σ ℤ) (d : Fin r → ℤ) (v : Fin r → ℕ)
    (G : Fin s → HistoryUnitGuard σ) (a : σ → ℤ) (coord : σ)
    (F : Fin n → ClippedPolynomialFactor) (H : Fin t → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) (z : ℤ) :
    guardedHistoryAmplitude (Fin.append N (wordUnitNumerators G))
      (Fin.append d (wordUnitDenominators G)) (Fin.append v (wordUnitModuli G)) a coord F H keep z =
      (if ∀ i, (G i).Holds (Function.update a coord z) then 1 else 0) *
        guardedHistoryAmplitude N d v a coord F H keep z := by
  simp only [guardedHistoryAmplitude, Fin.forall_fin_add, Fin.append_left, Fin.append_right,
    wordUnitNumerators, wordUnitDenominators, wordUnitModuli, HistoryUnitGuard.Holds]
  split_ifs <;> simp_all
  all_goals
    left
    apply ite_eq_right
    intro hgood
    aesop

namespace WordFourierParameters

noncomputable def unitRangedCoefficient {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (U D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : σ → ℤ) : ℂ :=
  (if ∀ g ∈ U.unitGuards template t ht .prime, g.Holds x then 1 else 0) *
    p.rangedCoefficient D template t ht x

/-- All inherited unit tests are literal divisibility tests on the constructed
numerators, with the same polynomial inequalities and smooth factors. -/
theorem unitRangedCoefficient_local {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (U D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) (z : ℤ) :
    p.unitRangedCoefficient U D template t ht (Function.update a coord z) =
      guardedHistoryAmplitude
        (Fin.append (wordGuardNumerators (template.guardAt t ht)) (wordUnitNumerators (U.unitAt template t ht)))
        (Fin.append (wordGuardDenominators (template.guardAt t ht)) (wordUnitDenominators (U.unitAt template t ht)))
        (Fin.append (wordGuardModuli (template.guardAt t ht)) (wordUnitModuli (U.unitAt template t ht)))
        a coord (p.factors template t ht a coord) (p.rangedPolynomials D template t ht a coord)
        (rangedKeep D template t ht) z := by
  rw [guardedHistoryAmplitude_extra_units, ← rangedCoefficient_local]
  unfold unitRangedCoefficient
  simp only [U.unitAt_all]

/-- On valid natural histories these are exactly the recursively inherited
unit conditions, including the original leaf-frequency conditions. -/
theorem unitRangedCoefficient_nat {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (U D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : σ → ℕ)
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    p.unitRangedCoefficient U D template t ht (fun i => (x i : ℤ)) =
      (if U.UnitsAt template x t then 1 else 0) *
        p.rangedCoefficient D template t ht (fun i => (x i : ℤ)) := by
  unfold unitRangedCoefficient
  have he := U.unitGuards_iff template t ht .prime (fun i => (x i : ℤ)) x
    (fun i => by simp only [HistoryFormula.value_prime, Int.cast_natCast]) hv
  simp only [he]

theorem coefficient_eq_zero_of_not_valid {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (x : σ → ℕ)
    (hv : ¬ ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    p.coefficient template t ht (fun i => (x i : ℤ)) = 0 := by
  unfold coefficient
  split_ifs with h
  · exact False.elim (hv ((template.guardAt_valid_iff t ht x).mp h.1))
  · exact zero_mul _

theorem unitRangedCoefficient_nat_all {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (U D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : σ → ℕ) :
    p.unitRangedCoefficient U D template t ht (fun i => (x i : ℤ)) =
      (if U.UnitsAt template x t then 1 else 0) *
        p.rangedCoefficient D template t ht (fun i => (x i : ℤ)) := by
  by_cases hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t
  · exact p.unitRangedCoefficient_nat U D template t ht x hv
  · simp only [unitRangedCoefficient, rangedCoefficient,
      p.coefficient_eq_zero_of_not_valid template t ht x hv, mul_zero]

end WordFourierParameters

end Ostmann

end OAI
