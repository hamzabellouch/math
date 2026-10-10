import OAI.NumberTheory.Ostmann.Construction.WordRangeBounds
import OAI.NumberTheory.Ostmann.Construction.WordRangeWeight
import OAI.NumberTheory.Ostmann.Arithmetic.GlobalHistoryCoefficient

namespace OAI

/-! # The exact finite polynomial guard for all intermediate range tests -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def WordRangeDecoration.rangeAt {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (i : Fin D.count) : HistoryRange σ :=
  (D.formulas template t ht .prime)[i.val]'(by rw [D.formulas_length]; exact i.isLt)

theorem WordRangeDecoration.rangeAt_mem {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (i : Fin D.count) :
    D.rangeAt template t ht i ∈ D.formulas template t ht .prime := List.getElem_mem _

theorem WordRangeDecoration.rangeAt_all {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : σ → ℤ) :
    (∀ i, (D.rangeAt template t ht i).Holds x) ↔
      ∀ r ∈ D.formulas template t ht .prime, r.Holds x := by
  constructor
  · intro h r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    have hi' : i < D.count := by rwa [D.formulas_length] at hi
    exact h ⟨i, hi'⟩
  · intro h i
    exact h _ (D.rangeAt_mem template t ht i)

noncomputable def WordRangeDecoration.polynomials {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) :
    Fin (D.count + D.count) → Polynomial ℝ :=
  formulaRangePolynomials (fun i => (D.rangeAt template t ht i).formula)
    (fun i => (a i : ℝ)) coord (fun i => (D.rangeAt template t ht i).lower)
    (fun i => (D.rangeAt template t ht i).upper)

theorem WordRangeDecoration.polynomials_iff {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) (z : ℤ) :
    polynomialRangeKeep D.count
        (polynomialSupportCode (D.polynomials template t ht a coord) (z : ℝ)) = true ↔
      ∀ r ∈ D.formulas template t ht .prime, r.Holds (Function.update a coord z) := by
  rw [polynomials, formulaRangePolynomials_iff]
  simp only [formulaPolynomial_eval_update]
  exact D.rangeAt_all template t ht _

theorem WordRangeDecoration.polynomials_degree {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hD : D.WordsBounded B) :
    (∑ i, (D.polynomials template t ht a coord i).natDegree) ≤ 2 * D.count * B ^ (n + 1) := by
  apply (formulaRangePolynomials_degree _ _ _ _ _).trans
  have hs : (∑ i, (D.rangeAt template t ht i).formula.cost) ≤ D.count * B ^ (n + 1) := by
    calc
      _ ≤ ∑ _ : Fin D.count, B ^ (n + 1) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Nat.one_mul] using D.formulas_cost template t ht .prime B 1 hB le_rfl hwords hD
          (fun _ => le_rfl) _ (D.rangeAt_mem template t ht i)
      _ = _ := by simp
  nlinarith

/-- Adding a finite polynomial support family does not change the smooth
factor or any arithmetic residue condition. -/
theorem guardedHistoryAmplitude_extra {σ I : Type*} [Fintype I] {n t u : ℕ}
    (N : I → MvPolynomial σ ℤ) (d : I → ℤ) (s : I → ℕ) (a : σ → ℤ) (coord : σ)
    (F : Fin n → ClippedPolynomialFactor) (H : Fin t → Polynomial ℝ) (J : Fin u → Polynomial ℝ)
    (keep : (Fin t → Bool) → Bool) (extra : (Fin u → Bool) → Bool) (z : ℤ) :
    guardedHistoryAmplitude N d s a coord F (Fin.append H J) (pairedPolynomialKeep keep extra) z =
      (if extra (polynomialSupportCode J (z : ℝ)) = true then 1 else 0) *
        guardedHistoryAmplitude N d s a coord F H keep z := by
  have hleft : (fun i => polynomialSupportCode (Fin.append H J) (z : ℝ) (Fin.castAdd u i)) =
      polynomialSupportCode H (z : ℝ) := by
    funext i
    simp only [polynomialSupportCode, Fin.append_left]
  have hright : (fun i => polynomialSupportCode (Fin.append H J) (z : ℝ) (Fin.natAdd t i)) =
      polynomialSupportCode J (z : ℝ) := by
    funext i
    simp only [polynomialSupportCode, Fin.append_right]
  simp only [guardedHistoryAmplitude, polynomialAmplitude, pairedPolynomialKeep,
    hleft, hright, Bool.and_eq_true]
  split_ifs <;> simp_all

namespace WordFourierParameters

noncomputable def rangedPolynomials {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) :=
  Fin.append (p.polynomials template t ht a coord) (D.polynomials template t ht a coord)

noncomputable def rangedKeep {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) :=
  pairedPolynomialKeep (keep template t ht) (polynomialRangeKeep D.count)

theorem rangedCoefficient_local {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) (z : ℤ) :
    p.rangedCoefficient D template t ht (Function.update a coord z) =
      guardedHistoryAmplitude (wordGuardNumerators (template.guardAt t ht))
        (wordGuardDenominators (template.guardAt t ht)) (wordGuardModuli (template.guardAt t ht))
        a coord (p.factors template t ht a coord) (p.rangedPolynomials D template t ht a coord)
        (rangedKeep D template t ht) z := by
  rw [rangedPolynomials, rangedKeep, guardedHistoryAmplitude_extra, ← coefficient_local]
  unfold rangedCoefficient
  simp only [D.polynomials_iff template t ht a coord z]

theorem ranged_complexity_bound {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hD : D.WordsBounded B) :
    polynomialWeightComplexity (p.factors template t ht a coord)
      (p.rangedPolynomials D template t ht a coord) ≤
      (3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * D.count) * B ^ (n + 1) := by
  have hbase := p.complexity_bound template t ht a coord B hB hwords
  have hextra := D.polynomials_degree template t ht a coord B hB hwords hD
  simp only [polynomialWeightComplexity, rangedPolynomials, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right] at *
  nlinarith

end WordFourierParameters

end Ostmann

end OAI
