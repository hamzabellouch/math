import OAI.NumberTheory.Ostmann.Arithmetic.ReconstructedWordQueries
import OAI.NumberTheory.Ostmann.Construction.FormulaCoprimality

namespace OAI

/-! # The original word coprimalities, with constructed degree and denominator bounds -/

namespace Ostmann

open scoped BigOperators Classical

theorem HistoryFormula.prime_denominator_unit {σ : Type*} (F : HistoryFormula σ)
    (M p : ℕ) (hp : p.Prime) (hM : p.Coprime M)
    (hF : ∀ s ∈ F.frequencies, s ∣ (M : ℤ)) : ¬p ∣ F.cleared.denominator.natAbs := by
  have habs (l : List ℤ) : l.prod.natAbs = (l.map Int.natAbs).prod := by
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.prod_cons, List.map_cons, Int.natAbs_mul, ih]
  apply hp.coprime_iff_not_dvd.mp
  rw [F.denominator_eq_frequency_product, habs]
  apply Nat.coprime_list_prod_right_iff.mpr
  intro n hn
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hn
  exact hM.of_dvd_right (Int.dvd_natCast.mp (hF s hs))

theorem reconstructedWordFormula_frequencies_dvd {σ : Type*} (steps : List (HistoryPivotStep σ))
    (stage : ℕ) (word : List σ) (M : ℤ) (hsteps : ∀ step ∈ steps, step.s ∣ M) :
    ∀ s ∈ (reconstructedWordFormula steps stage word).frequencies, s ∣ M := by
  apply HistoryFormula.frequencies_listProduct_dvd
  intro F hF
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hF
  exact integerReconstructionFormulas_frequencies_dvd (steps.take stage) M
    (fun step hstep => hsteps step (List.mem_of_mem_take hstep)) i

theorem reconstructed_word_coprimality {σ : Type*} (steps : List (HistoryPivotStep σ))
    (stage : ℕ) (word : List σ) (x : σ → ℤ) (hx : ValidIntegerReconstruction steps x)
    (M p : ℕ) (hp : p.Prime) (hM : p.Coprime M)
    (hsteps : ∀ step ∈ steps, step.s ∣ (M : ℤ)) :
    p.Coprime ((word.map (reconstructIntegers (steps.take stage) x)).prod).natAbs ↔
      ¬p ∣ (MvPolynomial.eval₂Hom (RingHom.id ℤ) x
        (reconstructedWordFormula steps stage word).cleared.numerator).natAbs := by
  let F := reconstructedWordFormula steps stage word
  have hd := F.prime_denominator_unit M p hp hM
    (reconstructedWordFormula_frequencies_dvd steps stage word M hsteps)
  exact F.cleared.prime_coprime_integer_value x p hp hd _
    (reconstructedWordFormula_value steps stage word x hx)

theorem zero_reconstructed_word_support {σ : Type*} (steps : List (HistoryPivotStep σ))
    (stage : ℕ) (word : List σ) (coord : σ)
    (hzero : zeroHistoryVariable coord (reconstructedWordFormula steps stage word).cleared.numerator = 0)
    (x : σ → ℤ) (hx : ValidIntegerReconstruction steps x)
    (M p : ℕ) (hp : p.Prime) (hM : p.Coprime M)
    (hsteps : ∀ step ∈ steps, step.s ∣ (M : ℤ)) (hcoord : x coord = p) :
    ¬p.Coprime ((word.map (reconstructIntegers (steps.take stage) x)).prod).natAbs := by
  rw [reconstructed_word_coprimality steps stage word x hx M p hp hM hsteps, not_not]
  exact zeroHistoryVariable_identically_bad coord _ hzero x p hcoord

theorem reconstructed_word_coprimality_removal {A I : Type*}
    [Fintype A] [Nonempty A] [Fintype I] {n : ℕ}
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (steps : I → List (HistoryPivotStep (Fin (n + 1)))) (stage : I → ℕ)
    (word : I → List (Fin (n + 1))) (coord : I → Fin (n + 1))
    (C : ℕ) (hC : 1 ≤ C)
    (hsize : ∀ j step, step ∈ steps j → step.left.length + step.right.length + 4 ≤ C)
    (hzero : ∀ j, zeroHistoryVariable (coord j)
      (reconstructedWordFormula (steps j) (stage j) (word j)).cleared.numerator ≠ 0)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a = 1)
    (α V R : ℝ) (β : I → ℝ) (hα : 0 ≤ α) (hβ : ∀ j, 0 ≤ β j) (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i a, μ i a ≤ α) (hpmax : ∀ j a, μ (coord j) a ≤ β j)
    (hlower : ∀ a, V ≤ Real.log (prime a : ℝ)) (hupper : ∀ a, (prime a : ℝ) ≤ R)
    (hfreq : ∀ j step, step ∈ steps j →
      |(step.v : ℝ)| ≤ R ∧ |(step.w : ℝ)| ≤ R ∧ |(step.s : ℝ)| ≤ R)
    (W : (Fin (n + 1) → A) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hW : ∀ x, ‖W x‖ ≤ B) :
    ‖(∑ x, (productPrior μ x : ℂ) *
        (if ∀ j, ¬prime (x (coord j)) ∣
          (integerTestValue (fun a => (prime a : ℤ))
            (reconstructedWordFormula (steps j) (stage j) (word j)).cleared.numerator x).natAbs
          then W x else 0)) - ∑ x, (productPrior μ x : ℂ) * W x‖ ≤
      B * ∑ j, ((word j).length * C ^ (steps j).length + 1 : ℕ) *
        (α + Real.log R / V * β j) := by
  apply (formula_coprimality_removal prime hpInj hprime
    (fun j => reconstructedWordFormula (steps j) (stage j) (word j)) coord hzero
    μ hμ hmass α V R β hα hβ hV hR hmax hpmax hlower hupper
    (fun j => reconstructedWordFormula_inputsBounded _ _ _ R (by linarith) (hfreq j))
    W B hB hW).trans
  apply mul_le_mul_of_nonneg_left _ hB
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast reconstructedWordFormula_cost (steps j) (stage j) (word j) C hC (hsize j)
  · exact add_nonneg hα (mul_nonneg (div_nonneg (Real.log_nonneg (by linarith)) hV.le) (hβ j))

end Ostmann

end OAI
