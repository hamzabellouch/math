import OAI.NumberTheory.DukePrimeDegree.Entropy.EntropyGraph

namespace OAI

/-!
# Entropy symmetry and the root coefficient balance

The entropy formula in EKL (2006), Proposition 3.1, is a sum of positive
root weights. Equality of the entropy of an invertible map and its inverse
then gives the row/column balance. The finite algebraic implication
uses trace-zero test weights independently of the dynamical entropy formula.
-/

noncomputable section
open scoped BigOperators Classical

namespace DukePrimeDegree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite positive-root expression in the entropy formula. -/
def rootEntropyForm (w : ι → ι → ℝ) (t : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * max (t i - t j) 0

omit [DecidableEq ι] in
lemma rootEntropyForm_shift (w : ι → ι → ℝ) (t : ι → ℝ) (c : ℝ) :
    rootEntropyForm w (fun i => t i - c) = rootEntropyForm w t := by
  unfold rootEntropyForm
  congr 1
  funext i
  congr 1
  funext j
  congr 2
  ring

lemma rootEntropyForm_indicator (w : ι → ι → ℝ) (a : ι) :
    rootEntropyForm w (fun i => if i = a then 1 else 0) =
      (∑ j, w a j) - w a a := by
  unfold rootEntropyForm
  rw [Finset.sum_eq_single a]
  · have h : (∑ j, w a j * max ((1 : ℝ) - (if j = a then 1 else 0)) 0) =
        ∑ j ∈ Finset.univ.erase a, w a j := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
      simp only [ite_true, sub_self, max_self, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro j hj
      simp [(Finset.mem_erase.mp hj).1]
    simp only [ite_true]
    rw [h, ← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
    ring
  · intro i _ hia
    apply Finset.sum_eq_zero
    intro j _
    by_cases hja : j = a <;> simp [hia, hja]
  · simp

lemma rootEntropyForm_neg_indicator (w : ι → ι → ℝ) (a : ι) :
    rootEntropyForm w (fun i => -(if i = a then 1 else 0)) =
      (∑ i, w i a) - w a a := by
  unfold rootEntropyForm
  rw [Finset.sum_comm, Finset.sum_eq_single a]
  · have h : (∑ i, w i a * max (-(if i = a then 1 else 0) - -(1 : ℝ)) 0) =
        ∑ i ∈ Finset.univ.erase a, w i a := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
      simp only [ite_true, sub_self, max_self, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro i hi
      simp [(Finset.mem_erase.mp hi).1]
    simp only [ite_true]
    rw [h, ← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
    ring
  · intro j _ hja
    apply Finset.sum_eq_zero
    intro i _
    by_cases hia : i = a <;> simp [hia, hja]
  · simp

/-- Trace-zero entropy symmetry implies the coefficient balance. The test
weight is the indicator of one coordinate minus its average. -/
theorem balanced_of_rootEntropyForm_symmetry
    (w : ι → ι → ℝ)
    (hsym : ∀ t : ι → ℝ, ∑ i, t i = 0 →
      rootEntropyForm w t = rootEntropyForm w (fun i => -t i)) :
    ∀ a, ∑ j, w a j = ∑ j, w j a := by
  intro a
  let c : ℝ := (Fintype.card ι : ℝ)⁻¹
  let t : ι → ℝ := fun i => (if i = a then 1 else 0) - c
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    let : Nonempty ι := ⟨a⟩
    exact_mod_cast Fintype.card_ne_zero
  have ht : ∑ i, t i = 0 := by
    simp [t, c, Finset.sum_sub_distrib, hn]
  have h := hsym t ht
  have htform : rootEntropyForm w t = rootEntropyForm w (fun i => if i = a then 1 else 0) :=
    rootEntropyForm_shift w _ c
  have hnegform : rootEntropyForm w (fun i => -t i) =
      rootEntropyForm w (fun i => -(if i = a then 1 else 0)) := by
    have heq : (fun i => -t i) = (fun i => -(if i = a then 1 else 0) - (-c)) := by
      funext i
      dsimp [t]
      ring
    rw [heq, rootEntropyForm_shift]
  rw [htform, hnegform, rootEntropyForm_indicator, rootEntropyForm_neg_indicator] at h
  linarith

/-- The purely finite part of EKL's coefficient symmetry conclusion. -/
theorem coefficients_symmetric_of_entropy_symmetry
    (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hsym : ∀ t : ι → ℝ, ∑ i, t i = 0 →
      rootEntropyForm w t = rootEntropyForm w (fun i => -t i))
    (hcomp : ∀ a b c, a ≠ c → 0 < w a b → 0 < w b c → w a c = 1) :
    ∀ a b, w a b = w b a :=
  coefficients_symmetric_of_balanced_two_step w hw
    (balanced_of_rootEntropyForm_symmetry w hsym) hcomp

end DukePrimeDegree

end

end OAI
