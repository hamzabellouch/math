import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinWords

namespace OAI

/-! # Difference bounds for the actual finite Dynkin polynomial

The middle input in a conjugation product vanishes at time zero. These
bounds retain that factor rather than losing it in an absolute polynomial
estimate; this gives polynomial coarse speed for Cartan-fiber paths.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped BigOperators

variable {L J I : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
  (b : Basis J ℝ L)

/-- A bracket word is Lipschitz on a coordinate ball, with one fewer
power of its radius than the absolute word bound. -/
theorem norm_basis_evalBracketWord_sub_le
    (X Y : I → L) {C M D : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C)
    (hX : ∀ i, ‖b.equivFun (X i)‖ ≤ M) (hY : ∀ i, ‖b.equivFun (Y i)‖ ≤ M)
    (hXY : ∀ i, ‖b.equivFun (X i - Y i)‖ ≤ D) (w : FreeMagma I) :
    ‖b.equivFun (evalBracketWord X w - evalBracketWord Y w)‖ ≤
      (bracketWordLength w : ℝ) * ((Fintype.card J : ℝ) ^ 2 * C) ^ bracketWordNodes w *
        M ^ bracketWordNodes w * D := by
  let K := (Fintype.card J : ℝ) ^ 2 * C
  have hK : 0 ≤ K := by positivity
  induction w using FreeMagma.rec with
  | of i => simpa [evalBracketWord, bracketWordLength, bracketWordNodes] using hXY i
  | mul u v hu hv =>
    have hxv := norm_basis_evalBracketWord_le b X hC hM hbracket hX v
    have hyu := norm_basis_evalBracketWord_le b Y hC hM hbracket hY u
    have he : ⁅evalBracketWord X u, evalBracketWord X v⁆ -
        ⁅evalBracketWord Y u, evalBracketWord Y v⁆ =
        ⁅evalBracketWord X u - evalBracketWord Y u, evalBracketWord X v⁆ +
          ⁅evalBracketWord Y u, evalBracketWord X v - evalBracketWord Y v⁆ := by
      simp only [sub_lie, lie_sub]
      abel
    change ‖b.equivFun (⁅evalBracketWord X u, evalBracketWord X v⁆ -
      ⁅evalBracketWord Y u, evalBracketWord Y v⁆)‖ ≤ _
    rw [he, map_add]
    calc
      _ ≤ ‖b.equivFun ⁅evalBracketWord X u - evalBracketWord Y u, evalBracketWord X v⁆‖ +
          ‖b.equivFun ⁅evalBracketWord Y u, evalBracketWord X v - evalBracketWord Y v⁆‖ :=
        norm_add_le _ _
      _ ≤ K * ‖b.equivFun (evalBracketWord X u - evalBracketWord Y u)‖ *
          ‖b.equivFun (evalBracketWord X v)‖ +
          K * ‖b.equivFun (evalBracketWord Y u)‖ *
            ‖b.equivFun (evalBracketWord X v - evalBracketWord Y v)‖ :=
        add_le_add (norm_basis_bracket_le b hC hbracket _ _)
          (norm_basis_bracket_le b hC hbracket _ _)
      _ ≤ K * ((bracketWordLength u : ℝ) * K ^ bracketWordNodes u * M ^ bracketWordNodes u * D) *
          (K ^ bracketWordNodes v * M ^ bracketWordLength v) +
          K * (K ^ bracketWordNodes u * M ^ bracketWordLength u) *
            ((bracketWordLength v : ℝ) * K ^ bracketWordNodes v * M ^ bracketWordNodes v * D) := by
        gcongr
      _ = _ := by
        simp only [bracketWordLength, bracketWordNodes, bracketWordLength_eq_nodes_add_one,
          Nat.cast_add, Nat.cast_one, pow_add, pow_one]
        ring

/-- Fixed finite Dynkin coefficients give a uniform polynomial Lipschitz
bound on coordinate balls. No extra group-law or analytic input is used. -/
theorem exists_finiteDynkinPolynomial_difference_bound
    {c n : ℕ} (a : DynkinCoefficients c n) {C : ℝ} (hC : 0 ≤ C)
    (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X Y : Fin n → L) (M D : ℝ), 0 ≤ M → 0 ≤ D →
      (∀ i, ‖b.equivFun (X i)‖ ≤ M) → (∀ i, ‖b.equivFun (Y i)‖ ≤ M) →
      (∀ i, ‖b.equivFun (X i - Y i)‖ ≤ D) →
      ‖b.equivFun (finiteDynkinPolynomial a X - finiteDynkinPolynomial a Y)‖ ≤
        A * (1 + M) ^ c * D := by
  let K := (Fintype.card J : ℝ) ^ 2 * C
  have hK : 0 ≤ K := by positivity
  let A := ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
    |a d w| * (d.val + 1) * K ^ d.val
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro X Y M D hM hD hX hY hXY
  have he : finiteDynkinPolynomial a X - finiteDynkinPolynomial a Y =
      ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
        a d w • (evalBracketWord X (rightNestedWord d.val w) -
          evalBracketWord Y (rightNestedWord d.val w)) := by
    simp only [finiteDynkinPolynomial, Finset.sum_sub_distrib, smul_sub]
  have hterm (d : Fin c) (w : Fin (d.val + 1) → Fin n) :
      ‖b.equivFun (a d w • (evalBracketWord X (rightNestedWord d.val w) -
        evalBracketWord Y (rightNestedWord d.val w)))‖ ≤
        (|a d w| * (d.val + 1) * K ^ d.val) * (1 + M) ^ c * D := by
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    have hh := norm_basis_evalBracketWord_sub_le b X Y hC hM hD hbracket hX hY hXY
      (rightNestedWord d.val w)
    simp only [rightNestedWord_length, rightNestedWord_nodes, Nat.cast_add, Nat.cast_one] at hh
    have hp : M ^ d.val ≤ (1 + M) ^ c :=
      (pow_le_pow_left₀ hM (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) d.isLt.le)
    calc
      _ ≤ |a d w| * ((d.val + 1) * K ^ d.val * M ^ d.val * D) :=
        mul_le_mul_of_nonneg_left hh (abs_nonneg _)
      _ ≤ |a d w| * ((d.val + 1) * K ^ d.val * (1 + M) ^ c * D) := by gcongr
      _ = _ := by ring
  rw [he, map_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
        (|a d w| * (d.val + 1) * K ^ d.val) * (1 + M) ^ c * D := by
      apply Finset.sum_le_sum
      intro d _
      rw [map_sum]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun w _ => hterm d w))
    _ = _ := by simp only [A, Finset.sum_mul]

end PolycyclicRecognition

end

end OAI
