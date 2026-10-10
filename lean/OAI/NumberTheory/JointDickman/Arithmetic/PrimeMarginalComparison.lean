import OAI.NumberTheory.JointDickman.Arithmetic.PartialPrimeChannel

namespace OAI

/-! # Comparing the independent common/exclusive marginal with a fair split -/

namespace JointDickman

open scoped BigOperators

open Classical in
theorem independentPrimeCellMass_eq_marginal {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (q : Q → ℝ) (cell : ℕ → Option A) (a : A) :
    (∑ y, if cell (independentSplitProducts Q y).1 = some a then
      bernoulliProductMass Finset.univ (fun p (_ : Fin 3) => q p) y else 0) =
      independentCellMarginal (bernoulliSiteMass q) (bernoulliSiteMass q)
        (primeProductCell Q cell) a := by
  have h := independentCategory_triple_test q
    (fun c e₁ _ => if primeProductCell Q cell c e₁ = some a then 1 else 0)
  have hl : (∑ y, if cell (independentSplitProducts Q y).1 = some a then
      bernoulliProductMass Finset.univ (fun p (_ : Fin 3) => q p) y else 0) =
      ∑ y, bernoulliProductMass Finset.univ (fun p (_ : Fin 3) => q p) y *
        (if primeProductCell Q cell ((categoryTripleEquiv Q y).1)
          ((categoryTripleEquiv Q y).2.1) = some a then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro y _
    rw [categoryPrimeProduct_eq_retained]
    dsimp only [primeProductCell]
    split_ifs <;> simp_all
  rw [hl, h]
  unfold independentCellMarginal optionCellMass
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : primeProductCell Q cell c e = some a
  · simp only [he, ite_true, mul_one]
    rw [← Finset.mul_sum, bernoulliSiteMass_sum, mul_one]
  · simp [he]

open Classical in
/-- The two-split comparison already controls the one-coordinate marginal;
no new coupling assumption is needed. -/
theorem independentPrimeMarginal_fair_error {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → Option A) (a : A) :
    |independentCellMarginal (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeProductCell Q cell) a -
      optionCellMass (bernoulliSiteMass (fun p : Q => 1 / (2 * (p.val : ℝ))))
        (fun y => cell (retainedPrimeProduct Q y)) a| ≤ 9 / (8 * N : ℝ) := by
  let S : Set ℕ := {n | cell n = some a}
  have h := twoSplitPrimeProducts_cell_tail_bound Q hQ hN hcut S Set.univ
  have huniv (x : Q → Bool) : fairSplitPrimeCell Q Set.univ x = 1 := by
    rw [fairSplitPrimeCell_eq]
    simp only [Set.mem_univ, ite_true, fairRetentionMass_sum]
  have ha : (∑ x, if (actualSplitProducts Q x).1 ∈ S ∧
      (actualSplitProducts Q x).2 ∈ Set.univ then
        sameSiteTwoSplitProductMass (fun p : Q => 1 / (p.val : ℝ)) x else 0) =
      optionCellMass (bernoulliSiteMass (fun p : Q => 1 / (2 * (p.val : ℝ))))
        (fun y => cell (retainedPrimeProduct Q y)) a := by
    have hj := fairSplitPrimeCell_joint Q (fun p : Q => 1 / (p.val : ℝ)) S Set.univ
    have hm := fairSplitPrimeCell_marginal Q S
    simp_rw [huniv, mul_one] at hj
    have heq : (∑ x, if (actualSplitProducts Q x).1 ∈ S ∧
        (actualSplitProducts Q x).2 ∈ Set.univ then
          sameSiteTwoSplitProductMass (fun p : Q => 1 / (p.val : ℝ)) x else 0) =
        ∑ x, bernoulliSiteMass (fun p : Q => 1 / (p.val : ℝ)) x * fairSplitPrimeCell Q S x := by
      convert hj.symm using 1
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> rfl
    calc
      _ = _ := heq
      _ = _ := hm
      _ = _ := by
        unfold optionCellMass
        apply Finset.sum_congr rfl
        intro y _
        dsimp only [S, Set.mem_ofPred_eq]
        split_ifs <;> rfl
  have hi : (∑ y, if (independentSplitProducts Q y).1 ∈ S ∧
      (independentSplitProducts Q y).2 ∈ Set.univ then
        bernoulliProductMass Finset.univ
          (fun (p : Q) (_ : Fin 3) => 1 / (4 * (p.val : ℝ))) y else 0) =
      independentCellMarginal (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeProductCell Q cell) a := by
    simp only [Set.mem_univ, and_true, S, Set.mem_ofPred_eq]
    exact independentPrimeCellMass_eq_marginal Q _ cell a
  have hh : |optionCellMass (bernoulliSiteMass (fun p : Q => 1 / (2 * (p.val : ℝ))))
        (fun y => cell (retainedPrimeProduct Q y)) a -
      independentCellMarginal (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeProductCell Q cell) a| ≤ 9 / (8 * N : ℝ) := by
    convert h using 1
    convert congrArg abs (congrArg₂ (fun x y : ℝ => x - y) ha.symm hi.symm) using 1
    congr 4 <;> funext x <;> split_ifs <;> rfl
  rwa [abs_sub_comm] at hh

end JointDickman

end OAI
