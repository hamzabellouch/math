import OAI.NumberTheory.Ostmann.Construction.SupportedPivotTransfer

namespace OAI

/-! # The supported transfer from actual prime tuples to positive integers -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def positiveIntegerPivotKey (M : ℕ) (hM : 0 < M) (L : ℕ) (v : ℤ) : Fin M := by
  letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  exact pivotResidueKey M L v

theorem transferPrimeTupleProduct_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (x : Fin n → P) : 0 < ∏ i, (x i : ℕ) :=
  Finset.prod_pos (fun i _ => (hP (x i) (x i).property).pos)

noncomputable def primeTuplePivotKey (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (x : Fin n → P) (L : ℕ) (v : ℤ) : Fin (∏ i, (x i : ℕ)) :=
  positiveIntegerPivotKey _ (transferPrimeTupleProduct_pos P hP x) L v

/-- All coprimality and interval restrictions may remain in `c`. The
extended integer has no prime tuple or character attached to it. -/
theorem original_pivot_transfer_real {A : Type*} [Fintype A]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (Q : Fin n → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (S : Finset (Fin n → P)) (hS : ∀ x ∈ S, Function.Injective x)
    (T : Finset ℕ) (hTpos : ∀ M ∈ T, 0 < M)
    (hT : ∀ x ∈ S, (∏ i, (x i : ℕ)) ∈ T)
    (row : ∀ x : Fin n → P, Fin (∏ i, (x i : ℕ)) → ℂ)
    (hrow : ∀ x ∈ S, ∀ u, ‖row x u‖ ≤ 1)
    (L : A → ℕ) (v : A → ℤ) (c : ℕ → A → ℂ)
    (hL : ∀ M ∈ T, ∀ a, c M a ≠ 0 → (L a).Coprime M) :
    ‖∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
      ∑ a, row x (primeTuplePivotKey P hP x (L a) (v a)) * c (∏ i, (x i : ℕ)) a‖ ^ 2 ≤
      ((n.factorial : ℝ) * ∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) *
        ((∑ M ∈ T, (pivotDiagonal L v (c M)).re) +
          (∑ M ∈ T, pivotOffDiagonal M L v (c M)).re) := by
  let B : (M : ℕ) → Fin M → ℂ := fun M =>
    if hM : 0 < M then
      groupedCoefficient (fun a => positiveIntegerPivotKey M hM (L a) (v a)) (c M)
    else fun _ => 0
  have he : (∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
      ∑ a, row x (primeTuplePivotKey P hP x (L a) (v a)) * c (∏ i, (x i : ℕ)) a) =
      ∑ x ∈ S, (productPrior (fun i => primeSubsetPrior P (Q i)) x : ℂ) *
        ∑ u, row x u * B (∏ i, (x i : ℕ)) u := by
    apply Finset.sum_congr rfl
    intro x _
    have hx := transferPrimeTupleProduct_pos P hP x
    simp only [B, dite_eq_left hx]
    congr 1
    exact pivot_residue_grouping (fun a => primeTuplePivotKey P hP x (L a) (v a))
      (row x) (c (∏ i, (x i : ℕ)))
  rw [he]
  have hb := pivot_integer_transfer P hP Q hQP hQ S hS T hT row hrow B
  apply hb.trans_eq
  congr 1
  calc
    _ = ∑ M ∈ T, ((pivotDiagonal L v (c M)).re + (pivotOffDiagonal M L v (c M)).re) := by
      apply Finset.sum_congr rfl
      intro M hMT
      have hM := hTpos M hMT
      let : NeZero M := ⟨Nat.ne_of_gt hM⟩
      simpa only [B, dite_eq_left hM, positiveIntegerPivotKey] using
        pivot_square_split_on_support M L v (c M) (hL M hMT)
    _ = _ := by rw [Finset.sum_add_distrib, Complex.re_sum]

end Ostmann

end OAI
