import OAI.Combinatorics.EditApproximation.Coarse.CoarseCompleteWork

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem coarseActiveChildrenWork_const_bound {B d : ℕ} {α : Type*} (Q lam allowance : ℚ) (C : ℕ)
    (work : CoarseSourceTree B α d → CoarseThresholdDraws B d → ℚ → ℕ)
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d))
    (hc : ∀ child draw below, (child, draw, below) ∈ children →
      work child below (lam * coarseChildThreshold B Q allowance draw) ≤ C) :
    coarseActiveChildrenWork Q lam allowance work children ≤ children.length * C := by
  induction children with
  | nil => simp only [coarseActiveChildrenWork, List.length_nil, Nat.zero_mul, le_refl]
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    have hi := hc child draw below List.mem_cons_self
    have hr := ih (fun c r b h => hc c r b (List.mem_cons_of_mem _ h))
    rw [coarseActiveChildrenWork, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

attribute [local irreducible] coarseActiveArrayWork

theorem coarseActiveArrayWork_le_complete {B d : ℕ} {α : Type*} (k : ℕ) (Q lam : ℚ)
    (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d) (allowance : ℚ) :
    coarseActiveArrayWork k Q lam tree draws allowance ≤
      (B * (2 * k + 1)) * coarseCompleteNodes B d := by
  induction tree generalizing allowance with
  | leaf letter =>
    rw [coarseActiveArrayWork]
    split_ifs <;> simp only [coarseCompleteNodes, Nat.mul_one] <;> omega
  | @branch d children ih =>
    obtain ⟨draws, below⟩ := draws
    have hr := coarseActiveChildrenWork_const_bound Q lam allowance
      ((B * (2 * k + 1)) * coarseCompleteNodes B d)
      (fun child => coarseActiveArrayWork k Q lam child)
      (List.ofFn fun i => (children i, draws i, below i)) (by
        intro child draw b hb
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hb
        cases hi
        exact ih i (below i) _)
    simp only [List.length_ofFn] at hr
    rw [coarseActiveArrayWork]
    split_ifs
    · exact Nat.zero_le _
    · rw [coarseCompleteNodes]
      nlinarith only [hr]

end BinaryFraction
end EditApproximation

end OAI
