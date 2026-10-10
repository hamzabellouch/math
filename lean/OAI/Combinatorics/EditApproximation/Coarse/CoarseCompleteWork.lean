import OAI.Combinatorics.EditApproximation.Coarse.CoarseBinaryWeight

namespace OAI

namespace EditApproximation
namespace BinaryFraction

def coarseCompleteNodes (B : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => 1 + B * coarseCompleteNodes B d

theorem coarseCompleteNodes_pos (B d : ℕ) : 1 ≤ coarseCompleteNodes B d := by
  cases d <;> simp only [coarseCompleteNodes] <;> omega

theorem coarseCompleteNodes_le (B d : ℕ) (hB : 2 ≤ B) :
    coarseCompleteNodes B d + 1 ≤ 2 * B ^ d := by
  induction d with
  | zero => simp only [coarseCompleteNodes, pow_zero]; omega
  | succ d ih =>
    have hm := Nat.mul_le_mul_left B ih
    rw [coarseCompleteNodes, pow_succ]
    nlinarith only [hm, hB]

theorem coarseBinaryChildrenWeight_const_bound {B d : ℕ} {α : Type*} (q L C : ℕ)
    (weight : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ)
    (allowance : BinaryFraction) (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d))
    (hc : ∀ child draw below, (child, draw, below) ∈ children →
      weight child below (coarseChildAllowanceWithWork L
        (coarseChildThresholdWithWork B q allowance draw).1).1 ≤ C) :
    coarseBinaryChildrenWeight q L weight allowance children ≤ children.length * C := by
  induction children with
  | nil => simp only [coarseBinaryChildrenWeight, List.length_nil, Nat.zero_mul, le_refl]
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    have hi := hc child draw below List.mem_cons_self
    have hr := ih (fun c r b h => hc c r b (List.mem_cons_of_mem _ h))
    rw [coarseBinaryChildrenWeight, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

attribute [local irreducible] coarseBinaryWeight

theorem coarseBinaryWeight_le_complete {B d : ℕ} {α : Type*} (k q L : ℕ)
    (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d) (allowance : BinaryFraction) :
    coarseBinaryWeight k q L tree draws allowance ≤
      (B * (2 * k + 1) + 1) * coarseCompleteNodes B d := by
  induction tree generalizing allowance with
  | leaf letter =>
    rw [coarseBinaryWeight]
    split_ifs <;> simp only [coarseCompleteNodes, Nat.mul_one] <;> omega
  | @branch d children ih =>
    obtain ⟨draws, below⟩ := draws
    have hr := coarseBinaryChildrenWeight_const_bound q L
      ((B * (2 * k + 1) + 1) * coarseCompleteNodes B d)
      (fun child => coarseBinaryWeight k q L child) allowance
      (List.ofFn fun i => (children i, draws i, below i)) (by
        intro child draw b hb
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hb
        cases hi
        exact ih i (below i) _)
    simp only [List.length_ofFn] at hr
    rw [coarseBinaryWeight]
    split_ifs
    · have hc := coarseCompleteNodes_pos B (d + 1)
      have hp := Nat.mul_le_mul (show 1 ≤ B * (2 * k + 1) + 1 by omega) hc
      simpa only [Nat.one_mul] using hp
    · rw [coarseCompleteNodes]
      nlinarith only [hr]

end BinaryFraction
end EditApproximation

end OAI
