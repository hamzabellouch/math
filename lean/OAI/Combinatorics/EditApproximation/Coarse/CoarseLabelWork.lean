import OAI.Combinatorics.EditApproximation.Coarse.CoarseWork
import OAI.Combinatorics.EditApproximation.Probability.ExactSampling
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- Only expanded internal nodes request their child thresholds. The full
product seed is a specification; labels below a pruned node are never read. -/




private theorem coarseLabelChildren_le {B d : ℕ} {α : Type*} (Q lam allowance : ℚ)
    (labels arrays : CoarseSourceTree B α d → CoarseThresholdDraws B d → ℚ → ℕ)
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d))
    (hle : ∀ child draw below, (child, draw, below) ∈ children → ∀ a, labels child below a ≤ arrays child below a) :
    coarseLabelChildren Q lam allowance labels children ≤
      coarseActiveChildrenWork Q lam allowance arrays children := by
  induction children with
  | nil => exact le_rfl
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    exact Nat.add_le_add (hle child draw below List.mem_cons_self _)
      (ih (fun child draw below hmem => hle child draw below (List.mem_cons_of_mem _ hmem)))

 theorem coarseLabelCount_le_arrayWork {B d : ℕ} {α : Type*} (k : ℕ) (Q lam : ℚ)
    (tree : CoarseSourceTree B α d) (draws : CoarseThresholdDraws B d) (allowance : ℚ) :
    coarseLabelCount Q lam tree draws allowance ≤ coarseActiveArrayWork k Q lam tree draws allowance := by
  induction tree generalizing allowance with
  | leaf letter =>
    simp only [coarseLabelCount, coarseActiveArrayWork]
    split_ifs <;> omega
  | branch children ih =>
    obtain ⟨draws, below⟩ := draws
    simp only [coarseLabelCount, coarseActiveArrayWork]
    split_ifs
    · exact le_rfl
    · have hc := coarseLabelChildren_le Q lam allowance
        (fun child => coarseLabelCount Q lam child)
        (fun child => coarseActiveArrayWork k Q lam child)
        (List.ofFn fun i => (children i, draws i, below i)) (by
          intro child draw childBelow hmem a
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
          cases hi
          exact ih i (below i) a)
      have hunit : B ≤ B * (2 * k + 1) := by nlinarith
      exact Nat.add_le_add hunit hc

/-- Power-of-two threshold sampling consumes exactly the fixed word length
per used label. `binaryWord_uniform` proves the output law of every draw. -/
def coarseThresholdBitWork {d : ℕ} {α : Type*} (r : ℕ) (Q lam : ℚ)
    (tree : CoarseSourceTree (2 ^ r) α d) (draws : CoarseThresholdDraws (2 ^ r) d)
    (allowance : ℚ) : ℕ := r * coarseLabelCount Q lam tree draws allowance

 theorem coarseThresholdBitWork_le {d : ℕ} {α : Type*} (r k : ℕ) (Q lam : ℚ)
    (tree : CoarseSourceTree (2 ^ r) α d) (draws : CoarseThresholdDraws (2 ^ r) d)
    (allowance : ℚ) :
    coarseThresholdBitWork r Q lam tree draws allowance ≤
      r * coarseActiveArrayWork k Q lam tree draws allowance :=
  Nat.mul_le_mul_left r (coarseLabelCount_le_arrayWork k Q lam tree draws allowance)

end EditApproximation

end OAI
