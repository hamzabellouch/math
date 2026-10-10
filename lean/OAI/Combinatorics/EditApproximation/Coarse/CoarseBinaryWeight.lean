import OAI.Combinatorics.EditApproximation.Coarse.CoarseBinaryEvaluation
import OAI.Combinatorics.EditApproximation.Coarse.CoarseLabelWork

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Sum the weights of exactly those child calls made by the binary loop. -/
def coarseBinaryChildrenWeight {B d : ℕ} {α : Type*} (q L : ℕ)
    (weight : CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ)
    (allowance : BinaryFraction) :
    List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d) → ℕ
  | [] => 0
  | (child, draw, below) :: rest =>
    weight child below (coarseChildAllowanceWithWork L
      (coarseChildThresholdWithWork B q allowance draw).1).1 +
    coarseBinaryChildrenWeight q L weight allowance rest

/-- One array unit per expanded child shift and one unit per visited node.
This counter follows the executed pruning and threshold branches. -/
def coarseBinaryWeight {B : ℕ} {α : Type*} (k q L : ℕ) :
    {d : ℕ} → CoarseSourceTree B α d → CoarseThresholdDraws B d → BinaryFraction → ℕ
  | _, tree, draws, allowance =>
    if (leWithWork (nat tree.word.length) allowance).1 then 1 else
    match tree, draws with
    | .leaf _, _ => B * (2 * k + 1) + 1
    | .branch children, (draws, below) => B * (2 * k + 1) + 1 +
      coarseBinaryChildrenWeight q L (fun child => coarseBinaryWeight k q L child) allowance
        (List.ofFn fun i => (children i, draws i, below i))

def coarseChildrenSpan {B d : ℕ} {α : Type*} :
    List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d) → ℕ
  | [] => 0
  | (child, _, _) :: rest => child.word.length + coarseChildrenSpan rest

 theorem coarseChildrenSpan_eq {B d : ℕ} {α : Type*}
    (children : List (CoarseSourceTree B α d × Fin B × CoarseThresholdDraws B d)) :
    coarseChildrenSpan children = (children.map (fun data => data.1.word)).flatten.length := by
  induction children with
  | nil => rfl
  | cons data rest ih =>
    simp only [coarseChildrenSpan, List.map_cons, List.flatten_cons, List.length_append, ih]

 theorem coarseChildrenSpan_ofFn {B d : ℕ} {α : Type*}
    (children : Fin B → CoarseSourceTree B α d) (draws : Fin B → Fin B)
    (below : Fin B → CoarseThresholdDraws B d) :
    coarseChildrenSpan (List.ofFn fun i => (children i, draws i, below i)) =
      (CoarseSourceTree.branch children).word.length := by
  rw [coarseChildrenSpan_eq]
  simp only [List.map_ofFn, Function.comp_def, CoarseSourceTree.word]

end BinaryFraction
end EditApproximation

end OAI
