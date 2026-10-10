import OAI.NumberTheory.Ostmann.Arithmetic.HistoryResidueUnits
import OAI.NumberTheory.Ostmann.Tree.Diagram

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryTreeParameters
open Construction HistoryBulkProducts HistoryResidueRegular

variable {q : ℕ} [Fact q.Prime]

def parameters (V : ℕ → ℕ) (outside : List ℕ) :
    {l : ℕ} → (h : History l) → h.Supported V outside → Regular q h → Bool →
      Tree.Parameters (ZMod q) l
  | 0, .leaf a, _, hr, sign => .leaf (frequencyUnit (.leaf a) hr) sign
  | _+1, .node a p u hp hm left right, hs, hr, sign =>
      .branch (frequencyUnit (.node a p u hp hm left right) hr) (leftConstant hs hr) (rightConstant hs hr)
        (splitConstant hs hr)
        (parameters V outside left (History.supported_left hs) (left_regular hr) sign)
        (parameters V outside right (History.supported_right hs) (right_regular hr) (!sign))

@[simp] theorem frequency_parameters {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (hr : Regular q h) (sign : Bool) :
    (parameters V outside h hs hr sign).frequency = frequencyUnit h hr := by
  cases h <;> rfl

theorem fixedUnit_node {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) :
    fixedUnit _ hr = leftConstant hs hr * rightConstant hs hr := by
  apply Units.ext
  change (fixedProduct a.small : ZMod q) = (fixedProduct hp:ZMod q)*(fixedProduct hm:ZMod q)
  rw [(supported_product_split hs).2,Nat.cast_mul]

theorem fixedUnit_left {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) :
    fixedUnit left (left_regular hr) = splitConstant hs hr * leftConstant hs hr := by
  apply Units.ext
  change (fixedProduct left.root.small : ZMod q) =
    ((u.map SmallSlot.value).prod:ZMod q)*(fixedProduct hp:ZMod q)
  rw [(supported_child_products hs (History.supported_compensation_roles hs)).2.2.1,Nat.cast_mul]

theorem fixedUnit_right {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) :
    fixedUnit right (right_regular hr) = splitConstant hs hr * rightConstant hs hr := by
  apply Units.ext
  change (fixedProduct right.root.small : ZMod q) =
    ((u.map SmallSlot.value).prod:ZMod q)*(fixedProduct hm:ZMod q)
  rw [(supported_child_products hs (History.supported_compensation_roles hs)).2.2.2,Nat.cast_mul]

theorem parameters_childConsistent {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (hr : Regular q h) (sign : Bool) :
    (parameters V outside h hs hr sign).childConsistent (fixedUnit h hr) := by
  cases h with
  | leaf a => trivial
  | node a p u hp hm left right => exact (fixedUnit_node hs hr).symm

theorem parameters_consistent {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (hr : Regular q h) (sign : Bool) :
    (parameters V outside h hs hr sign).consistent := by
  induction h generalizing sign with
  | leaf a => trivial
  | @node l a p u hp hm left right ihl ihr =>
      change (parameters V outside left _ _ sign).childConsistent _ ∧
        (parameters V outside right _ _ (!sign)).childConsistent _ ∧ _ ∧ _
      refine ⟨?_,?_,ihl (History.supported_left hs) (left_regular hr) sign,
        ihr (History.supported_right hs) (right_regular hr) (!sign)⟩
      · rw [← fixedUnit_left hs hr]
        exact parameters_childConsistent left _ _ sign
      · rw [← fixedUnit_right hs hr]
        exact parameters_childConsistent right _ _ (!sign)

theorem parameters_bottomOpposite {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (hr : Regular q h) (sign : Bool) :
    (parameters V outside h hs hr sign).bottomOpposite := by
  induction h generalizing sign with
  | leaf a => trivial
  | @node l a p u hp hm left right ihl ihr =>
      cases l with
      | zero =>
          cases left
          cases right
          cases sign <;> simp [parameters,Tree.Parameters.bottomOpposite]
      | succ l =>
          exact ⟨ihl (History.supported_left hs) (left_regular hr) sign,
            ihr (History.supported_right hs) (right_regular hr) (!sign)⟩

def diagram {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History (l+1)) (hs : h.Supported V outside) (hr : Regular q h)
    (D : (ZMod q)ˣ) : Tree.Diagram (ZMod q) (l+1) where
  parameters := parameters V outside h hs hr false
  denominator := D
  rootLeft := giantPlusUnit h hr
  rootRight := giantMinusUnit h hr
  consistent := parameters_consistent h hs hr false
  bottomOpposite := parameters_bottomOpposite h hs hr false

end Ostmann.Arithmetic.HistoryTreeParameters

end

end OAI
