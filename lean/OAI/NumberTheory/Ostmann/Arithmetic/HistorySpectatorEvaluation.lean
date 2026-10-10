import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFiniteFieldReversal
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySpectatorDenominator
import OAI.NumberTheory.Ostmann.Construction.HistoryFactorization

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistoryTreeParameters
open Construction HistoryResidueRegular

variable {q : ℕ} [Fact q.Prime]

def conjugateIf (sign : Bool) (z : ℂ) : ℂ := if sign then conj z else z

theorem conjugateIf_mul_conj (sign : Bool) (z w : ℂ) :
    conjugateIf sign (z*conj w) = conjugateIf sign z * conjugateIf (!sign) w := by
  cases sign <;> simp [conjugateIf,map_mul]

theorem evaluate_node_actual {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right))
    (g : ZMod q → ℂ) (D : (ZMod q)ˣ) (sign : Bool) :
    Tree.Parameters.evaluate g D (parameters V outside _ hs hr sign)
      (giantPlusUnit _ hr) (giantMinusUnit _ hr) (argument D a) (leafBulk _ hr) =
      Tree.Parameters.evaluate g D
        (parameters V outside left (History.supported_left hs) (left_regular hr) sign)
        (giantPlusUnit left (left_regular hr)) (giantMinusUnit left (left_regular hr))
        (argument D left.root) (leafBulk left (left_regular hr)) *
      Tree.Parameters.evaluate g D
        (parameters V outside right (History.supported_right hs) (right_regular hr) (!sign))
        (giantPlusUnit right (right_regular hr)) (giantMinusUnit right (right_regular hr))
        (argument D right.root) (leafBulk right (right_regular hr)) := by
  simp only [parameters,Tree.Parameters.evaluate,leafBulk_child_left,leafBulk_child_right,
    frequency_parameters]
  change (if hz : nodePivot hs hr = 0 then (0:ℂ) else _) = _
  rw [dite_eq_right (nodePivot_ne_zero hs hr)]
  change Tree.Parameters.evaluate g D (parameters V outside left _ _ sign)
      (pivotUnit hs hr) (giantPlusUnit _ hr)
      ((frequencyUnit left (left_regular hr):ZMod q) /
        ((D:ZMod q)*(pivotUnit hs hr:ZMod q)*(splitConstant hs hr:ZMod q)*
          (giantPlusUnit _ hr * leftConstant hs hr *
            Tree.Parameters.leafProduct (leafBulk left (left_regular hr)) : (ZMod q)ˣ)))
      (leafBulk left (left_regular hr)) *
    Tree.Parameters.evaluate g D (parameters V outside right _ _ (!sign))
      (pivotUnit hs hr) (giantMinusUnit _ hr)
      ((frequencyUnit right (right_regular hr):ZMod q) /
        ((D:ZMod q)*(pivotUnit hs hr:ZMod q)*(splitConstant hs hr:ZMod q)*
          (giantMinusUnit _ hr * rightConstant hs hr *
            Tree.Parameters.leafProduct (leafBulk right (right_regular hr)) : (ZMod q)ˣ)))
      (leafBulk right (right_regular hr)) = _
  apply congrArg₂ (fun z w : ℂ => z*w)
  · rw [outgoing_left,pivotUnit_left,parentPlus_eq_childMinus hs hr]
  · rw [outgoing_right,pivotUnit_right,parentMinus_eq_childMinus hs hr]

theorem evaluate_eq_leafProduct {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (hr : Regular q h)
    (g : ZMod q → ℂ) (D : (ZMod q)ˣ) (sign : Bool) :
    Tree.Parameters.evaluate g D (parameters V outside h hs hr sign)
      (giantPlusUnit h hr) (giantMinusUnit h hr) (argument D h.root) (leafBulk h hr) =
      conjugateIf sign (History.leafProduct (fun a => g (argument D a)) h) := by
  induction h generalizing sign with
  | leaf a => cases sign <;> rfl
  | @node l a p u hp hm left right ihl ihr =>
      refine (evaluate_node_actual hs hr g D sign).trans ?_
      rw [ihl (History.supported_left hs) (left_regular hr) sign,
        ihr (History.supported_right hs) (right_regular hr) (!sign)]
      exact (conjugateIf_mul_conj sign _ _).symm

theorem diagram_value_eq_leafProduct {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History (l+1)) (hs : h.Supported V outside) (hr : Regular q h)
    (g : ZMod q → ℂ) (D : (ZMod q)ˣ) :
    (diagram h hs hr D).value g (leafBulk h hr) =
      History.leafProduct (fun a => g (argument D a)) h := by
  cases h with
  | node a p u hp hm left right =>
      simpa only [Tree.Diagram.value,diagram,Tree.Parameters.value,parameters,
        Tree.Parameters.evaluate,conjugateIf,Bool.false_eq_true,ite_false]
        using evaluate_eq_leafProduct (.node a p u hp hm left right) hs hr g D false

theorem argument_denominatorUnit {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {h : History l} (hs : h.Supported V outside) (hq : q∈outside) (a : State) :
    argument (denominatorUnit hs hq) a =
      modFraction q a.frequency ((outsideProduct outside/q)*a.product) := by
  simp only [argument,denominatorUnit_coe,modFraction,Nat.cast_mul,div_eq_mul_inv]

theorem spectator_eq_diagram {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History (l+1)) (hs : h.Supported V outside) (hq : q∈outside)
    (hV : ∀j≤l+1,V j<q) (g : ZMod q → ℂ) :
    History.leafProduct (fun a => g (modFraction q a.frequency
      ((outsideProduct outside/q)*a.product))) h =
      (diagram h hs (supported_regular h hs hq hV) (denominatorUnit hs hq)).value g
        (leafBulk h (supported_regular h hs hq hV)) := by
  rw [diagram_value_eq_leafProduct]
  simp only [argument_denominatorUnit hs hq]

end Ostmann.Arithmetic.HistoryTreeParameters

end

end OAI
