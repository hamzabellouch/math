import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramAlgebra

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistorySignedSpectatorDiagram
open Construction HistoryResidueRegular HistoryTreeParameters HistorySignedSpectatorCRT
variable {q : ℕ} [Fact q.Prime]

theorem treePivot_eq_residuePivot {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (History.node a p u hp hm left right)) (Xp Xm : (ZMod q)ˣ) :
    ((frequencyUnit left (left_regular hr):ZMod q)*
      ((Xm*rightConstant hs hr*Tree.Parameters.leafProduct (leafBulk right (right_regular hr)):
        (ZMod q)ˣ):ZMod q)-
      (frequencyUnit right (right_regular hr):ZMod q)*
      ((Xp*leftConstant hs hr*Tree.Parameters.leafProduct (leafBulk left (left_regular hr)):
        (ZMod q)ˣ):ZMod q))/
      ((frequencyUnit _ hr:ZMod q)*(splitConstant hs hr:ZMod q))=
      residuePivot q a left.root.frequency right.root.frequency u hp hm Xp Xm := by
  rw [left_product_variable hs hr Xp,right_product_variable hs hr Xm]
  rfl

theorem evaluate_variable_roots {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (hr : Regular q h)
    (g : ZMod q→ℂ) (hg : g 0=0) (D : (ZMod q)ˣ) (sign : Bool)
    (Xp Xm : (ZMod q)ˣ) :
    Tree.Parameters.evaluate g D (parameters V outside h hs hr sign) Xp Xm
      (primeArgument q D h.root Xp Xm) (leafBulk h hr)=
      conjugateIf sign (primeSpectator q g D h Xp Xm) := by
  induction h generalizing sign Xp Xm with
  | leaf a => cases sign <;> rfl
  | node a p u hp hm left right il ir =>
    simp only [parameters,Tree.Parameters.evaluate,leafBulk_child_left,leafBulk_child_right,
      frequency_parameters]
    simp only [treePivot_eq_residuePivot hs hr Xp Xm]
    split_ifs with hz
    · rw [primeSpectator,primeSpectator_zero_of_giant q g hg D left _ _ (Or.inl hz),zero_mul]
      cases sign <;> simp [conjugateIf]
    · rw [outgoing_left_variable hs hr D,outgoing_right_variable hs hr D,
        il (History.supported_left hs) (left_regular hr) sign,
        ir (History.supported_right hs) (right_regular hr) (!sign)]
      exact (conjugateIf_mul_conj sign _ _).symm

def variableDiagram {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h : History (l+1)) (hs : h.Supported V outside) (hr : Regular q h)
    (D Xp Xm : (ZMod q)ˣ) : Tree.Diagram (ZMod q) (l+1) where
  parameters := parameters V outside h hs hr false
  denominator := D
  rootLeft := Xp
  rootRight := Xm
  consistent := parameters_consistent h hs hr false
  bottomOpposite := parameters_bottomOpposite h hs hr false

theorem variableDiagram_value {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h : History (l+1)) (hs : h.Supported V outside) (hr : Regular q h)
    (g : ZMod q→ℂ) (hg : g 0=0) (D Xp Xm : (ZMod q)ˣ) :
    (variableDiagram h hs hr D Xp Xm).value g (leafBulk h hr)=
      primeSpectator q g D h Xp Xm := by
  cases h with
  | node a p u hp hm left right =>
    simpa only [variableDiagram,Tree.Diagram.value,Tree.Parameters.value,parameters,
      Tree.Parameters.evaluate,conjugateIf,Bool.false_eq_true,ite_false] using
      evaluate_variable_roots (.node a p u hp hm left right) hs hr g hg D false Xp Xm

end Ostmann.Arithmetic.HistorySignedSpectatorDiagram

end

end OAI
