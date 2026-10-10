import OAI.Computability.WLIdentification.SeedBits

namespace OAI

namespace WLIdentification
namespace Machine
open BinaryAddress
 theorem initialSeedLetter_inl (M : Machine) (d : ℕ) (w : Word) (hsize : inputSpan w<2^d) (i : Fin (inputSpan w)) :
    M.initialSeedLetter d w (.inl i) =
      ((w[i.val]?).elim 0 (inputSymbol M), if i.val=0 then some 0 else none) := by
  have hi : i.val<2^d := i.isLt.trans hsize
  have hz : ofNat d i.val=(fun _ => false) ↔ i.val=0 := by
    constructor
    · intro h
      have := congrArg value h
      simpa only [value_ofNat d i.val hi,value_zero] using this
    · intro h; rw [h,ofNat_zero]
  simp only [initialSeedLetter,TapeConfig.letter,ringInitial,value_ofNat d i.val hi,hz]
end Machine
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
namespace InitialRealizer
open Machine
variable (M : Machine) (d : Word → ℕ) (dp : NatPoly (fun X : Fin 1 → Word => d (X 0)))
    (hsize : ∀ w,inputSpan w<2^d w)

def letterEval (f : M.Letter → ℕ) (w : Word) (i : ℕ) : ℕ :=
  if i<w.length then
    if i=0 then if w[i]?.getD false then f (inputSymbol M true,some 0) else f (inputSymbol M false,some 0)
    else if w[i]?.getD false then f (inputSymbol M true,none) else f (inputSymbol M false,none)
  else if i=0 then f (0,some 0) else f (0,none)

theorem letterEval_poly (f : M.Letter → ℕ) : NatPoly (fun X : Fin 2 → Word => letterEval M f (X 0) (X 1).length) := by
  unfold letterEval
  apply NatPoly.iteProp (NatPoly.lt (NatPoly.var 1) (NatPoly.var 0))
  · apply NatPoly.iteProp (NatPoly.eqtest (NatPoly.var 1) (NatPoly.const 0))
    · exact NatPoly.ite (Poly.nth (Poly.var 0) (NatPoly.var 1)) (NatPoly.const _) (NatPoly.const _)
    · exact NatPoly.ite (Poly.nth (Poly.var 0) (NatPoly.var 1)) (NatPoly.const _) (NatPoly.const _)
  · exact NatPoly.iteProp (NatPoly.eqtest (NatPoly.var 1) (NatPoly.const 0)) (NatPoly.const _) (NatPoly.const _)

noncomputable def positionLetter (f : M.Letter → ℕ) : Number positionP (fun w i => f (M.initialSeedLetter (d w) w (.inl i))) where
  eval := letterEval M f
  correct w i := by
    rw [M.initialSeedLetter_inl (d w) w (hsize w) i]
    change letterEval M f w i.val=f _
    unfold letterEval
    by_cases hi : i.val<w.length
    · rw [ite_eq_left hi,List.getElem?_eq_getElem hi,Option.getD_some,Option.elim_some]
      by_cases hz : i.val=0 <;> cases w[i.val] <;> simp [hz]
    · rw [ite_eq_right hi,List.getElem?_eq_none (by omega),Option.elim_none]
      split <;> rfl
  poly := letterEval_poly M f

noncomputable def seedLetter (f : M.Letter → ℕ) : Number (seedP d dp) (fun w z => f (M.initialSeedLetter (d w) w z)) :=
  (Number.sumCases (positionLetter M d hsize f) (Number.const _ (f (0,none)))).congr
    (by intro w x; cases x <;> rfl)
end InitialRealizer
end FinitePresentation

end WLIdentification

end OAI
