import OAI.NumberTheory.Ostmann.Tree.PairMellinVariables
import OAI.NumberTheory.Ostmann.Tree.TwistedPairSpectrum

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem twoPairValue_doubleMellin (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (ν χ ψ : MulChar (ZMod p) ℂ) (d e : ZMod p)
    (hg0 : g 0=0) (hh0 : h 0=0) :
    doubleMellin (twoPairValue g h σ τ L R ν d e) χ ψ =
      (pairSpectrum g χ ((σ:ZMod p)*d)*(leftPairTwist L R ν χ ψ) d)*
      (pairSpectrum h ψ ((τ:ZMod p)*e)*(rightPairTwist L R ν χ ψ) e) := by
  by_cases hd : d=0
  · subst d
    simp [twoPairValue,doubleMellin,mellin,MulChar.map_zero]
  by_cases he : e=0
  · subst e
    simp [twoPairValue,doubleMellin,mellin,MulChar.map_zero]
  let D : (ZMod p)ˣ := Units.mk0 d hd
  let E : (ZMod p)ˣ := Units.mk0 e he
  have hl : ((L.unitMultiplier D E:(ZMod p)ˣ):ZMod p)=L.multiplier d e := L.coe_unitMultiplier D E
  have hr : ((R.unitMultiplier E D:(ZMod p)ˣ):ZMod p)=R.multiplier e d := R.coe_unitMultiplier E D
  unfold twoPairValue
  rw [doubleMellin_product,← hl,← hr,
    pairTest_mellin_mul g σ (L.unitMultiplier D E) χ d hd hg0,
    pairTest_mellin_mul h τ (R.unitMultiplier E D) ψ e he hh0]
  have honeD : (1:MulChar (ZMod p) ℂ) d=1 := MulChar.one_apply (isUnit_iff_ne_zero.mpr hd)
  have honeE : (1:MulChar (ZMod p) ℂ) e=1 := MulChar.one_apply (isUnit_iff_ne_zero.mpr he)
  cases L <;> cases R <;>
    simp only [PairMode.unitMultiplier,leftPairTwist,rightPairTwist,MulChar.mul_apply,
      MulChar.inv_apply',Units.val_inv_eq_inv_val,D,E,Units.val_mk0,honeD,honeE] <;> ring

end
end Ostmann.FiniteField

end OAI
