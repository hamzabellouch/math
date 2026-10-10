import OAI.NumberTheory.Ostmann.Tree.QuartetMobiusMellin
import OAI.NumberTheory.Ostmann.Tree.TwoPairConvolution

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

def twoPairRatioValue (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (lam mu y r : (ZMod p)ˣ) : ℂ :=
  let d := pairMobiusValue y r
  let e := d-(y:ZMod p)
  pairTest g σ d ((lam:ZMod p)*L.multiplier d e) *
    pairTest h τ e ((mu:ZMod p)*R.multiplier e d)

theorem twoPairRatio_mellin (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (lam mu y : (ZMod p)ˣ) (χ : MulChar (ZMod p) ℂ)
    (hg0 : g 0=0) :
    mellin (twoPairRatioValue g h σ τ L R lam mu y) χ =
      ((p:ℂ)/(Fintype.card (ZMod p)ˣ:ℂ)) *
        twoPairConvolution g h σ τ L R χ⁻¹ lam mu y := by
  let H : ZMod p → ℂ := fun d =>
    pairTest g σ d ((lam:ZMod p)*L.multiplier d (d-(y:ZMod p))) *
      pairTest h τ (d-(y:ZMod p)) ((mu:ZMod p)*R.multiplier (d-(y:ZMod p)) d)
  have hH0 : H 0=0 := by
    simp [H,pairTest,pairFirst,pairSecond,hg0]
  have hm := mellin_mobius_pullback H y χ hH0
  change mellin (twoPairRatioValue g h σ τ L R lam mu y) χ =
    (Fintype.card (ZMod p)ˣ:ℂ)⁻¹ * ∑ d : ZMod p, H d*(χ⁻¹ d*χ (d-(y:ZMod p))) at hm
  rw [hm]
  have hp0 : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out : p.Prime))
  have hN0 : (Fintype.card (ZMod p)ˣ:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [twoPairConvolution, mean, twoPairValue, inv_inv]
  change (Fintype.card (ZMod p)ˣ:ℂ)⁻¹ * ∑ d : ZMod p, H d*(χ⁻¹ d*χ (d-(y:ZMod p))) =
    ((p:ℂ)/(Fintype.card (ZMod p)ˣ:ℂ)) *
      ((p:ℂ)⁻¹ * ∑ d : ZMod p, H d*(χ⁻¹ d*χ (d-(y:ZMod p))))
  field_simp

end
end Ostmann.FiniteField

end OAI
