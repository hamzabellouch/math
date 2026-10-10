import OAI.NumberTheory.Ostmann.Tree.PairSecondMoment

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

def twoPairBare (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ) (L R : PairMode)
    (d e : ZMod p) (lam mu : (ZMod p)ˣ) : ℂ :=
  pairTest g σ d ((lam:ZMod p)*L.multiplier d e)*
    pairTest h τ e ((mu:ZMod p)*R.multiplier e d)

theorem twoPairBare_zero_left (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ) (L R : PairMode)
    (e : ZMod p) (lam mu : (ZMod p)ˣ) (hg0 : g 0=0) :
    twoPairBare g h σ τ L R 0 e lam mu=0 := by simp [twoPairBare,pairTest_zero g σ hg0]

theorem twoPairBare_zero_right (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ) (L R : PairMode)
    (d : ZMod p) (lam mu : (ZMod p)ˣ) (hh0 : h 0=0) :
    twoPairBare g h σ τ L R d 0 lam mu=0 := by simp [twoPairBare,pairTest_zero h τ hh0]

theorem twoPairBare_parameter_average (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (L R : PairMode) (d e : ZMod p) (hg0 : g 0=0) (hh0 : h 0=0) :
    (Fintype.card (ZMod p)ˣ:ℝ)⁻¹^2*
      (∑ lam : (ZMod p)ˣ,∑ mu : (ZMod p)ˣ,‖twoPairBare g h σ τ L R d e lam mu‖^2) =
      pairSecondMoment g σ d*pairSecondMoment h τ e := by
  by_cases hd : d=0
  · subst d
    simp [twoPairBare_zero_left g h σ τ L R _ _ _ hg0,pairSecondMoment_zero g σ hg0]
  by_cases he : e=0
  · subst e
    simp [twoPairBare_zero_right g h σ τ L R _ _ _ hh0,pairSecondMoment_zero h τ hh0]
  let D : (ZMod p)ˣ := Units.mk0 d hd
  let E : (ZMod p)ˣ := Units.mk0 e he
  have hl : ((L.unitMultiplier D E:(ZMod p)ˣ):ZMod p)=L.multiplier d e := L.coe_unitMultiplier D E
  have hr : ((R.unitMultiplier E D:(ZMod p)ˣ):ZMod p)=R.multiplier e d := R.coe_unitMultiplier E D
  simp only [twoPairBare,norm_mul,mul_pow]
  calc
    _ = ((Fintype.card (ZMod p)ˣ:ℝ)⁻¹*∑ lam : (ZMod p)ˣ,
          ‖pairTest g σ d ((lam:ZMod p)*L.multiplier d e)‖^2)*
        ((Fintype.card (ZMod p)ˣ:ℝ)⁻¹*∑ mu : (ZMod p)ˣ,
          ‖pairTest h τ e ((mu:ZMod p)*R.multiplier e d)‖^2) := by
      simp only [← Finset.mul_sum,← Finset.sum_mul]
      ring
    _ = _ := by rw [← hl,← hr,pairSecondMoment_parameter_average,pairSecondMoment_parameter_average]

end
end Ostmann.FiniteField

end OAI
