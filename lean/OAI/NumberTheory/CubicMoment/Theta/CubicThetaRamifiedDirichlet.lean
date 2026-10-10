import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedDenominator
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDirichlet

namespace OAI

/-! Exact unit/ramified/primary separation of the actual Dirichlet series.
Reordering uses its already proved absolute convergence on Re(s)>2. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRamifiedTerm (s : ℂ) (h : Eisenstein)
    (v : Eisensteinˣ × ℕ × CubicThetaPrimaryPart) : ℂ :=
  cubicThetaDenominatorTerm s h (cubicThetaRamifiedDenominator v)

theorem cubicThetaFrequencyDirichlet_ramified (s : ℂ) (h : Eisenstein) :
    cubicThetaFrequencyDirichlet h s=
      ∑' v : Eisensteinˣ × ℕ × CubicThetaPrimaryPart, cubicThetaRamifiedTerm s h v := by
  rw [cubicThetaFrequencyDirichlet_denominators]
  exact (cubicThetaRamifiedDenominatorEquiv.tsum_eq (cubicThetaDenominatorTerm s h)).symm

lemma cubicThetaRamifiedTerm_summable {s : ℂ} (hs : 2<s.re) (h : Eisenstein) :
    Summable (cubicThetaRamifiedTerm s h) :=
  (cubicThetaDenominatorTerm_summable hs h).comp_injective
    cubicThetaRamifiedDenominatorEquiv.injective

theorem cubicThetaFrequencyDirichlet_ramified_iterated {s : ℂ} (hs : 2<s.re)
    (h : Eisenstein) :
    cubicThetaFrequencyDirichlet h s=
      ∑' u : Eisensteinˣ, ∑' n : ℕ, ∑' a : CubicThetaPrimaryPart,
        cubicThetaRamifiedTerm s h (u,n,a) := by
  rw [cubicThetaFrequencyDirichlet_ramified]
  have hf := cubicThetaRamifiedTerm_summable hs h
  rw [hf.tsum_prod]
  apply tsum_congr
  intro u
  exact (hf.prod_factor u).tsum_prod

end CubicFirstMoment

end

end OAI
