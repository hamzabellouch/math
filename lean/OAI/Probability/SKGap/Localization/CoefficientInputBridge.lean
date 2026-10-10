import Mathlib
import OAI.Probability.SKGap.Stability.OrdinaryClosure
import OAI.Probability.SKGap.Localization.RecipeCoefficientClosure

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Noncrossing.Primary
variable {n : ℕ} {ι κ σ τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ] [Fintype τ]

namespace LocalConstants
def withCoefficient (c : LocalConstants) (K S : ℝ) (hK : 1≤K) (hS : 0≤S) : LocalConstants :=
  {c with A:=K,C:=K,S:=S,one_le_A:=hK,C_nonneg:=le_trans (by norm_num) hK,C_le_A:=le_rfl,S_nonneg:=hS}
end LocalConstants

theorem LocalOrdinaryInput.with_coefficients {D : OrdinaryData n ι κ σ} {N : ℕ}
    {T : ι→SourceTree (Fin n→ℝ)} {x : Spin n} {c : LocalConstants}
    (h : LocalOrdinaryInput D T x N c) (E : OrdinaryData n ι κ τ)
    (hJ : E.J=D.J) (hj : E.j=D.j) (hH : E.H=D.H) (hp : E.predecessor=D.predecessor) (hθ : E.θ=D.θ)
    (A : ℕ) (K S : ℝ) (hK : 1≤K) (hS : 0≤S)
    (hs : (∑s,vectorNorm (E.seed s))≤S) (hc : E.CoefficientClass A x K) :
    LocalOrdinaryInput E T x A (c.withCoefficient K S hK hS) := by
  refine ⟨h.dimension,?_,?_,?_,?_,?_,?_,hs,?_,hc.seedRegular,hc.auxRegular,?_,?_⟩
  · simpa only [hJ,LocalConstants.withCoefficient] using h.interaction
  · simpa only [hH,LocalConstants.withCoefficient] using h.primaryShape
  · simpa only [hH,hj,hJ,LocalConstants.withCoefficient] using h.primaryFieldError
  · simpa only [hp,hj,hJ,LocalConstants.withCoefficient] using h.primarySourceError
  · simpa only [hp] using h.primaryValue
  · simpa only [hp,LocalConstants.withCoefficient] using h.primaryDerivative
  · simpa only [hθ,LocalConstants.withCoefficient] using h.parameter
  · intro a ha s i; exact (hc.seedValue a ha s).at i
  · intro a ha b i; exact (hc.auxValue a ha b).at i

end SKGapCutoff.Recipe

end
end

end OAI
