import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.PowerSeriesSplit
import OAI.Combinatorics.Chromatic.GradedAlgebra.HNSeries

namespace OAI

section
namespace ElementaryPositivity.WallUnits.LaurentRay
noncomputable section
def vUnit : (LaurentSeries ℚ)ˣ := Units.map atInfinity.toMonoidHom PositiveRay.vUnit
lemma vUnit_zpow (k : ℤ) : (↑(vUnit^k) : LaurentSeries ℚ)=HahnSeries.single (-k) 1 := by
  rw [Units.val_zpow_eq_zpow_val]
  change (atInfinity (↑PositiveRay.vUnit))^k=_
  rw [← map_zpow₀]
  exact atInfinity_v_pow k
end
end ElementaryPositivity.WallUnits.LaurentRay

namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent QuantumTorus WeightedTorusSeries WallUnits
open PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0<c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]
variable (w : I → ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
variable (hΩ : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)

include hΩ in
lemma hnSeries_convolution (θ : ℝ) :
    hnSeries a κ c η hc=convolution LaurentRay.vUnit Ω P
      (highSeries a κ c η hc θ) (lowSeries a κ c η hc θ) := by
  funext d
  rw [hnSeries_threshold a κ c η hc θ]
  apply Finset.sum_congr rfl
  intro s hs
  rw [LaurentRay.vUnit_zpow,hΩ]

include hΩ in
theorem hnTorus_factorization (θ : ℝ) :
    push w LaurentRay.vUnit Ω P (hnSeries a κ c η hc)=
      push w LaurentRay.vUnit Ω P (highSeries a κ c η hc θ)*
      push w LaurentRay.vUnit Ω P (lowSeries a κ c η hc θ) := by
  rw [hnSeries_convolution a κ c η hc Ω P hΩ θ,push_convolution]

variable (h : M →+ ℝ) (θ : ℝ) (hh : ∀d,h (P d)=slopeValue c η θ d)

include hΩ hh in
theorem hnTorus_canonical_factors :
    push w LaurentRay.vUnit Ω P (highSeries a κ c η hc θ)=
        PowerSeriesSplit.leftFactor (positiveProject LaurentRay.vUnit Ω h)
          (push w LaurentRay.vUnit Ω P (hnSeries a κ c η hc)) ∧
    push w LaurentRay.vUnit Ω P (lowSeries a κ c η hc θ)=
        PowerSeriesSplit.rightFactor (positiveProject LaurentRay.vUnit Ω h)
          (push w LaurentRay.vUnit Ω P (hnSeries a κ c η hc)) := by
  apply PowerSeriesSplit.uniqueness
  · exact push_constant w _ _ _ _ (highSeries_zero a κ c η hc θ)
  · exact push_constant w _ _ _ _ (lowSeries_zero a κ c η hc θ)
  · exact (hnTorus_factorization a κ c η hc w Ω P hΩ θ).symm
  · exact project_push_fixed w _ _ _ h _ (fun d hd=>by
      rw [hh]
      exact highSeries_support a κ c η hc θ d hd)
  · intro n
    exact project_push_killed w _ _ _ h _ (fun d hd=>by
      rw [hh]
      exact lowSeries_support a κ c η hc θ d hd) (n+1)

include hΩ hh in
theorem literalInput_canonical_factors (ε : I → Bool) (ha : ∀i,a i i=elementaryDiagonal ε i) :
    push w LaurentRay.vUnit Ω P (highSeries a κ c η hc θ)=
        PowerSeriesSplit.leftFactor (positiveProject LaurentRay.vUnit Ω h)
          (push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε)) ∧
    push w LaurentRay.vUnit Ω P (lowSeries a κ c η hc θ)=
        PowerSeriesSplit.rightFactor (positiveProject LaurentRay.vUnit Ω h)
          (push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε)) := by
  have he : literalInputCoefficient a κ ε=hnSeries a κ c η hc :=
    funext (literalInput_hnSeries a κ c η hc ε ha)
  rw [he]
  exact hnTorus_canonical_factors a κ c η hc w Ω P hΩ h θ hh

end
end ElementaryPositivity.RawShuffle

end

end OAI
