import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedUnitCube

namespace OAI

/-! The actual ramified cube step with its three low rows retained.
Their residues must be determined; this identity does not assume that they
vanish or that the full residue is cube-periodic. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaRamifiedLowDirichlet (s : ℂ) (h : Eisenstein) : ℂ :=
  ∑' e : Eisensteinˣ, ∑ n ∈ Finset.range 3, ∑' a : CubicThetaPrimaryPart,
    cubicThetaRamifiedTerm s (lambdaE^3*h) (e,n,a)

theorem cubicThetaFrequencyDirichlet_ramified_cube {s : ℂ} (hs : 2<s.re)
    (h : Eisenstein) :
    cubicThetaFrequencyDirichlet (lambdaE^3*h) s=
      cubicThetaRamifiedLowDirichlet s h+
        (27*(27:ℂ)^(-s))*cubicThetaFrequencyDirichlet h s := by
  let : Finite Eisensteinˣ := Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; norm_num)
  have hf := cubicThetaRamifiedTerm_summable hs (lambdaE^3*h)
  have hrow (e : Eisensteinˣ) :
      (∑' n : ℕ, ∑' a : CubicThetaPrimaryPart,
        cubicThetaRamifiedTerm s (lambdaE^3*h) (e,n,a))=
      (∑ n ∈ Finset.range 3, ∑' a : CubicThetaPrimaryPart,
        cubicThetaRamifiedTerm s (lambdaE^3*h) (e,n,a))+
      (27*(27:ℂ)^(-s))*(∑' n : ℕ, ∑' a : CubicThetaPrimaryPart,
        cubicThetaRamifiedTerm s h (e,n,a)) := by
    rw [← (hf.prod_factor e).prod.sum_add_tsum_nat_add 3]
    simp_rw [cubicThetaRamifiedTerm_cube]
    simp_rw [tsum_mul_left]
  rw [cubicThetaFrequencyDirichlet_ramified_iterated hs,
    cubicThetaFrequencyDirichlet_ramified_iterated hs]
  simp_rw [hrow]
  rw [Summable.tsum_add Summable.of_finite Summable.of_finite,tsum_mul_left]
  rfl

theorem cubicThetaRamifiedLowDirichlet_primary (s : ℂ) (h : Eisenstein) :
    cubicThetaRamifiedLowDirichlet s h=
      ∑' e : Eisensteinˣ, ∑ n ∈ Finset.range 3,
        cubicThetaRamifiedFactor e n s (lambdaE^3*h)*
          cubicThetaPrimaryFourierSeries e n s h := by
  unfold cubicThetaRamifiedLowDirichlet
  apply tsum_congr
  intro e
  apply Finset.sum_congr rfl
  intro n _
  simp_rw [cubicThetaRamifiedTerm_factor]
  rw [tsum_mul_left]
  change cubicThetaRamifiedFactor e n s (lambdaE^3*h)*
      cubicThetaPrimaryFourierSeries e n s (lambdaE^3*h)=_
  rw [cubicThetaPrimaryFourierSeries_lambda_cube]

end CubicFirstMoment

end

end OAI
