import OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedLocalLattice
import OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialPole

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.WeightedMonomialLattice

open CurveLocalOrder WeightedLocalLattice WeightedPolynomialPole WeightedMonomialPole

theorem exists_weighted_generator
    {A K ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Fintype ι] [DecidableEq ι]
    (x : ι → K) (w : ι → ℚ) (hw : ∀ i, 0 < w i) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ i, w i * (powers i : ℚ) = R)
    (M : Finset (ι → ℕ)) (hzero : 0 ∈ M)
    (hpure : ∀ i, Pi.single i (powers i) ∈ M)
    (hbudget : ∀ a ∈ M, (∑ i, w i * (a i : ℚ)) ≤ R) :
    ∃ a ∈ M, (∏ i, x i ^ a i) ≠ 0 ∧
      (coordinateOrder (fractionAddValuation A K) (∏ i, x i ^ a i) : ℚ) =
        -R * coordinatePole (fractionAddValuation A K) x w ∧
      generatedLattice A (fun b => ∏ i, x i ^ b i) M =
        Submodule.span A {∏ i, x i ^ a i} ∧
      Nonempty (A ≃ₗ[A] generatedLattice A (fun b => ∏ i, x i ^ b i) M) := by
  obtain ⟨a,ha,han,hao,hmin⟩ := exists_minimizing_monomial
    (fractionAddValuation A K) x w hw hR powers hpowers M hzero hpure hbudget
  exact ⟨a,ha,han,hao,
    generatedLattice_eq_span_of_minimum _ M a ha han hmin,
    generatedLattice_rank_one_of_minimum _ M a ha han hmin⟩

end PiExponent.WeightedMonomialLattice

end

end OAI
