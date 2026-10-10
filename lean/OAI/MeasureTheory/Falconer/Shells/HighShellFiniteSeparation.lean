import OAI.MeasureTheory.Falconer.Shells.HighShellSeparatedTerms

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

 theorem normalizedHighShellF_finite_separation (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (n : ℕ) (v r : ℝ) :
    d.normalizedHighShellF n v r =
      (((r*(2:ℝ)^(-(d.a:ℝ)))^(1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1),
        ((((r/(2:ℝ)^v)⁻¹)^j:ℝ):ℂ) *
          ((inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)).map (fun b =>
            d.absorbedInverseCoefficient j v b *
              ∫ ξ, spatialFourierCoeff 96 2004 (by norm_num) (by norm_num) j ξ *
                sourceParentDistanceF (d.Q.descendant d.X) (d.Q.descendant d.Y)
                  d.ρ d.ρ d.levelMass d.levelMass
                  (spatialPhasedSymbol ((2:ℝ)^(-(d.a:ℝ))) ξ (d.inverseEndpointSymbol b.2 0))
                  (spatialPhasedSymbol ((2:ℝ)^(-(d.a:ℝ))) ξ (d.inverseEndpointSymbol b.2 1)) r)).sum := by
  let L := fun j => inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)
  let R := fun j => ((((r/(2:ℝ)^v)⁻¹)^j:ℝ):ℂ)
  let A := (((r*(2:ℝ)^(-(d.a:ℝ)))^(1/2:ℝ):ℝ):ℂ)
  let K := fun j (b : ℂ × (PairMaskIndex → ℕ)) => d.inverseDistanceEndpointKernel j b.2 r
  let c := fun j b => d.absorbedInverseCoefficient j v b
  have hi (j : ℕ) (b : ℂ × (PairMaskIndex → ℕ)) (hb : b ∈ L j) :
      Integrable (fun z => c j b * K j b z) d.cellPair :=
    (d.inverseDistanceEndpointKernel_integrable hQ hs j hb r).const_mul (c j b)
  have hiJ (j : ℕ) : Integrable (fun z => R j * ((L j).map (fun b => c j b * K j b z)).sum) d.cellPair :=
    (integrable_list_sum d.cellPair (L j) (fun b z => c j b * K j b z) (hi j)).const_mul (R j)
  have heJ (j : ℕ) :
      (∫ z, R j * ((L j).map (fun b => c j b * K j b z)).sum ∂d.cellPair) =
        R j * ((L j).map (fun b => c j b * ∫ z, K j b z ∂d.cellPair)).sum := by
    rw [integral_const_mul, integral_list_sum d.cellPair (L j) _ (hi j)]
    simp_rw [integral_const_mul]
  change (d.levelMass^(-2:ℤ):ℝ) • (∫ z, A * ∑ j ∈ Finset.range (n+1),
    R j * ((L j).map (fun b => c j b * K j b z)).sum ∂d.cellPair) = _
  rw [integral_const_mul,integral_finsetSum (Finset.range (n+1)) (fun j _ => hiJ j)]
  simp_rw [heJ]
  calc
    _ = A * ∑ j ∈ Finset.range (n+1), R j * ((L j).map (fun b => c j b *
        ((d.levelMass^(-2:ℤ):ℝ) • ∫ z, K j b z ∂d.cellPair))).sum := by
      simp only [Complex.real_smul, Finset.mul_sum, ← List.sum_map_mul_left]
      apply Finset.sum_congr rfl
      intro j hj
      apply congrArg List.sum
      apply List.map_congr_left
      intro b hb
      ring
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro b hb
      rw [show (d.levelMass^(-2:ℤ):ℝ) • (∫ z, K j b z ∂d.cellPair) = _ from
        d.inverseDistanceEndpointKernel_form hQ hs j hb r]

end PositiveDistanceData

end PlanarFalconer

end OAI
