import OAI.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

theorem allocatedCenteredJointDensity_normalizer_of_subtractConstant
    (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (widths : Option (LayerSamplerVariables G I n B) × X → ℝ)
    (bases : Finset (X → ℤ))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (E : ℝ)
    (hshift :
      let Z : ℝ := selectedJointDensityMass bases stride cells widths
        (allocatedJointBaseDensity B U b hb o hR hσ S X
          (fun j => subtractConstant (c j).val (poly j))
          (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j)));
      |Z - 1| ≤ Real.exp (-E) ∧ Z ∈ Set.Icc (1/2) (3/2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2) :
    let Z : ℝ := selectedJointDensityMass bases stride cells widths
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center);
    |Z - 1| ≤ Real.exp (-E) ∧ Z ∈ Set.Icc (1/2) (3/2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2 := by
  simpa only [allocatedJointBaseDensity_subtractConstant_centered
    B U b hb o hR hσ S poly hmem center c hc] using hshift

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (N : X → ℕ) (hN : ∀ i, 0 < N i)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

omit [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
  [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
theorem allocatedCenteredJointFiniteLaw_site_excess_of_subtractConstant
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))))
    (htotal : 0 < selectedJointDensityMass bases stride cells widths
      (allocatedJointBaseDensity B U b hb o hR hσ S X
        (fun j => subtractConstant (c j).val (poly j))
        (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))))
    (hcenter : 0 < selectedJointDensityMass bases stride cells widths
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center))
    {Sites Y : Type*} [Fintype Sites] [Nonempty Sites] [Fintype Y]
    (physical : (bases × rectangularWeightIndices 0 widths 1) → Sites → Y)
    (reference : FiniteProbabilityWeights Y) (cap ε : ℝ)
    (hexcess : reference.excessMass
      ((allocatedOriginalPathLaw B U b hb o hR hσ S X
        (fun j => subtractConstant (c j).val (poly j))
        (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))
        N hN hW hτ hξ stride cells hmass bases hbases htotal).siteLaw physical) cap ≤ ε) :
    reference.excessMass
      ((selectedJointFiniteLaw bases hbases stride cells widths
        (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass
        (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)
        (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center)
        hcenter).siteLaw physical) cap ≤ ε := by
  rw [← allocatedOriginalPathLaw_subtractConstant_eq_centered
    B U b hb o hR hσ S poly hmem N hN hW hτ hξ stride cells hmass bases hbases
    center c hc htotal hcenter]
  exact hexcess

end Erdos3.VectorPolynomial

end

end OAI
