import OAI.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)

variable {X : Type*} [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
variable (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
variable (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m,
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
variable (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
variable (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
variable (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
variable (hSP : (S.value : ℝ) ≤ Real.exp P)
variable (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
variable (width : Option (LayerSamplerVariables G I n B) × X → ℝ)
variable (hwidth : ∀ z, 0 < width z)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
variable {Eforecast : ℝ}
variable (hnormalizerCenter : ∀ center,
  let Z := selectedJointDensityMass bases stride cells width
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)
  |Z - 1| ≤ Real.exp (-Eforecast) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
    0 < Z ∧ Z⁻¹ ≤ 2)

include hC hV hσ1 hCinv hchart hsmall hP hm hK hRP hσP hcount hI hn hJ hAP hSP hCP hVP in

theorem allocatedCenteredJointReference_retained_mass
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (F : Finset (bases × rectangularWeightIndices 0 width 1)) {ρ : ℝ}
    (hF : ρ < (selectedJointFiniteLaw bases hbases stride cells width hwidth hmass
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center)
      (hnormalizerCenter center).2.2.1).mass F) :
    ρ / (2 * Real.exp (allocatedFourierLogBudget m P)) <
      (selectedJointReference bases hbases stride cells width hwidth hmass).mass F := by
  apply selectedJointReference_retained_mass bases hbases stride cells width hwidth hmass
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center)
    (hnormalizerCenter center).2.2.1 (Real.exp_pos _) (hnormalizerCenter center).2.1.1 _ F hF
  intro z
  exact allocatedCenteredJointDensity_fixedScale_le_exp B U b hb o hR hσ S C V
    hC hV hσ1 Cinv hCinv hchart hsmall poly hmem center z.1.val z.2.val
    hP hm hK hRP hσP hcount hI hn hJ hAP hSP hCP hVP

include hC hV hσ1 hCinv hchart hsmall hP hm hK hRP hσP hcount hI hn hJ hAP hSP hCP hVP in

theorem allocatedCenteredJointReference_retained_exp_mass
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (F : Finset (bases × rectangularWeightIndices 0 width 1)) {Q : ℝ}
    (hF : Real.exp (-Q) < (selectedJointFiniteLaw bases hbases stride cells width hwidth hmass
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center)
      (hnormalizerCenter center).2.2.1).mass F) :
    Real.exp (-(Q + allocatedFourierLogBudget m P + 1)) <
      (selectedJointReference bases hbases stride cells width hwidth hmass).mass F := by
  apply selectedJointReference_retained_exp_mass bases hbases stride cells width hwidth hmass
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center)
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center)
    (hnormalizerCenter center).2.2.1 (hnormalizerCenter center).2.1.1 _ F hF
  intro z
  exact allocatedCenteredJointDensity_fixedScale_le_exp B U b hb o hR hσ S C V
    hC hV hσ1 Cinv hCinv hchart hsmall poly hmem center z.1.val z.2.val
    hP hm hK hRP hσP hcount hI hn hJ hAP hSP hCP hVP

end Erdos3.VectorPolynomial

end

end OAI
