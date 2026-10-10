import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidatePhysicalScore
import OAI.Combinatorics.Progressions.Sampling.FrozenMarkedRightOrbitGrid

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

theorem exists_frozenMarkedPhysical_bounds
    {κ : Type*} [Fintype κ] [DecidableEq κ] (cF : Basis κ ℚ M)
    (sectionMap : M →ₗ[ℚ] L)
    (hSection : ∀ j, ∀ y ∈ Fmark.layer j, sectionMap y ∈ D.filtration.layer j) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ (H HS : ℕ) (p : ℝ), 0 ≤ p →
        (Fintype.card (Fin d) : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
        (H : ℝ) ≤ Real.exp p → (HS : ℝ) ≤ Real.exp p →
        (∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H) →
        (∀ i j, RationalHeightLE (LinearMap.toMatrix cF D.basis sectionMap i j) HS) →
        ∀ q r : ℕ, 0 < q → 0 < r →
          ((matrixDenominator (LinearMap.toMatrix cF D.basis sectionMap) * q * r : ℕ) : ℝ) ≤
            Real.exp p →
          ∃ mFull : ℕ, 0 < mFull ∧ (mFull : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            matrixDenominator (LinearMap.toMatrix cF D.basis sectionMap) * q * r ∣ mFull ∧
            ∀ leftMark rightMark : Fmark.realification.PolynomialOrbit
                (fullTaggedVariableWeight (X := X) J),
              (∀ x ∈ integerBox N, ∀ i, |(cF.baseChange ℝ).repr
                (Fmark.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
                  (P.physicalIntegerPoint x) leftMark).coord i| ≤ Real.exp p) →
              CoefficientGrid (cF.baseChange ℝ) q rightMark.log →
              ∀ leftCenter rightCenter : D.filtration.realification.Group,
                (∀ i, |(D.basis.baseChange ℝ).repr leftCenter.coord i| ≤ Real.exp p) →
                (D.basis.baseChange ℝ).equivFun rightCenter.coord ∈ realDenominatorGrid r →
                (∀ x ∈ integerBox N, ∀ i, |(D.basis.baseChange ℝ).repr
                  (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
                    (P.physicalIntegerPoint x)
                    (D.filtration.frozenMarkedLeftOrbit Fmark (fullTaggedVariableWeight J)
                      sectionMap hSection leftMark leftCenter)).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
                (∀ x ∈ integerBox N, (D.basis.baseChange ℝ).equivFun
                  (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
                    (P.physicalIntegerPoint x)
                    (D.filtration.frozenMarkedRightOrbit Fmark (fullTaggedVariableWeight J)
                      sectionMap hSection rightMark rightCenter)).coord ∈ realDenominatorGrid mFull) := by
  obtain ⟨CL, hCL, hleft⟩ := exists_frozenMarkedLeftOrbit_exp_bound s
  obtain ⟨CR, hCR, hright⟩ := exists_frozenMarkedRightOrbit_grid_bound s
  let C := max CL CR
  have hLC : CL ≤ C := le_max_left _ _
  have hRC : CR ≤ C := le_max_right _ _
  refine ⟨C, hCL.trans hLC, ?_⟩
  intro H HS p hp hdim hdimF hH hHS hlie hsection q r hq hr hqr
  have hgrow (a : ℕ) (ha : 2 ≤ a) (haC : a ≤ C) :
      Real.exp ((p + a) ^ a) ≤ Real.exp ((p + C) ^ C) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ (p + C) ^ a := pow_le_pow_left₀ (by positivity : 0 ≤ p + (a : ℝ))
        (add_le_add le_rfl (Nat.cast_le.mpr haC)) a
      _ ≤ _ := pow_le_pow_right₀ (by
        have hC : (2 : ℝ) ≤ C := Nat.cast_le.mpr (ha.trans haC)
        linarith) haC
  obtain ⟨mFull, hm, hmp, hdiv, hgrid⟩ :=
    hright D.filtration Fmark D.basis cF (fullTaggedVariableWeight (X := X) J)
      sectionMap hSection H p hp hdim hH hlie q r hq hr hqr
  refine ⟨mFull, hm, hmp.trans (hgrow CR hCR hRC), hdiv, ?_⟩
  intro leftMark rightMark hleftMark hrightMark leftCenter rightCenter hleftCenter hrightCenter
  constructor
  · intro x hx i
    exact (hleft D.filtration Fmark D.basis cF (fullTaggedVariableWeight J)
      sectionMap hSection H HS p hp hdim hdimF hH hHS hlie hsection
      leftMark leftCenter (P.physicalIntegerPoint x) (hleftMark x hx) hleftCenter i).trans
        (hgrow CL hCL hLC)
  · intro x _
    exact hgrid rightMark hrightMark rightCenter hrightCenter (P.physicalIntegerPoint x)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
