import OAI.Geometry.SurfaceImmersion.Correction.UniformPolynomialCompactFamily
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialProfiledSplitCancellation

namespace OAI

/-! Actual polynomial cancellation on compact supports, uniform over nearby maps. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

theorem uniform_polynomial_nearby_cancellation_all_profiles {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs univ)
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Compacts SmallModes.Base)
    (hImm : ∀ x ∈ (K : Set SmallModes.Base),
      Function.Injective (fderiv ℝ (F ∘ planeCoordinateIsometry.symm) x))
    (hgood : ∀ x ∈ (K : Set SmallModes.Base),
      Good (RealModes.realSecondTensor (F ∘ planeCoordinateIsometry.symm) x)
        (phaseDerivative (coordinatePhase φ) x))
    {U : Set JetPolynomial.Base} (hU : IsOpen U) (KU : Compacts JetPolynomial.Base)
    (hUK : U ⊆ KU) (hKU : (jetSupport K : Set JetPolynomial.Base) ⊆ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : ℕ → ℝ, (∀ m, 0 ≤ R m) → ∀ q : ℕ,
    ∃ Cv Ct : ℕ → ℝ, (∀ m, 0 ≤ Cv m) ∧ (∀ m, 0 ≤ Ct m) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (_hG : ContDiff ℝ ∞ G) (B : ℝ),
      0 ≤ B → B < ρ → WeightedBound univ 1 2 B
        ((G ∘ planeCoordinateIsometry.symm)-(F ∘ planeCoordinateIsometry.symm)) →
      ∀ (τ ε : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → τ/s+ε/τ^tensorLoss P ≤ 1 →
      (∀ m j, j ≤ m+2 → WeightedBound univ 1 j (R m/(s:ℝ)^(j-2))
        (G ∘ planeCoordinateIsometry.symm)) →
      ∀ A : SupportedField (F := ComplexTensor) K,
      ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
        (∀ m, WeightedBound univ τ m (Cv m * supportedWeightedSeminorm K s
          (PolynomialSolveData.inputOrder (P := P) q m) A) X) ∧
        (∀ m, WeightedBound univ τ m ((τ/s+ε/τ^tensorLoss P)^(q+1)*Ct m *
          supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A)
          (coordinateFullLinearized P ε G X+QuadraticMean.displacement τ (coordinatePhase φ) A)) := by
  classical
  obtain ⟨a⟩ := exists_compactPhaseFamily hF hφ K hImm hgood
  obtain ⟨ρ,hρ,hall⟩ := a.uniform_polynomial_solvers_all_profiles P hP hF hφ hU KU hUK hKU
  refine ⟨ρ,hρ,?_⟩
  intro R hR q
  obtain ⟨C,D,J,I,hC,_,hJ,hI,hsol⟩ := hall R hR
  obtain ⟨Cv,Ct,hCv,hCt,hcancel⟩ := polynomial_profiled_split_cancellation P K
    a.support a.split a.support_subset C D J I hC hJ hI a.partition.splitConstant
    a.partition.one_le_splitConstant a.split_bound a.split_sum q
  refine ⟨Cv,Ct,hCv,hCt,?_⟩
  intro G hG B hB hBρ hb τ ε s hτ hs hτs hs1 hε hε1 hsmall hp A
  obtain ⟨c,hc,hd,hj,hi⟩ := hsol G hG B hB hBρ hb τ ε s hτ hs hτs hs1 hε hε1 hp
  exact hcancel G hG φ τ ε s hτ hs hτs hs1 hε hsmall c hc hd hj hi A

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
