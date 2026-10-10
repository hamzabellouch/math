import OAI.Geometry.SurfaceImmersion.Geometry.FixedCompactCancellation

namespace OAI

/-! Relative phase margins supply the fixed compact noncritical region and
the explicit normal denominator needed by the actual cancellation theorem. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

theorem relative_phase_polynomial_cancellation
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K₀ : Compacts SmallModes.Base)
    {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) :
    ∃ (N : ℕ) (J S : ℕ → ℝ) (p : ℕ → ℕ) (A : ℕ → ℝ),
      (∀ m, 1 ≤ J m) ∧ (∀ m, 1 ≤ S m) ∧ (∀ m, 1 ≤ A m) ∧
      ∀ {G : JetPolynomial.Base → JetPolynomial.Space} (_hG : ContDiff ℝ ∞ G)
        (K : Compacts SmallModes.Base), (K : Set SmallModes.Base) ⊆ K₀ →
      ∀ D : ℝ, 1 ≤ D → (ε*b)⁻¹ ≤ D →
      (∀ x ∈ (K : Set SmallModes.Base),
        Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
      (∀ x ∈ (K : Set SmallModes.Base),
        b ≤ ‖RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x‖) →
      (∀ x ∈ (K : Set SmallModes.Base),
        ε*‖RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x‖ ≤
          ‖secondQuadratic (RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
            (-(phaseDerivative (coordinatePhase φ) x).2,
              (phaseDerivative (coordinatePhase φ) x).1)‖) →
      (∀ x ∈ (K : Set SmallModes.Base),
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ D) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) →
      (∀ m j, j ≤ m+3 → WeightedBound univ 1 j
        (B m/(s : ℝ)^(j-2)) (G ∘ planeCoordinateIsometry.symm)) →
      ∀ q : ℕ, ∀ f : SupportedField (F := ComplexTensor) K,
      ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
        (∀ m, WeightedBound univ τ m
          ((N : ℝ)*splitSizeBudget q m
            (fun r => A r*(fixedChartSolverBudget J B D r)^(p r))
            (fixedChartSolverBudget J B D) J S * supportedWeightedSeminorm K s
              (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f) X) ∧
        (∀ m, WeightedBound univ τ m
          ((τ/s)^(q+1)*(N : ℝ)*splitResidualBudget q m
            (fun r => A r*(fixedChartSolverBudget J B D r)^(p r))
            (fixedChartSolverBudget J B D) J S * supportedWeightedSeminorm K s
              (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f)
          (RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
            QuadraticMean.displacement τ (coordinatePhase φ) f)) := by
  have hφ' := hφ.comp planeCoordinateIsometry.symm.contDiff
  obtain ⟨N,J,S,p,A,hJ,hS,hA,hcancel⟩ := fixed_compact_polynomial_cancellation hφ
    (phaseMarginCompact hφ' K₀ ε)
    (fun x hx => phaseMarginCompact_noncritical hφ' K₀ hε hx)
  refine ⟨N,J,S,p,A,hJ,hS,hA,?_⟩
  intro G hG K hK D hD hDB hImm hB hrel hgram τ s hτ hs hτs hs1 B hBP hFj q f
  have hn (x : SmallModes.Base) (hx : x ∈ (K : Set SmallModes.Base)) :
      RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x ≠ 0 :=
    norm_pos_iff.mp (hb.trans_le (hB x hx))
  have hKK : (K : Set SmallModes.Base) ⊆ phaseMarginCompact hφ' K₀ ε := by
    intro x hx
    exact mem_phaseMarginCompact_of_relative_margin hφ' K₀ (hK hx) _ (hn x hx) (hrel x hx)
  have hgood (x : SmallModes.Base) (hx : x ∈ (K : Set SmallModes.Base)) :
      Good (RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
        (phaseDerivative (coordinatePhase φ) x) :=
    good_of_direction_length_pos _ _ ((mul_pos hε (hb.trans_le (hB x hx))).trans_le (hrel x hx))
  have hnormal (x : SmallModes.Base) (hx : x ∈ (K : Set SmallModes.Base)) :
      ‖secondQuadratic (RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
        (-(phaseDerivative (coordinatePhase φ) x).2,
          (phaseDerivative (coordinatePhase φ) x).1)‖⁻¹ ≤ D :=
    (reciprocal_second_length_bound _ _ hε hb (hB x hx) (hrel x hx)).trans hDB
  exact hcancel hG K hKK D hD hImm hgood hgram hnormal τ s hτ hs hτs hs1 B hBP hFj q f

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
