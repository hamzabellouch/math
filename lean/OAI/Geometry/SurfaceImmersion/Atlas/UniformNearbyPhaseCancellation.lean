import OAI.Geometry.SurfaceImmersion.Atlas.UniformCompactPhaseFamily
import OAI.Geometry.SurfaceImmersion.Primitive.ProfiledSplitCancellation

namespace OAI

/-! Compact good-phase cancellation uniform over nearby maps and slow scales. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

theorem uniform_nearby_good_phase_cancellation_all_profiles
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Compacts SmallModes.Base)
    (hImm : ∀ p ∈ (K : Set SmallModes.Base),
      Function.Injective (fderiv ℝ (F ∘ planeCoordinateIsometry.symm) p))
    (hgood : ∀ p ∈ (K : Set SmallModes.Base),
      Good (RealModes.realSecondTensor (F ∘ planeCoordinateIsometry.symm) p)
        (phaseDerivative (coordinatePhase φ) p))
    : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (R : ℕ → ℝ), (∀ m, 0 ≤ R m) → ∀ q : ℕ,
    ∃ Cv Ct : ℕ → ℝ,
      (∀ m, 0 ≤ Cv m) ∧ (∀ m, 0 ≤ Ct m) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (_hG : ContDiff ℝ ∞ G)
        (B : ℝ), 0 ≤ B → B < ρ →
      WeightedBound univ 1 2 B
        ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m j, j ≤ m+2 → WeightedBound univ 1 j (R m/(s:ℝ)^(j-2))
        (G ∘ planeCoordinateIsometry.symm)) →
      ∀ A : SupportedField (F := ComplexTensor) K,
      ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
        (∀ m, WeightedBound univ τ m
          (Cv m * supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A) X) ∧
        (∀ m, WeightedBound univ τ m
          ((τ/s)^(q+1) * Ct m * supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A)
          (RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
            QuadraticMean.displacement τ (coordinatePhase φ) A)) := by
  classical
  obtain ⟨a⟩ := exists_compactPhaseFamily hF hφ K hImm hgood
  obtain ⟨ρ,hρ,hall⟩ := a.uniform_solvers_all_profiles hF hφ
  refine ⟨ρ,hρ,?_⟩
  intro R hR q
  obtain ⟨C,J,I,hC,hJ,hI,hi,hsol⟩ := hall R hR
  obtain ⟨Cv,Ct,hCv,hCt,hcancel⟩ := profiled_split_cancellation emptyMetricPolynomial K
    a.support a.split a.support_subset C J I hC hJ hI a.partition.splitConstant
    a.partition.one_le_splitConstant a.split_bound a.split_sum q
  refine ⟨Cv,Ct,hCv,hCt,?_⟩
  intro G hG B hB hBρ hb τ s hτ hs hτs hs1 hp A
  obtain ⟨c,he,hc,hd,hj⟩ := hsol G hG B hB hBρ hb τ s hs hs1 hp
  apply hcancel G hG φ τ s hτ hs hτs hs1 c hc _ hj _ A
  · intro i
    funext m
    exact hd i m
  · intro i m j hj₁ hjm x hx
    rw [he i] at hx ⊢
    exact hi i m j hj₁ hjm x hx

theorem uniform_nearby_good_phase_cancellation
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : Compacts SmallModes.Base)
    (hImm : ∀ p ∈ (K : Set SmallModes.Base),
      Function.Injective (fderiv ℝ (F ∘ planeCoordinateIsometry.symm) p))
    (hgood : ∀ p ∈ (K : Set SmallModes.Base),
      Good (RealModes.realSecondTensor (F ∘ planeCoordinateIsometry.symm) p)
        (phaseDerivative (coordinatePhase φ) p))
    (R : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) (q : ℕ) :
    ∃ (ρ : ℝ) (Cv Ct : ℕ → ℝ), 0 < ρ ∧
      (∀ m, 0 ≤ Cv m) ∧ (∀ m, 0 ≤ Ct m) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (_hG : ContDiff ℝ ∞ G)
        (B : ℝ), 0 ≤ B → B < ρ →
      WeightedBound univ 1 2 B
        ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m j, j ≤ m+2 → WeightedBound univ 1 j (R m/(s:ℝ)^(j-2))
        (G ∘ planeCoordinateIsometry.symm)) →
      ∀ A : SupportedField (F := ComplexTensor) K,
      ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
        (∀ m, WeightedBound univ τ m
          (Cv m * supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A) X) ∧
        (∀ m, WeightedBound univ τ m
          ((τ/s)^(q+1) * Ct m * supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A)
          (RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
            QuadraticMean.displacement τ (coordinatePhase φ) A)) := by
  obtain ⟨ρ,hρ,hall⟩ := uniform_nearby_good_phase_cancellation_all_profiles hF hφ K hImm hgood
  obtain ⟨Cv,Ct,hCv,hCt,hcancel⟩ := hall R hR q
  exact ⟨ρ,Cv,Ct,hρ,hCv,hCt,hcancel⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
