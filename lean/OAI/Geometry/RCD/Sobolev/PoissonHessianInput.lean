import OAI.Geometry.RCD.Sobolev.WeakRadialCancellation
import OAI.Geometry.RCD.Sobolev.ShiftedBochnerCutoff

namespace OAI

/-!
# The Hessian input for the finite Poisson span

Gigli (2018), equation (3.1.10) and Theorem 3.3.8, give the local Hessian
pairing and its Bochner bound. Han (2018), Proposition 3.2 and Theorem 3.3,
give the top-dimensional trace identity and the lower-dimensional trace
defect. Completing the trace-defect square and applying integral Cauchy--Schwarz gives
the displayed bound on the integrated pairing on every concentric inner
ball, using the same canonical measure. This localization is needed to
apply cutoff mass bounds before constructing the harmonic correction.
The tensor pairing is restricted to the finite harmonic and Poisson span.
-/

open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X]

/-- Local second-order calculus for n harmonic coordinates and two
constant-Laplacian replacements. The same full Bochner measure occurs in
the energy equation, the positivity assertion and the Hessian bound. -/
def LocalPoissonHessianInput {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → -κ ≤ K → ∀ (p : X) (r : ℝ), 0 < r →
    ∀ (L : ℝ≥0)
      (U : Euclidean (n + 2) →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
      (ell : Euclidean (n + 2) →ₗ[ℝ] ℝ),
      (∀ v, IsConstantLaplacianOn (hausdorff n X) hX.quadratic
        (ball p (8 * r)) (U v) (ell v)) →
      (∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * r)),
        localGamma (hausdorff n X) hX.quadratic (U v) (U v) x ≤
          (L : ℝ) ^ 2 * ‖v‖ ^ 2) →
      ∃ M : PositiveBilinearMeasure X (Euclidean (n + 2)),
        (∀ v, Nonempty (LocalHarmonicEnergy (hausdorff n X) hX.quadratic U M κ p r L v)) ∧
        ShiftedBochnerLowerBound M ((hausdorff n X).restrict (ball p (2 * r))) ell n ∧
        ∀ v w (t : ℝ), 0 < t → t ≤ 2 * r →
          ∃ G : LocalHessianPairing (hausdorff n X) hX.quadratic
            (ball p t) (U v) (U w),
          ∀ (b : ℝ) (φ : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p t)),
            (G.hessian φ - b * energyForm (hausdorff n X) hX.quadratic (U w) φ.val) ^ 2 ≤
              ((L : ℝ) ^ 2 * ‖w‖ ^ 2 *
                ((M.measure v).real (ball p t) -
                  (2 * b * ell v - (n : ℝ) * b ^ 2) * (hausdorff n X).real (ball p t))) *
              energyForm (hausdorff n X) hX.quadratic φ.val φ.val

omit [ProperSpace X] in
/-- The second-order specialization includes the earlier scalar
constant-Laplacian Bochner input. -/
theorem LocalPoissonHessianInput.constantLaplacianBochnerInput
    {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} (h : LocalPoissonHessianInput hX) :
    LocalConstantLaplacianBochnerInput hX := by
  intro κ hκ hK p r hr L U ell hU hgrad
  obtain ⟨M, hM, hshift, _⟩ := h κ hκ hK p r hr L U ell hU hgrad
  exact ⟨M, hM, hshift⟩

variable (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The exact shift correction is the full positive mass on the interior
set. This removes the raw Hessian bound from the harmonic-correction step. -/
theorem LocalHessianPairing.harmonic_correction_of_shifted_mass
    {Ω : Set X} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (μ.restrict Ω)]
    (U : E →L[ℝ] SobolevSpace μ hQ) (M : PositiveBilinearMeasure X E)
    (ell : E →ₗ[ℝ] ℝ) (n : ℝ) (hshift : ShiftedBochnerLowerBound M (μ.restrict Ω) ell n)
    (v w : E) (G : LocalHessianPairing μ hQ Ω (U v) (U w))
    (hf : IsConstantLaplacianOn μ hQ Ω (U v) (ell v))
    (ha : IsSobolevHarmonicOn μ hQ Ω (U w))
    (b L P : ℝ) (hP : 0 ≤ P)
    (hpoincare : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ φ.val‖ ^ 2 ≤ P * energyForm μ hQ φ.val φ.val)
    (hbound : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (G.hessian φ - b * energyForm μ hQ (U w) φ.val) ^ 2 ≤
        (L ^ 2 * ‖w‖ ^ 2 *
          ((M.measure v).real Ω - (2 * b * ell v - n * b ^ 2) * μ.real Ω)) *
        energyForm μ hQ φ.val φ.val) :
    ∃ h : SobolevSpace μ hQ, G.mixed - h ∈ SobolevSpace.dirichlet μ hQ Ω ∧
      IsSobolevHarmonicOn μ hQ Ω h ∧
      energyForm μ hQ (G.mixed - h) (G.mixed - h) ≤
        4 * (L ^ 2 * ‖w‖ ^ 2 *
          ((shiftedBochnerMeasure M (μ.restrict Ω) ell n hshift).measure (WithLp.toLp 2 (v, b))).real Ω) ∧
      ‖SobolevSpace.toLp μ hQ (G.mixed - h)‖ ^ 2 ≤
        P * (4 * (L ^ 2 * ‖w‖ ^ 2 *
          ((shiftedBochnerMeasure M (μ.restrict Ω) ell n hshift).measure (WithLp.toLp 2 (v, b))).real Ω)) := by
  have hm := ShiftedBochnerMeasure.mass M (μ.restrict Ω) ell n hshift v b Ω hΩ
  rw [measureReal_restrict_apply hΩ, inter_self] at hm
  simp only [Measure.real] at hm
  apply G.exists_harmonic_correction μ hQ hΩ hf ha b hP
    (mul_nonneg (mul_nonneg (sq_nonneg L) (sq_nonneg ‖w‖)) ENNReal.toReal_nonneg) hpoincare
  intro φ
  rw [hm]
  exact hbound φ

end RegularPointCoordinates

end

end OAI
