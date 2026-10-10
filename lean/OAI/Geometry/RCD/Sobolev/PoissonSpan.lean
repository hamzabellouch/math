import OAI.Geometry.RCD.Sobolev.PoissonGradientBridge
import OAI.Geometry.RCD.Sobolev.PoissonHessianInput
import OAI.Geometry.RCD.Sobolev.DirectionalGradientBound

namespace OAI

/-! # The actual span of harmonic coordinates and two Poisson replacements -/

open Set Metric MeasureTheory
open scoped BigOperators NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The last two components are the Poisson replacements used in a
same-scale two-center comparison. -/
def poissonSpan {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (f : Fin 2 → SobolevSpace μ hQ) : Fin (n + 2) → SobolevSpace μ hQ :=
  Fin.append u f

/-- Both replacements have the same constant Laplacian; the harmonic
coordinate components have zero Laplacian. -/
def poissonSpanLaplacian (n : ℕ) (c : ℝ) : Euclidean (n + 2) →ₗ[ℝ] ℝ :=
  ∑ i : Fin (n + 2), (Fin.append (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin 2 => c) i) •
    EuclideanSpace.projₗ i

omit [BorelSpace X] [ProperSpace X] in
theorem poissonSpan_constant_laplacian {n : ℕ} {Ω : Set X}
    (u : Fin n → SobolevSpace μ hQ) (f : Fin 2 → SobolevSpace μ hQ) (c : ℝ)
    (hu : ∀ i, IsSobolevHarmonicOn μ hQ Ω (u i))
    (hf : ∀ i, IsConstantLaplacianOn μ hQ Ω (f i) c) (v : Euclidean (n + 2)) :
    IsConstantLaplacianOn μ hQ Ω (sobolevColumnMap μ hQ (poissonSpan μ hQ u f) v)
      (poissonSpanLaplacian n c v) := by
  have hc : ∀ i : Fin (n + 2), IsConstantLaplacianOn μ hQ Ω
      (poissonSpan μ hQ u f i)
      (Fin.append (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin 2 => c) i) := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [poissonSpan, Fin.append_left] using
        (isConstantLaplacianOn_zero_iff μ hQ Ω (u j)).mpr (hu j)
    · intro j
      simpa only [poissonSpan, Fin.append_right] using hf j
  convert IsConstantLaplacianOn.linearCombination μ hQ hc v using 1
  simp only [poissonSpanLaplacian, LinearMap.sum_apply, LinearMap.smul_apply,
    EuclideanSpace.projₗ, PiLp.projₗ_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Component estimates give the full directional gradient estimate
required by the single shared Bochner measure. -/
theorem poissonSpan_gradient {n : ℕ} {Ω : Set X}
    (u : Fin n → SobolevSpace μ hQ) (f : Fin 2 → SobolevSpace μ hQ) (B : ℝ)
    (hu : ∀ i, ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ (u i) (u i) x ≤ B ^ 2)
    (hf : ∀ i, ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ (f i) (f i) x ≤ B ^ 2)
    (v : Euclidean (n + 2)) :
    ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ
      (sobolevColumnMap μ hQ (poissonSpan μ hQ u f) v)
      (sobolevColumnMap μ hQ (poissonSpan μ hQ u f) v) x ≤
        (((n + 2 : ℕ) : ℝ) * B) ^ 2 * ‖v‖ ^ 2 := by
  apply gamma_column_le_of_diagonal_bounds μ hQ
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [poissonSpan, Fin.append_left] using hu j
  · intro j
    simpa only [poissonSpan, Fin.append_right] using hf j

/-- The local estimates now produce the shared Bochner measure
for the actual coordinates and replacements. The height hypotheses are
exactly the output of the positive-source Poisson estimates. -/
theorem local_poisson_span {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    (hn : 2 ≤ n) (hgradient : LocalPoissonGradientInput hX)
    (hhessian : LocalPoissonHessianInput hX)
    {κ r ε H c Bq : ℝ} (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (p : X) (hr : 0 < r) (hcurv : -1 ≤ K * (2 * r) ^ 2)
    (hε : 0 ≤ ε) (hH : 0 ≤ H) (hBqH : Bq ≤ H)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (f q : Fin 2 → SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (8 * r)) (u i))
    (hgrad : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * r)),
      localGamma (hausdorff n X) hX.quadratic (u i) (u i) x ≤ (1 + ε) ^ 2)
    (hf : ∀ i, IsConstantLaplacianOn (hausdorff n X) hX.quadratic
      (ball p (16 * r)) (f i) c)
    (hq : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (16 * r)),
      0 ≤ SobolevSpace.toLp (hausdorff n X) hX.quadratic (q i) x ∧
        SobolevSpace.toLp (hausdorff n X) hX.quadratic (q i) x ≤ Bq)
    (hheight : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (16 * r)),
      0 ≤ SobolevSpace.toLp (hausdorff n X) hX.quadratic (q i - f i) x ∧
        SobolevSpace.toLp (hausdorff n X) hX.quadratic (q i - f i) x ≤ H) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∃ L : ℝ≥0,
      (L : ℝ) = ((n + 2 : ℕ) : ℝ) * max (1 + ε) (C₀ * (H / (2 * r) + |c| * (2 * r))) ∧
      ∃ M : PositiveBilinearMeasure X (Euclidean (n + 2)),
      let U := sobolevColumnMap (hausdorff n X) hX.quadratic
        (poissonSpan (hausdorff n X) hX.quadratic u f)
      let ell := poissonSpanLaplacian n c
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
            energyForm (hausdorff n X) hX.quadratic φ.val φ.val := by
  obtain ⟨C, hC, hbound⟩ := hgradient hn
  let D := C * (H / (2 * r) + |c| * (2 * r))
  let B := max (1 + ε) D
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB : 0 ≤ B := (by linarith : 0 ≤ 1 + ε).trans (le_max_left _ _)
  let L : ℝ≥0 := ⟨((n + 2 : ℕ) : ℝ) * B, mul_nonneg (Nat.cast_nonneg _) hB⟩
  have h8 : 8 * (2 * r) = 16 * r := by ring
  have h4 : 4 * (2 * r) = 8 * r := by ring
  have hfg (i : Fin 2) : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * r)),
      localGamma (hausdorff n X) hX.quadratic (f i) (f i) x ≤ D ^ 2 := by
    have hv := replacement_value_bound_of_height (hausdorff n X) hX.quadratic
      (q i) (f i) (ball p (16 * r)) hBqH (hq i) (hheight i)
    have hb := hbound p (2 * r) (by positivity) hcurv (f i) c H hH
      (by simpa only [h8] using hf i) (by simpa only [h8] using hv)
    simpa only [h4] using hb
  refine ⟨C, hC, L, rfl, ?_⟩
  apply hhessian κ hκ hK p r hr L
    (sobolevColumnMap (hausdorff n X) hX.quadratic
      (poissonSpan (hausdorff n X) hX.quadratic u f)) (poissonSpanLaplacian n c)
  · intro v
    apply poissonSpan_constant_laplacian (hausdorff n X) hX.quadratic u f c hu
    intro i
    exact (hf i).mono _ _ measurableSet_ball (ball_subset_ball (by linarith))
  · intro v
    apply poissonSpan_gradient (hausdorff n X) hX.quadratic u f B
    · intro i
      filter_upwards [hgrad i] with x hx
      exact hx.trans ((sq_le_sq₀ (by linarith) hB).mpr (le_max_left _ _))
    · intro i
      filter_upwards [hfg i] with x hx
      exact hx.trans ((sq_le_sq₀ hD hB).mpr (le_max_right _ _))

end RegularPointCoordinates

end

end OAI
