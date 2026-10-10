import OAI.Geometry.RCD.Metric.ProductFactorDiameter
import OAI.Geometry.RCD.Harmonic.NearbyMeanGrams

namespace OAI

/-!
# First-order splitting maps and the published almost-splitting input

`LocalAlmostSplittingInput` is a specialization of Huang--Huang (2024),
Theorem 2.9(2), with the first-order criterion following Definition 2.7.
The first-order data are imposed on B_(16r); the conclusion concerns B_(2r),
leaving the factor two needed for the criterion. Threshold losses include
metric rescaling and the conversion from GH isometries to pointed maps.

The consequence proved here eliminates the residual product factor when
there is also a Euclidean approximation. No bi-Lipschitz or injectivity
conclusion is included in the published premise.
-/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section

namespace RegularPointCoordinates

universe u

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The first-order conditions of Huang--Huang Definition 2.7, on actual
Sobolev components with continuous pointwise representatives. The Hessian
condition is obtained on a smaller ball by the published following remark. -/
structure FirstOrderSplittingOn {n : ℕ} (p : X) (r ε : ℝ)
    (u : Fin n → SobolevSpace μ hQ) (v : X → Euclidean n) : Prop where
  representative : ∀ i, SobolevSpace.toLp μ hQ (u i) =ᵐ[μ.restrict (ball p r)]
    fun x => v x i
  continuous : ContinuousOn v (ball p r)
  harmonic : ∀ i, IsSobolevHarmonicOn μ hQ (ball p r) (u i)
  gradient : ∀ i, ∀ᵐ x ∂μ.restrict (ball p r),
    localGamma μ hQ (u i) (u i) x ≤ (1 + ε) ^ 2
  gram : ∀ i j, (μ.real (ball p r))⁻¹ * ∫ x in ball p r,
    |localGamma μ hQ (u i) (u j) x - (if i = j then 1 else 0)| ∂μ ≤ ε

/-- The precise product-map consequence used from Huang--Huang Theorem
2.9(2) and its first-order criterion, including the residual product factor. -/
def LocalAlmostSplittingInput {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) : Prop :=
  2 ≤ n → ∀ τ : ℝ, 0 < τ → ∃ ε : ℝ, 0 < ε ∧
    ∀ (p : X) (r : ℝ), 0 < r → -ε ≤ K * r ^ 2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (16 * r) ε u v →
        ∃ (Z : Type u) (dZ : MetricSpace Z), letI := dZ
          ∃ (z₀ : Z) (w : X → Z),
            IsPointedApproximation p (WithLp.toLp 2 (0, z₀)) r 2 τ
              (fun x => WithLp.toLp 2 (r⁻¹ • (v x - v p), w x))

/-- Only this Euclidean-flat coordinate consequence of the product theorem
is used in the chart construction. It is also proved directly from the
noncollapsed measured-coordinate input in `FlatSplittingApproximation`. -/
def LocalFlatSplittingInput {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) : Prop :=
  2 ≤ n → ∀ ρ : ℝ, 0 < ρ → ∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧
    ∀ (p : X) (r : ℝ), 0 < r → -ε ≤ K*r^2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (16*r) ε u v →
        (∃ f : X → Euclidean n, IsPointedApproximation p 0 r 2 τ f) →
        IsPointedApproximation p 0 r (1/2) ρ (fun x => r⁻¹ • (v x-v p))

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
/-- Increasing the error preserves a pointed approximation, including
its smaller target-density requirement. -/
theorem IsPointedApproximation.mono_error {Y : Type*} [MetricSpace Y]
    {p : X} {q : Y} {r R ε δ : ℝ} {f : X → Y}
    (hf : IsPointedApproximation p q r R ε f) (hεδ : ε ≤ δ) :
    IsPointedApproximation p q r R δ f := by
  refine ⟨hf.1.trans hεδ, fun x y hx hy => (hf.2.1 x y hx hy).trans hεδ, ?_⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hf.2.2 y (by linarith)
  exact ⟨x, hx, hxy.trans hεδ⟩

omit [ProperSpace X] in
/-- Almost splitting plus metric flatness controls the actual harmonic
coordinates. The tolerances are uniform in the center, scale and map. -/
theorem splitting_coordinates_approximate {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hpublished : LocalAlmostSplittingInput hX)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ τ ε : ℝ, 0 < τ ∧ 0 < ε ∧
      ∀ (p : X) (r : ℝ), 0 < r → -ε ≤ K * r ^ 2 →
        ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
          FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (16 * r) ε u v →
          (∃ f : X → Euclidean n, IsPointedApproximation p 0 r 2 τ f) →
          IsPointedApproximation p 0 r (1 / 2) ρ (fun x => r⁻¹ • (v x - v p)) := by
  let C : ℝ := 1 + 80 * ((n + 1 : ℕ) : ℝ) ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  let τ := min (1 / 4 : ℝ) (ρ / C)
  have hτ : 0 < τ := lt_min (by norm_num) (div_pos hρ hC)
  obtain ⟨ε, hε, happly⟩ := hpublished hn τ hτ
  refine ⟨τ, ε, hτ, hε, ?_⟩
  intro p r hr hcurv u v hsplit hflat
  obtain ⟨f, hf⟩ := hflat
  obtain ⟨Z, dZ, z₀, w, hw⟩ := happly p r hr hcurv u v hsplit
  let : MetricSpace Z := dZ
  have hcoord := product_projection_approximation n hr hτ.le hτ.le
    (min_le_left _ _) f (fun x => WithLp.toLp 2 (r⁻¹ • (v x - v p), w x)) hf hw
  apply hcoord.mono_error
  have hτC : τ * C ≤ ρ := (le_div_iff₀ hC).mp (min_le_right _ _)
  dsimp [C] at hτC
  nlinarith

omit [ProperSpace X] in
theorem LocalAlmostSplittingInput.flatSplittingInput {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} (h : LocalAlmostSplittingInput hX) :
    LocalFlatSplittingInput hX := by
  intro hn ρ hρ
  exact splitting_coordinates_approximate hX hn h hρ

end RegularPointCoordinates

end

end OAI
