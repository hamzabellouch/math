import OAI.Geometry.RCD.Sobolev.HarmonicSequenceEnergy

namespace OAI

/-! # Uniform affine improvement from published harmonic compactness

The threshold is uniform in the center, radius, coordinates and harmonic
function. All inputs are measured approximation, a rescaled curvature
bound, harmonicity and an actual normalized L² bound. The affine estimate
itself is proved by a compactness contradiction.
-/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The averaged norm, with its radius dependence exposed for rescaling. -/
def harmonicTargetNorm {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    (p : X) (r : ℝ) (w : SobolevSpace (hausdorff n X) hX.quadratic) : ℝ :=
  ‖normalizeLocalL2 (hausdorff n X) (ball p r)
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p r) w)‖

/-- The averaged affine residual, with its radius dependence exposed. -/
def harmonicAffineResidualNorm {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (p : X) (r : ℝ) (w : SobolevSpace (hausdorff n X) hX.quadratic) : ℝ :=
  ‖normalizeLocalL2 (hausdorff n X) (ball p r)
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (affineResidual (hausdorff n X) hX.quadratic u (ball p r)
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p r) w))‖

/-- One normalized harmonic test on a measured almost-Euclidean ball. -/
structure NormalizedHarmonicTest {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (S ε : ℝ) where
  center : X
  scale : ℝ
  scale_pos : 0 < scale
  curvature : -1 ≤ K * scale ^ 2
  coordinates : Fin n → SobolevSpace (hausdorff n X) hX.quadratic
  values : X → Euclidean n
  target : SobolevSpace (hausdorff n X) hX.quadratic
  approximation : IsMeasuredEuclideanApproximation (hausdorff n X) n center scale S ε values
  representative : ∀ i, SobolevSpace.toLp (hausdorff n X) hX.quadratic (coordinates i) =ᵐ[
    (hausdorff n X).restrict (ball center (S * scale))] fun x => values x i
  harmonic : IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball center (S * scale)) target
  normalized : harmonicTargetNorm hX center (S * scale) target ≤ 1

namespace NormalizedHarmonicTest

variable {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} {S ε : ℝ}

def residualNorm (d : NormalizedHarmonicTest hX S ε) (ρ : ℝ) : ℝ :=
  harmonicAffineResidualNorm hX d.coordinates d.center (ρ * d.scale) d.target

end NormalizedHarmonicTest

omit [ProperSpace X] in
/-- The quantitative affine-improvement theorem for normalized harmonic
functions. There is no energy-bound or affine-fit premise: the former is
derived from Jiang's estimate and the latter from the Euclidean limit. -/
theorem harmonic_affine_improvement_of_measured_approximation
    {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (hcompact : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput n) :
    ∃ m : ℕ, 3 ≤ m ∧ ∀ S : ℝ, 0 < S →
      ∃ ε : ℝ, 0 < ε ∧ ∀ d : NormalizedHarmonicTest hX S ε,
        d.residualNorm ((1 / 2 : ℝ) ^ m * S) <
          (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ m * Real.sqrt ((1 / 2 : ℝ) ^ m) := by
  classical
  obtain ⟨m, hm, hmodel⟩ := heuclidean.affine_contraction
  refine ⟨m, hm, ?_⟩
  intro S hS
  by_contra hbad
  push Not at hbad
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε : ∀ k, 0 < ε k := fun k => by dsimp only [ε]; positivity
  have hchoice : ∀ k, ∃ d : NormalizedHarmonicTest hX S (ε k),
      (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ m * Real.sqrt ((1 / 2 : ℝ) ^ m) ≤
        d.residualNorm ((1 / 2 : ℝ) ^ m * S) := fun k => hbad (ε k) (hε k)
  choose d hd using hchoice
  let data : HarmonicCompactnessSequence hX S := {
    center := fun k => (d k).center
    scale := fun k => (d k).scale
    error := ε
    scale_pos := fun k => (d k).scale_pos
    curvature := fun k => (d k).curvature
    error_pos := hε
    error_zero := tendsto_one_div_add_atTop_nhds_zero_nat
    coordinates := fun k => (d k).coordinates
    values := fun k => (d k).values
    target := fun k => (d k).target
    approximation := fun k => (d k).approximation
    representative := fun k => (d k).representative
    harmonic := fun k => (d k).harmonic
    normalized := fun k => (d k).normalized
    energy := rescaled_harmonic_energy_of_gradient hgradient hn hS
      (fun k => (d k).center) (fun k => (d k).scale)
      (fun k => (d k).scale_pos) (fun k => (d k).curvature)
      (fun k => (d k).target) (fun k => (d k).harmonic) (fun k => (d k).normalized) }
  obtain ⟨k, hk⟩ := (data.eventual_affine_contraction hcompact hm hmodel hS).exists
  exact (not_lt_of_ge (hd k)) hk

end RegularPointCoordinates

end

end OAI
