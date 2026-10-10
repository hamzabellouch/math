import OAI.Geometry.RCD.Harmonic.HarmonicMomentCompactnessInput
import OAI.Geometry.RCD.Harmonic.EuclideanHarmonicContraction

namespace OAI

/-! # Harmonic affine improvement along an actual RCD rescaling sequence -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The local bounds and measured approximations appearing in the
published harmonic-compactness input, bundled for subsequence restriction. -/
structure HarmonicCompactnessSequence {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (S : ℝ) where
  center : ℕ → X
  scale : ℕ → ℝ
  error : ℕ → ℝ
  scale_pos : ∀ k, 0 < scale k
  curvature : ∀ k, -1 ≤ K * scale k ^ 2
  error_pos : ∀ k, 0 < error k
  error_zero : Tendsto error atTop (𝓝 0)
  coordinates : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic
  values : ℕ → X → Euclidean n
  target : ℕ → SobolevSpace (hausdorff n X) hX.quadratic
  approximation : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n
    (center k) (scale k) S (error k) (values k)
  representative : ∀ k i, SobolevSpace.toLp (hausdorff n X) hX.quadratic (coordinates k i) =ᵐ[
    (hausdorff n X).restrict (ball (center k) (S * scale k))] fun x => values k x i
  harmonic : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
    (ball (center k) (S * scale k)) (target k)
  normalized : ∀ k, ‖normalizeLocalL2 (hausdorff n X) (ball (center k) (S * scale k))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
      (ball (center k) (S * scale k)) (target k))‖ ≤ 1
  energy : ∀ ρ : ℝ, 0 < ρ → ρ < S → ∃ C : ℝ, 0 ≤ C ∧ ∀ k,
    scale k ^ 2 * ((hausdorff n X).real (ball (center k) (S * scale k)))⁻¹ *
      (∫ x in ball (center k) (ρ * scale k), localGamma (hausdorff n X) hX.quadratic
        (target k) (target k) x ∂hausdorff n X) ≤ C

namespace HarmonicCompactnessSequence

variable {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} {S : ℝ}

/-- Restricting to an increasing subsequence preserves precisely the
analytic and geometric hypotheses of local harmonic compactness. -/
def subsequence (d : HarmonicCompactnessSequence hX S) (s : ℕ → ℕ) (hs : StrictMono s) :
    HarmonicCompactnessSequence hX S where
  center := d.center ∘ s
  scale := d.scale ∘ s
  error := d.error ∘ s
  scale_pos := fun k => d.scale_pos (s k)
  curvature := fun k => d.curvature (s k)
  error_pos := fun k => d.error_pos (s k)
  error_zero := d.error_zero.comp hs.tendsto_atTop
  coordinates := d.coordinates ∘ s
  values := d.values ∘ s
  target := d.target ∘ s
  approximation := fun k => d.approximation (s k)
  representative := fun k => d.representative (s k)
  harmonic := fun k => d.harmonic (s k)
  normalized := fun k => d.normalized (s k)
  energy := fun ρ hρ hρS => by
    obtain ⟨C, hC, hb⟩ := d.energy ρ hρ hρS
    exact ⟨C, hC, fun k => hb (s k)⟩

def residualNorm (d : HarmonicCompactnessSequence hX S) (ρ : ℝ) (k : ℕ) : ℝ :=
  ‖normalizeLocalL2 (hausdorff n X) (ball (d.center k) (ρ * d.scale k))
    (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (affineResidual (hausdorff n X) hX.quadratic (d.coordinates k)
      (ball (d.center k) (ρ * d.scale k))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic
        (ball (d.center k) (ρ * d.scale k)) (d.target k)))‖

omit [ProperSpace X] in
/-- Actual local harmonic compactness gives the affine contraction for
all sufficiently late members of each admissible rescaling sequence. -/
theorem eventual_affine_contraction (hcompact : LocalHarmonicMomentCompactnessInput hX)
    {m : ℕ} (hm : 3 ≤ m)
    (hmodel : ∀ S : ℝ, 0 < S → ∀ w : EuclideanHarmonicModel n S,
      ∃ (c : ℝ) (v : Euclidean n), ∃ hρS : (1 / 2 : ℝ) ^ m * S ≤ S,
        ‖∑ i, affineErrorCoefficients c (fun j => v j) i • w.moments hρS i‖ <
          (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ m * Real.sqrt ((1 / 2 : ℝ) ^ m))
    (hS : 0 < S) (d : HarmonicCompactnessSequence hX S) :
    ∀ᶠ k in atTop, d.residualNorm ((1 / 2 : ℝ) ^ m * S) k <
      (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ m * Real.sqrt ((1 / 2 : ℝ) ^ m) := by
  let θ := (1 / 2 : ℝ) ^ m
  have hθ : 0 < θ := pow_pos (by norm_num) _
  have hθhalf : θ ≤ 1 / 2 := by
    have hh : θ = (1 / 2 : ℝ) ^ (m - 1) * (1 / 2) := by
      dsimp only [θ]
      rw [← pow_succ]
      congr 1
      omega
    rw [hh]
    exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
  have hρ : 0 < θ * S := mul_pos hθ hS
  have hρS : θ * S < S := by nlinarith
  by_contra hbad
  have hb : ∃ᶠ k in atTop, ¬ d.residualNorm (θ * S) k <
      (1 / 2 : ℝ) * θ * Real.sqrt θ := by
    simpa only [Filter.Frequently, not_not] using hbad
  obtain ⟨s, hs, hfail⟩ := extraction_of_frequently_atTop hb
  let d' := d.subsequence s hs
  obtain ⟨t, _ht, model, hlimit⟩ := hcompact S hS d'.center d'.scale d'.error
    d'.scale_pos d'.curvature d'.error_pos d'.error_zero d'.coordinates d'.values d'.target
    d'.approximation d'.representative d'.harmonic d'.normalized d'.energy
  obtain ⟨c, v, hboundRadius, hc⟩ := hmodel S hS model
  have hc' : ‖∑ i, affineErrorCoefficients c (fun j => v j) i •
      model.moments hboundRadius i‖ < (1 / 2 : ℝ) * θ * Real.sqrt θ := by
    have hroot : 0 < Real.sqrt θ := Real.sqrt_pos.2 hθ
    exact hc.trans (by change (1 / 4 : ℝ) * θ * Real.sqrt θ < _; nlinarith)
  have he := eventually_normalized_affineResidual_lt (hausdorff n X) hX.quadratic
    (fun k => d'.coordinates (t k)) (fun k => d'.target (t k))
    (fun k => ball (d'.center (t k)) ((θ * S) * d'.scale (t k)))
    (fun _ => ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
    (model.moments hboundRadius) (hlimit (θ * S) hρ hρS) c v hc'
  obtain ⟨k, hk⟩ := he.exists
  exact hfail (t k) hk

end HarmonicCompactnessSequence
end RegularPointCoordinates

end

end OAI
