import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeImageBridge
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePathConcatenation

namespace OAI

/-! # Actual good probes supply the two-path packing geometry -/

noncomputable section
namespace PolycyclicRecognition

open Filter Set
open scoped Topology NNReal

variable {G W V Z : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [AddCommGroup V] [Module ℝ V]

omit [IsIsometricSMul G G] in
/-- A finite image cover retains the witness needed to use the two actual
paths. The second endpoint height is derived from its common affine profile;
the image bridge is derived from the source bridge and the Lipschitz bound. -/
theorem probe_image_two_path_geometry
    {Y : ℕ → Type*} (good : ∀ n, Set (Y n)) (tiles : ℕ → ℕ)
    (tile : ∀ n, Y n → Fin (tiles n)) (points : ∀ n, Fin (tiles n) → Finset G)
    (height : G →* Multiplicative W) (f : ℕ → G → G)
    (center base : ℕ → G) (anchor : ∀ n, Fin (tiles n) → G)
    (first second : ∀ n, Y n → G) (scale η : ℕ → ℝ)
    (chart : ℕ → Z → G) (q : Z → V) (z₀ : ℕ → Z)
    (A : V →ₗ[ℝ] W) (b : W) (E₁ E₂ : Set W)
    (L B δ D : ℝ) (Λ : ℝ≥0)
    (hscale : ∀ n, 0 < scale n) (hη : Tendsto η atTop (𝓝 0))
    (hδ : 0 < δ) (hLip : ∀ n, LipschitzWith Λ (f n)) (hD : (Λ : ℝ) * D ≤ δ)
    (hpoint : ∀ n j x, x ∈ points n j → ∃ y ∈ good n,
      tile n y = j ∧ f n (center n * first n y * chart n (z₀ n)) = x)
    (hprofiles : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n)
        (anchor n (tile n y)) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b)‖ ≤ η n ∧
      ‖rescaledMapProfile (fun g => (height (f n g)).toAdd) (center n)
        (second n y) (Real.log (scale n)) (chart n) (z₀ n) -
          (A (q (z₀ n)) + b)‖ ≤ η n)
    (hbridge : ∀ᶠ n in atTop, ∀ y ∈ good n,
      dist (center n * second n y * chart n (z₀ n))
        (center n * first n y * chart n (z₀ n)) ≤ D * scale n)
    (hpaths : ∀ᶠ n in atTop, ∀ y ∈ good n,
      ∃ (path₁ : Path (1 : G) (basedImage (f n)
          (center n * base n * chart n (z₀ n))
          (center n * first n y * chart n (z₀ n))))
        (path₂ : Path (1 : G) (basedImage (f n)
          (center n * anchor n (tile n y) * chart n (z₀ n))
          (center n * second n y * chart n (z₀ n)))),
        PathMetricBound path₁ (L * scale n) (B * (1 + Real.log (2 + scale n))) ∧
        PathMetricBound path₂ (L * scale n) (B * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₁, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + L * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₂, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + L * (1 + Real.log (2 + scale n)))) :
    ∀ᶠ n in atTop, ∀ j, ∀ x ∈ points n j,
      ∃ (secondPoint : G)
        (path₁ : Path (1 : G) ((f n (center n * base n * chart n (z₀ n)))⁻¹ * x))
        (path₂ : Path (1 : G)
          ((f n (center n * anchor n j * chart n (z₀ n)))⁻¹ * secondPoint)),
        PathMetricBound path₁ (L * scale n) (B * (1 + Real.log (2 + scale n))) ∧
        PathMetricBound path₂ (L * scale n) (B * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₁, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + L * (1 + Real.log (2 + scale n))) ∧
        (∀ t, ∃ w ∈ E₂, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
          2 * scale n * η n + L * (1 + Real.log (2 + scale n))) ∧
        ‖(height ((f n (center n * anchor n j * chart n (z₀ n)))⁻¹ * secondPoint)).toAdd‖ ≤
          δ * scale n ∧ dist secondPoint x ≤ δ * scale n := by
  have hheight := eventually_uniform_probe_height_small height f center
    (fun n y => anchor n (tile n y)) second good scale η chart q A b z₀
    hscale hη hprofiles hδ
  filter_upwards [hheight, hbridge, hpaths] with n hnheight hnbridge hnpaths
  intro j x hx
  obtain ⟨y, hy, rfl, rfl⟩ := hpoint n j x hx
  obtain ⟨p₁, p₂, hm₁, hm₂, hh₁, hh₂⟩ := hnpaths y hy
  refine ⟨f n (center n * second n y * chart n (z₀ n)), p₁, p₂,
    hm₁, hm₂, hh₁, hh₂, hnheight y hy, ?_⟩
  calc
    _ ≤ (Λ : ℝ) * dist (center n * second n y * chart n (z₀ n))
        (center n * first n y * chart n (z₀ n)) := (hLip n).dist_le_mul _ _
    _ ≤ (Λ : ℝ) * (D * scale n) :=
      mul_le_mul_of_nonneg_left (hnbridge y hy) Λ.coe_nonneg
    _ = ((Λ : ℝ) * D) * scale n := (mul_assoc _ _ _).symm
    _ ≤ δ * scale n := mul_le_mul_of_nonneg_right hD (hscale n).le

end PolycyclicRecognition

end

end OAI
