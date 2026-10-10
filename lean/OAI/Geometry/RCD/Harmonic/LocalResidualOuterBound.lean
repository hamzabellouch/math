import OAI.Geometry.RCD.Harmonic.UniformResidualOuterBound
import OAI.Geometry.RCD.Coordinates.BoundedSplittingCoordinates

namespace OAI

/-! # Uniform residual transport using only local boundedness -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- Clipping outside the working ball preserves its Euler identity and
all three local norms. The transport constant uses only the local bound. -/
theorem local_uniform_residual_outer_bound (n : ℕ) {F E : ℝ} (hF : 0 ≤ F)
    (C : ℝ≥0) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ (R a : ℝ), 0 < R → 0 ≤ a → a ≤ (n : ℝ) + 1 →
      ∀ (z : X) (f w q : SobolevSpace μ hQ) (σ : ℝ), 0 ≤ σ →
      IsConstantLaplacianOn μ hQ (ball z (4 * R)) f a →
      ∀ {B : ℝ} (hf : ∀ᵐ x ∂μ.restrict (ball z (4 * R)), localGamma μ hQ f f x ≤ B),
      (∀ᵐ x ∂μ.restrict (ball z (4 * R)), |SobolevSpace.toLp μ hQ w x| ≤ C) →
      ∀ e : X → ℝ, MemLp e 2 μ →
      localRadialDerivative μ hQ (ball z (4 * R)) f hf w =
        SobolevSpace.restrictLp μ hQ (ball z (4 * R)) (w + q) →
      localGamma μ hQ f (inwardSobolev μ hQ z (3 * R)) =ᵐ[μ.restrict (ball z (3 * R))]
        (fun x => e x - dist z x) →
      μ (sphere z R) = 0 →
      ‖SobolevSpace.restrictLp μ hQ (ball z (4 * R)) q‖ ≤
        F * (‖SobolevSpace.restrictLp μ hQ (ball z R) w‖ + σ) →
      (∫ x in ball z (4 * R), (e x) ^ 2 ∂μ) ≤ E ^ 2 * R ^ 2 * σ ^ 2 →
      ‖SobolevSpace.restrictLp μ hQ (ball z (2 * R)) w‖ ≤
        T * (‖SobolevSpace.restrictLp μ hQ (ball z R) w‖ + σ) := by
  obtain ⟨T, hT, hb⟩ := uniform_residual_outer_bound μ hQ n (E := E) hF C
  refine ⟨T, hT, ?_⟩
  intro R a hR ha han z f w q σ hσ hlap B hf hw e he heuler hradial hsphere hq herr
  let w' := boundedLocalVersion μ hQ w C
  have hweq : SobolevSpace.toLp μ hQ w' =ᵐ[μ.restrict (ball z (4 * R))]
      SobolevSpace.toLp μ hQ w := boundedLocalVersion_eq μ hQ w C hw
  have hreseq (s : Set X) (hs : s ⊆ ball z (4 * R)) :
      SobolevSpace.restrictLp μ hQ s w' = SobolevSpace.restrictLp μ hQ s w := by
    apply Lp.ext
    filter_upwards [SobolevSpace.restrictLp_coe μ hQ s w',
      SobolevSpace.restrictLp_coe μ hQ s w, ae_restrict_of_ae_restrict_of_subset hs hweq]
      with x hx hy hz
    rw [hx, hy, hz]
  have hDeq : localRadialDerivative μ hQ (ball z (4 * R)) f hf w' =
      localRadialDerivative μ hQ (ball z (4 * R)) f hf w := by
    apply Lp.ext
    have hγ := localGamma_pair_congr_ae μ hQ
      (f := f) (f' := f) (Filter.Eventually.of_forall fun _ => rfl) hweq
    filter_upwards [localRadialDerivative_representative μ hQ _ f w' hf,
      localRadialDerivative_representative μ hQ _ f w hf, hγ] with x hx hy hz
    rw [hx, hy, hz]
  have heuler' : localRadialDerivative μ hQ (ball z (4 * R)) f hf w' =
      SobolevSpace.restrictLp μ hQ (ball z (4 * R)) (w' + q) := by
    rw [hDeq, heuler, map_add, map_add, hreseq _ Subset.rfl]
  have hinner : ball z R ⊆ ball z (4 * R) := ball_subset_ball (by linarith)
  have houter : ball z (2 * R) ⊆ ball z (4 * R) := ball_subset_ball (by linarith)
  have hb' := hb R a hR ha han z f w' q σ hσ hlap hf
    (boundedLocalVersion_bound μ hQ w C) e he heuler' hradial hsphere
    (by rw [hreseq _ hinner]; exact hq) herr
  rwa [hreseq _ hinner, hreseq _ houter] at hb'

end RegularPointCoordinates

end

end OAI
