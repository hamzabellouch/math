import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityMoments
import OAI.Geometry.SurfaceImmersion.Primitive.PositiveDensityTurns

namespace OAI

/-! Actual smooth unit-circle loops with the prescribed uniform mean. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.LoopDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

def normalizedPath (ρ : B × ℝ → ℝ) (p : B → ℝ → Plane) : B × ℝ → Plane :=
  PositiveDensity.reparametrize ρ (fun z => p z.1 z.2)

theorem normalizedPath_properties {ρ : B × ℝ → ℝ} {p : B → ℝ → Plane}
    {c : B → Plane} {U : Set B} (hU : IsOpen U)
    (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hp : ContDiffOn ℝ ∞ (fun z : B × ℝ => p z.1 z.2) (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hpper : ∀ b ∈ U, Function.Periodic (p b) 1)
    (hmom : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t) • augment (p b t)) = augment (c b))
    (hunit : ∀ b ∈ U, ∀ t, p b t 0 ^ 2 + p b t 1 ^ 2 = 1) :
    ContDiffOn ℝ ∞ (normalizedPath ρ p) (U ×ˢ univ) ∧
      (∀ b ∈ U, Function.Periodic (fun t => normalizedPath ρ p (b, t)) 1) ∧
      (∀ b ∈ U, (∫ t in 0..1, normalizedPath ρ p (b, t)) = c b) ∧
      ∀ b ∈ U, ∀ t, normalizedPath ρ p (b, t) 0 ^ 2 + normalizedPath ρ p (b, t) 1 ^ 2 = 1 := by
  have hmm (b : B) (hb : b ∈ U) := mass_and_mean
    (LocalPeriodicCalculus.smooth_slice hU hρ hb).continuous
    (LocalPeriodicCalculus.smooth_slice hU hp hb).continuous (hmom b hb)
  have hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1 := fun b hb => (hmm b hb).1
  refine ⟨PositiveDensity.reparametrize_smoothOn hU hρ hpos hper hmass hp, ?_, ?_, ?_⟩
  · intro b hb
    exact PositiveDensity.reparametrize_periodic hU hρ hpos hper hmass hpper hb
  · intro b hb
    exact (PositiveDensity.reparametrize_mean hU hρ hpos hper hmass hp hb).trans (hmm b hb).2
  · intro b hb t
    exact hunit b hb (PositiveDensity.inverseClock ρ b t)

end ClosedSurfaceR4.LoopDensity

end

end OAI
