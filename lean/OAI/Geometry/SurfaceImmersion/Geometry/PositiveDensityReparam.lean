import OAI.Geometry.SurfaceImmersion.Geometry.PositiveDensityInverse

namespace OAI

/-! Reparametrization converts an exact positive weighted mean into the uniform mean. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PositiveDensity

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ρ : B × ℝ → ℝ} {F : B × ℝ → E} {U : Set B}

def reparametrize (ρ : B × ℝ → ℝ) (F : B × ℝ → E) (z : B × ℝ) : E :=
  F (z.1, inverseClock ρ z.1 z.2)

omit [CompleteSpace E] in
lemma reparametrize_smoothOn (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (reparametrize ρ F) (U ×ˢ univ) :=
  hF.comp (contDiffOn_fst.prodMk (inverseClock_smoothOn hU hρ hpos hper hmass))
    (fun _ hz => ⟨hz.1, mem_univ _⟩)

omit [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
lemma reparametrize_periodic (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    (hFper : ∀ b ∈ U, Function.Periodic (fun t => F (b, t)) 1)
    {b : B} (hb : b ∈ U) : Function.Periodic (fun t => reparametrize ρ F (b, t)) 1 := by
  intro t
  simp only [reparametrize, inverseClock_period hU hρ hpos hper hmass hb]
  exact hFper b hb _

omit [CompleteSpace E] in
/-- The exact change of variables, for the actual vector-valued velocity. -/
theorem reparametrize_mean (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ)) {b : B} (hb : b ∈ U) :
    (∫ θ in 0..1, reparametrize ρ F (b, θ)) = ∫ t in 0..1, ρ (b, t) • F (b, t) := by
  have hri := reparametrize_smoothOn hU hρ hpos hper hmass hF
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (a := 0) (b := 1) (f := clock ρ b) (f' := fun t => ρ (b, t))
    (g := fun θ => reparametrize ρ F (b, θ))
    (fun t _ => hasDerivAt_clock hU hρ hb t)
    (LocalPeriodicCalculus.smooth_slice hU hρ hb).continuous.continuousOn
    (LocalPeriodicCalculus.smooth_slice hU hri hb).continuous
  have h1 : clock ρ b 1 = 1 := hmass b hb
  simpa only [Function.comp_apply, reparametrize, inverseClock_clock hU hρ hpos hb,
    clock_zero, h1] using hsub.symm

end ClosedSurfaceR4.PositiveDensity

end

end OAI
