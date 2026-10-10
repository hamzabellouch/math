import OAI.Geometry.SurfaceImmersion.Geometry.PositiveDensityReparam

namespace OAI

/-! Reparametrization commutes exactly with pulling back the parameter family. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PositiveDensity

variable {B E F : Type}

def pullbackDensity (ρ : B × ℝ → ℝ) (σ : E → B) : E × ℝ → ℝ :=
  fun z => ρ (σ z.1, z.2)

lemma clock_pullback (ρ : B × ℝ → ℝ) (σ : E → B) (x : E) (t : ℝ) :
    clock (pullbackDensity ρ σ) x t = clock ρ (σ x) t := rfl

lemma inverseClock_pullback (ρ : B × ℝ → ℝ) (σ : E → B) (x : E) (t : ℝ) :
    inverseClock (pullbackDensity ρ σ) x t = inverseClock ρ (σ x) t := rfl

lemma reparametrize_pullback (ρ : B × ℝ → ℝ) (σ : E → B) (f : B × ℝ → F)
    (z : E × ℝ) :
    reparametrize (pullbackDensity ρ σ) (fun w => f (σ w.1, w.2)) z =
      reparametrize ρ f (σ z.1, z.2) := rfl

variable [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma pullbackDensity_smoothOn {ρ : B × ℝ → ℝ} {σ : E → B} {U : Set E} {W : Set B}
    (hρ : ContDiffOn ℝ ∞ ρ (W ×ˢ univ)) (hσ : ContDiffOn ℝ ∞ σ U)
    (hσW : MapsTo σ U W) :
    ContDiffOn ℝ ∞ (pullbackDensity ρ σ) (U ×ˢ univ) := by
  exact hρ.comp ((hσ.comp contDiffOn_fst (fun z hz => hz.1)).prodMk contDiffOn_snd)
    (fun z hz => ⟨hσW hz.1, mem_univ _⟩)

end ClosedSurfaceR4.PositiveDensity

end

end OAI
