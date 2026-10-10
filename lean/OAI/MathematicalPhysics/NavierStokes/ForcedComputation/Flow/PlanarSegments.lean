import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarTranslation

namespace OAI

/-! The actual elementary trajectories used by the finite processor. Each
curve is polynomial in one smooth clock and satisfies the cutoff equation
whenever it lies in its assigned filled rectangle. -/

noncomputable section
namespace ForcedComputation.PlanarHamiltonian

open ShearFlows PlanarRouting Set
open scoped ContDiff

def Primitive.path (p : Primitive) (θ : ℝ → ℝ) (x : Plane) : ℝ → Plane :=
  match p with
  | .translation v => translationPath θ (fun j => (v j : ℝ)) x
  | .horizontal c a => horizontalPath θ a (fun j => (c j : ℝ)) (x - fun j => (c j : ℝ))
  | .vertical c a => verticalPath θ a (fun j => (c j : ℝ)) (x - fun j => (c j : ℝ))

def Primitive.endpoint (p : Primitive) (x : Plane) : Plane := p.path (fun _ => 1) x 0

theorem Primitive.path_hasDerivAt (p : Primitive) (x : Plane) {θ : ℝ → ℝ} {θ' t : ℝ}
    (hθ : HasDerivAt θ θ' t) :
    HasDerivAt (p.path θ x) (θ' • field p.potential (p.path θ x t)) t := by
  cases p with
  | translation v =>
      change HasDerivAt (translationPath θ (fun j => (v j : ℝ)) x)
        (θ' • field (translationPotential (fun j => (v j : ℝ))) _) t
      rw [field_translation]
      exact translationPath_hasDerivAt hθ _ _
  | horizontal c a => exact horizontalPath_hasDerivAt hθ _ _ _
  | vertical c a => exact verticalPath_hasDerivAt hθ _ _ _

theorem Primitive.path_smooth (p : Primitive) (x : Plane) {θ : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) : ContDiff ℝ ∞ (p.path θ x) := by
  cases p <;> dsimp only [Primitive.path, translationPath, horizontalPath, verticalPath]
  all_goals
    apply contDiff_pi.mpr
    intro j
    fin_cases j <;> dsimp [translationPath, horizontalPath, verticalPath, shearX, shearY] <;> fun_prop

theorem Primitive.path_start (p : Primitive) (x : Plane) {θ : ℝ → ℝ} {t : ℝ}
    (hθ : θ t = 0) : p.path θ x t = x := by
  cases p <;> ext j <;> fin_cases j <;>
    simp [Primitive.path, translationPath, horizontalPath, verticalPath, shearX, shearY, hθ]

theorem Primitive.path_end (p : Primitive) (x : Plane) {θ : ℝ → ℝ} {t : ℝ}
    (hθ : θ t = 1) : p.path θ x t = p.endpoint x := by
  cases p <;> simp [Primitive.path, Primitive.endpoint, translationPath,
    horizontalPath, verticalPath, hθ]

def Pulse.curve (p : Pulse) (x : Plane) : ℝ → Plane :=
  p.primitive.path (smoothRamp p.start p.finish) x

theorem Pulse.curve_smooth (p : Pulse) (x : Plane) : ContDiff ℝ ∞ (p.curve x) :=
  p.primitive.path_smooth x (smoothRamp_smooth _ _)

theorem Pulse.curve_ode {p : Pulse} (hp : p.Valid) (x : Plane) (t : ℝ)
    (hx : p.curve x t ∈ p.rectangle.carrier) :
    HasDerivAt (p.curve x) (p.velocity t (p.curve x t)) t := by
  rw [Pulse.velocity, p.spatial_on_rectangle hp hx]
  exact p.primitive.path_hasDerivAt x
    (((smoothRamp_smooth p.start p.finish).differentiable (by simp) t).hasDerivAt)

theorem Pulse.curve_before {p : Pulse} (hp : p.Valid) (x : Plane) {t : ℝ}
    (ht : t ≤ (p.start : ℝ)) : p.curve x t = x := by
  apply p.primitive.path_start
  exact smoothRamp_before (by exact_mod_cast hp.2) ht

theorem Pulse.curve_after {p : Pulse} (hp : p.Valid) (x : Plane) {t : ℝ}
    (ht : (p.finish : ℝ) ≤ t) : p.curve x t = p.primitive.endpoint x := by
  apply p.primitive.path_end
  exact smoothRamp_after (by exact_mod_cast hp.2) ht

end ForcedComputation.PlanarHamiltonian

end

end OAI
