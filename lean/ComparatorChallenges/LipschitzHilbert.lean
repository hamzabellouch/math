import Mathlib

namespace OAI

noncomputable section

/- Use the normed-field structure on ℂ for real scalar multiplication. -/
attribute [-instance] instCommCStarAlgebraComplex

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LipschitzHilbert

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev DirectionPlane := EuclideanSpace ℝ (Fin 2)

def sample (v : DirectionPlane → DirectionPlane) (t : ℝ) (x : DirectionPlane) :
    DirectionPlane := x - t • v x

/-- The symmetrized form of the hard-truncated directional integral. -/
def shortTransform (v : DirectionPlane → DirectionPlane) (ε a : ℝ)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) : ℂ :=
  ∫ t in ε..a, t⁻¹ • (f (sample v t x) - f (sample v (-t) x))

def directionalKernel (v : DirectionPlane → DirectionPlane)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) (t : ℝ) : ℂ :=
  t⁻¹ • f (sample v t x)

/-- The two hard-cutoff intervals in the directional Hilbert transform. -/
def twoSidedTruncation (v : DirectionPlane → DirectionPlane) (ε a : ℝ)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) : ℂ :=
  (∫ t in -a..-ε, directionalKernel v f x t) +
    ∫ t in ε..a, directionalKernel v f x t

/-- The symmetric quotient extended continuously at zero for smooth inputs. -/
def smoothPrincipalValue (v : DirectionPlane → DirectionPlane) (a : ℝ)
    (f : DirectionPlane → ℂ) (x : DirectionPlane) : ℂ :=
  let g := fun t : ℝ => f (sample v t x)-f (sample v (-t) x)
  ∫ t in (0:ℝ)..a, Function.update (fun t => t⁻¹ • g t) 0 (deriv g 0) t

attribute [instance] instCommCStarAlgebraComplex

def ShortHilbertConclusion (a : ℝ) (C : ℝ≥0) : Prop :=
  ∀ v : Plane → Plane, LipschitzWith 1 v → (∀ x, ‖v x‖=1) →
    (∀ epsilon : ℝ, 0<epsilon → epsilon<a → ∀ f : SchwartzMap Plane ℂ,
      eLpNorm (twoSidedTruncation v epsilon a f) 2 volume≤C*eLpNorm f 2 volume) ∧
    (∀ f : SchwartzMap Plane ℂ,
      eLpNorm (smoothPrincipalValue v a f) 2 volume≤C*eLpNorm f 2 volume) ∧
    (∀ f : SchwartzMap Plane ℂ, ∀ level : ℝ≥0∞, level≠0 → level≠∞ →
      volume {x | level<‖smoothPrincipalValue v a f x‖ₑ}≤
        level⁻¹^2*((C:ℝ≥0∞)*eLpNorm f 2 volume)^2) ∧
    (∀ epsilon : ℝ, 0<epsilon → epsilon<a →
      ∃ T : Lp ℂ 2 (volume : Measure Plane) →L[ℂ] Lp ℂ 2 volume,
        ‖T‖≤C ∧ ∀ f : SchwartzMap Plane ℂ,
          (T (f.toLp 2 volume) : Plane → ℂ)=ᵐ[volume] twoSidedTruncation v epsilon a f) ∧
    (∃ T : Lp ℂ 2 (volume : Measure Plane) →L[ℂ] Lp ℂ 2 volume,
      ‖T‖≤C ∧ ∀ f : SchwartzMap Plane ℂ,
        (T (f.toLp 2 volume) : Plane → ℂ)=ᵐ[volume] smoothPrincipalValue v a f)

/-- Uniform hard truncation, principal-value and weak-(2,2) estimates,
with bounded L² extensions for all Lipschitz unit vector fields. -/
theorem main :
    ∃ a : ℝ, a∈Ioo 0 (1/2) ∧ ∃ C : ℝ≥0, 0<C ∧ ShortHilbertConclusion a C := by
  sorry

/-- The same uniform estimate at the reciprocal-Lipschitz truncation scale. -/
theorem uniform_truncation :
    ∃ C : ℝ, 0<C ∧ ∀ K : ℝ≥0, 0<K → ∀ epsilon R : ℝ,
      0<epsilon → epsilon≤R → R≤1/(1000000*(K:ℝ)) →
      ∀ v : Plane → Plane, LipschitzWith K v → (∀ x, ‖v x‖=1) →
      ∀ f : SchwartzMap Plane ℂ,
        eLpNorm (shortTransform v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) := by
  sorry

end LipschitzHilbert

end

end OAI
