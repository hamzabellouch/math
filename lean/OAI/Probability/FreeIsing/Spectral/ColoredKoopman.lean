import OAI.Probability.FreeIsing.Spectral.KoopmanInvolutions
import OAI.Probability.FreeIsing.Trees.ColoredEdgeLifts

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.ColoredEdgeLifts
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def koopmanEquiv (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℝ τ hτ)
    (koopmanL2_involutive τ hτ hinv).surjective

@[simp] theorem koopmanEquiv_apply (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) (f : Lp ℝ 2 μ) :
    koopmanEquiv τ hτ hinv f = koopmanL2 τ hτ f := rfl

theorem koopmanEquiv_involutive (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) : Function.Involutive (koopmanEquiv τ hτ hinv) :=
  koopmanL2_involutive τ hτ hinv

variable [IsFiniteMeasure μ]

def centeredKoopmanIsometry (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) : centeredL2 μ →ₗᵢ[ℝ] centeredL2 μ where
  toLinearMap := ((koopmanL2 τ hτ).restrict
    (koopmanL2_preserves_centered τ hτ hinv)).toLinearMap
  norm_map' f := koopmanL2_norm τ hτ (f : Lp ℝ 2 μ)

@[simp] theorem centeredKoopmanIsometry_apply_coe
    (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) (f : centeredL2 μ) :
    (centeredKoopmanIsometry τ hτ hinv f : Lp ℝ 2 μ) = koopmanL2 τ hτ f := rfl

theorem centeredKoopmanIsometry_involutive
    (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) : Function.Involutive (centeredKoopmanIsometry τ hτ hinv) := by
  intro f
  apply Subtype.ext
  exact koopmanL2_involutive τ hτ hinv f

def centeredKoopmanEquiv (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) : centeredL2 μ ≃ₗᵢ[ℝ] centeredL2 μ :=
  LinearIsometryEquiv.ofSurjective (centeredKoopmanIsometry τ hτ hinv)
    (centeredKoopmanIsometry_involutive τ hτ hinv).surjective

@[simp] theorem centeredKoopmanEquiv_apply_coe
    (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) (f : centeredL2 μ) :
    (centeredKoopmanEquiv τ hτ hinv f : Lp ℝ 2 μ) = koopmanL2 τ hτ f := rfl

theorem centeredKoopmanEquiv_involutive
    (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) : Function.Involutive (centeredKoopmanEquiv τ hτ hinv) :=
  centeredKoopmanIsometry_involutive τ hτ hinv

theorem neighborAverage_centeredKoopmanEquiv {d : ℕ}
    (τ : Fin d → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hinv : ∀ i, Function.Involutive (τ i)) :
    neighborAverage (fun i => centeredKoopmanEquiv (τ i) (hτ i) (hinv i)) =
      centeredKoopmanAverage τ hτ hinv := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  simp [neighborAverage_apply, centeredKoopmanAverage, koopmanAverage]

end Problem367.ColoredEdgeLifts

end

end OAI
