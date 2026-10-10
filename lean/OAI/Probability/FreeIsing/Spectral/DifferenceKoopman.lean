import OAI.Probability.FreeIsing.Conditioning.CenteredCopyDifference
import OAI.Probability.FreeIsing.Spectral.ColoredKoopman

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367.CopyDifference

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable {μ : Measure A} {ν : Measure B} {p q : B → A}
variable (hp : MeasurePreserving p ν μ) (hq : MeasurePreserving q ν μ)
variable (τ : A → A) (σ : B → B)
variable (hτ : MeasurePreserving τ μ μ) (hσ : MeasurePreserving σ ν ν)
variable (hpc : p ∘ σ = τ ∘ p) (hqc : q ∘ σ = τ ∘ q)

include hpc hqc in
private theorem symmetry_intertwines (f : Lp ℝ 2 μ) :
    koopmanL2 σ hσ (operator hp hq f) = operator hp hq (koopmanL2 τ hτ f) :=
  congrArg (fun L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν => L f)
    (intertwines hp hq hτ hσ hpc hqc)

def differenceKoopmanIsometry :
    rangeClosure (operator hp hq) →ₗᵢ[ℝ] rangeClosure (operator hp hq) where
  toLinearMap := (restrictToRangeClosure (operator hp hq)
    (koopmanL2 τ hτ) (koopmanL2 σ hσ)
    (symmetry_intertwines hp hq τ σ hτ hσ hpc hqc)).toLinearMap
  norm_map' f := koopmanL2_norm σ hσ (f : Lp ℝ 2 ν)

@[simp] theorem differenceKoopmanIsometry_apply_coe
    (f : rangeClosure (operator hp hq)) :
    (differenceKoopmanIsometry hp hq τ σ hτ hσ hpc hqc f : Lp ℝ 2 ν) =
      koopmanL2 σ hσ f := rfl

theorem differenceKoopmanIsometry_involutive (hinv : Function.Involutive σ) :
    Function.Involutive (differenceKoopmanIsometry hp hq τ σ hτ hσ hpc hqc) := by
  intro f
  apply Subtype.ext
  exact koopmanL2_involutive σ hσ hinv f

def differenceKoopmanEquiv (hinv : Function.Involutive σ) :
    rangeClosure (operator hp hq) ≃ₗᵢ[ℝ] rangeClosure (operator hp hq) :=
  LinearIsometryEquiv.ofSurjective
    (differenceKoopmanIsometry hp hq τ σ hτ hσ hpc hqc)
    (differenceKoopmanIsometry_involutive hp hq τ σ hτ hσ hpc hqc hinv).surjective

@[simp] theorem differenceKoopmanEquiv_apply_coe (hinv : Function.Involutive σ)
    (f : rangeClosure (operator hp hq)) :
    (differenceKoopmanEquiv hp hq τ σ hτ hσ hpc hqc hinv f : Lp ℝ 2 ν) =
      koopmanL2 σ hσ f := rfl

theorem differenceKoopmanEquiv_involutive (hinv : Function.Involutive σ) :
    Function.Involutive (differenceKoopmanEquiv hp hq τ σ hτ hσ hpc hqc hinv) :=
  differenceKoopmanIsometry_involutive hp hq τ σ hτ hσ hpc hqc hinv

theorem neighborAverage_differenceKoopmanEquiv {d : ℕ}
    (τ : Fin d → A → A) (σ : Fin d → B → B)
    (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hσ : ∀ i, MeasurePreserving (σ i) ν ν)
    (hpc : ∀ i, p ∘ σ i = τ i ∘ p) (hqc : ∀ i, q ∘ σ i = τ i ∘ q)
    (hinv : ∀ i, Function.Involutive (σ i)) :
    ColoredEdgeLifts.neighborAverage
        (fun i => differenceKoopmanEquiv hp hq (τ i) (σ i) (hτ i) (hσ i)
          (hpc i) (hqc i) (hinv i)) =
      averageOnDifferences hp hq τ σ hτ hσ hpc hqc := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  simp [ColoredEdgeLifts.neighborAverage_apply, averageOnDifferences,
    restrictToRangeClosure, koopmanAverage]

end Problem367.CopyDifference

end

end OAI
