import OAI.Geometry.SurfaceImmersion.Correction.SupportedFreeLinearity
import OAI.Geometry.Immersion.ClosedSurface.MeanDifferences

namespace OAI

/-! The actual zero-phase metric error is bilinear in the free seeds. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial

variable {n : ℕ} {K : Compacts Base}

def seedMeanError (τ : ℝ)
    (T : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Ambient n) K)
    (V W : SupportedField (F := Ambient n) K) (v w p : Base) : ℝ :=
  QuadraticMean.zeroPair (gradientAmplitude τ (T V) v p) (gradientAmplitude τ (T W) w p) -
    QuadraticMean.zeroPair (leadingDerivative τ V v p) (leadingDerivative τ W w p)

lemma seedMeanError_sub_left (τ : ℝ)
    (T : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Ambient n) K)
    (V W Z : SupportedField (F := Ambient n) K) (v w p : Base) :
    seedMeanError τ T (V - W) Z v w p =
      seedMeanError τ T V Z v w p - seedMeanError τ T W Z v w p := by
  have he : ((T (V - W)) : Field n) = fun x => T V x - T W x := by
    rw [map_sub]
    rfl
  simp only [seedMeanError, he]
  change QuadraticMean.zeroPair (gradientAmplitude τ (fun x => T V x - T W x) v p)
      (gradientAmplitude τ (T Z) w p) -
      QuadraticMean.zeroPair (leadingDerivative τ (fun x => V x - W x) v p) (leadingDerivative τ Z w p) = _
  rw [gradientAmplitude_sub τ ((T V).contDiff.differentiable (by simp) p)
    ((T W).contDiff.differentiable (by simp) p), leadingDerivative_sub,
    QuadraticMean.zeroPair_sub_left, QuadraticMean.zeroPair_sub_left]
  ring

lemma seedMeanError_sub_right (τ : ℝ)
    (T : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Ambient n) K)
    (V W Z : SupportedField (F := Ambient n) K) (v w p : Base) :
    seedMeanError τ T Z (V - W) v w p =
      seedMeanError τ T Z V v w p - seedMeanError τ T Z W v w p := by
  have he : ((T (V - W)) : Field n) = fun x => T V x - T W x := by
    rw [map_sub]
    rfl
  simp only [seedMeanError, he]
  change QuadraticMean.zeroPair (gradientAmplitude τ (T Z) v p)
      (gradientAmplitude τ (fun x => T V x - T W x) w p) -
      QuadraticMean.zeroPair (leadingDerivative τ Z v p) (leadingDerivative τ (fun x => V x - W x) w p) = _
  rw [gradientAmplitude_sub τ ((T V).contDiff.differentiable (by simp) p)
    ((T W).contDiff.differentiable (by simp) p), leadingDerivative_sub,
    QuadraticMean.zeroPair_sub_right, QuadraticMean.zeroPair_sub_right]
  ring

lemma seedMeanError_difference (τ : ℝ)
    (T : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Ambient n) K)
    (V W : SupportedField (F := Ambient n) K) (v w p : Base) :
    seedMeanError τ T V V v w p - seedMeanError τ T W W v w p =
      seedMeanError τ T (V - W) V v w p + seedMeanError τ T W (V - W) v w p := by
  rw [seedMeanError_sub_left, seedMeanError_sub_right]
  ring

lemma seedMeanError_smooth (τ : ℝ)
    (T : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Ambient n) K)
    (V W : SupportedField (F := Ambient n) K) (v w : Base) :
    ContDiff ℝ ∞ (seedMeanError τ T V W v w) := by
  apply contDiffOn_univ.mp
  exact (QuadraticMean.contDiffOn_zeroPair
    (contDiffOn_gradientAmplitude isOpen_univ (T V).contDiff.contDiffOn τ v)
    (contDiffOn_gradientAmplitude isOpen_univ (T W).contDiff.contDiffOn τ w)).sub
    (QuadraticMean.contDiffOn_zeroPair (contDiffOn_leadingDerivative τ V.contDiff.contDiffOn v)
      (contDiffOn_leadingDerivative τ W.contDiff.contDiffOn w))

end ClosedSurfaceR4.SmallModes

end

end OAI
