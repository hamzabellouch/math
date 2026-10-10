import OAI.Analysis.KadisonKastler.ResolventContinuousCalculus
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! # A cyclic spectral isometry for the bounded resolvent

Continuous spectral functions are dense in the scalar L2 space. Their
functional-calculus vectors have exactly the same norm, so the map
extends to an isometry into the original Hilbert space.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev ResolventCyclicL2 (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :=
  Lp ℂ 2 (resolventVectorMeasure R hR x)

theorem resolventContinuousVector_norm_L2 (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (f : C(spectrum ℝ R, ℂ)) :
    ‖resolventContinuousVector R hR x f‖ =
      ‖ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ f‖ := by
  let μ := resolventVectorMeasure R hR x
  let v : ResolventCyclicL2 R hR x := ContinuousMap.toLp 2 μ ℂ f
  have hi := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def (𝕜 := ℂ) v v)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) v v)] at hi
  simp only [inner_self_eq_norm_sq] at hi
  have he : (∫ s, ‖v s‖ ^ 2 ∂μ) = ∫ s, ‖f s‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ f] with s hs
    rw [show v s = f s from hs]
  rw [he] at hi
  have hn := resolventContinuousVector_norm_sq R hR x f
  change ‖resolventContinuousVector R hR x f‖ = ‖v‖
  nlinarith [norm_nonneg (resolventContinuousVector R hR x f), norm_nonneg v]

def resolventCyclicIsometry (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :
    ResolventCyclicL2 R hR x →ₗᵢ[ℂ] H :=
  (resolventContinuousVector R hR x).extendOfIsometry
    (e := (ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ).toLinearMap)
    (ContinuousMap.toLp_denseRange ℂ (p := 2) (resolventVectorMeasure R hR x) ℂ (by norm_num))
    (resolventContinuousVector_norm_L2 R hR x)

theorem resolventCyclicIsometry_continuous (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (f : C(spectrum ℝ R, ℂ)) :
    resolventCyclicIsometry R hR x (ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ f) =
      resolventContinuousCalculus R hR f x :=
  LinearMap.extendOfIsometry_eq _ _ _ f

theorem resolventCyclicIsometry_one (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H) :
    resolventCyclicIsometry R hR x
      (ContinuousMap.toLp 2 (resolventVectorMeasure R hR x) ℂ (1 : C(spectrum ℝ R, ℂ))) = x := by
  rw [resolventCyclicIsometry_continuous, map_one, one_apply_eq_self]

end

end KadisonKastler

end OAI
