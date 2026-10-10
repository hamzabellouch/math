import OAI.Analysis.KadisonSimilarity.Representation.LocalizedL2Bound
import Mathlib.MeasureTheory.Function.ContinuousMapDense

namespace OAI

/-! Continuous scalar multiplication on vector-valued L² spaces. -/

noncomputable section
namespace KadisonSimilarity.VectorL2
open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem continuousL2Mul_memLp (f : C(X, ℂ)) (ξ : Lp H 2 μ) :
    MemLp (fun x => f x • ξ x) 2 μ := by
  apply (Lp.memLp ξ).of_le_mul (c := ‖f‖)
  · exact f.continuous.measurable.aestronglyMeasurable.smul (Lp.aestronglyMeasurable ξ)
  · exact Filter.Eventually.of_forall fun x => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm f x) (norm_nonneg _)

def continuousL2MulVector (f : C(X, ℂ)) (ξ : Lp H 2 μ) : Lp H 2 μ :=
  (continuousL2Mul_memLp μ f ξ).toLp (fun x => f x • ξ x)

theorem continuousL2MulVector_ae (f : C(X, ℂ)) (ξ : Lp H 2 μ) :
    continuousL2MulVector μ f ξ =ᵐ[μ] (fun x => f x • ξ x) := MemLp.coeFn_toLp _

def continuousL2MulLinear (f : C(X, ℂ)) : Lp H 2 μ →ₗ[ℂ] Lp H 2 μ where
  toFun := continuousL2MulVector μ f
  map_add' ξ η := by
    apply Lp.ext
    filter_upwards [continuousL2MulVector_ae μ f (ξ + η),
      continuousL2MulVector_ae μ f ξ, continuousL2MulVector_ae μ f η,
      Lp.coeFn_add ξ η, Lp.coeFn_add (continuousL2MulVector μ f ξ)
        (continuousL2MulVector μ f η)] with x hsum hξ hη hin hout
    rw [hsum, hout]
    simp only [Pi.add_apply]
    rw [hξ, hη, hin]
    simp only [Pi.add_apply, smul_add]
  map_smul' c ξ := by
    apply Lp.ext
    filter_upwards [continuousL2MulVector_ae μ f (c • ξ),
      continuousL2MulVector_ae μ f ξ, Lp.coeFn_smul c ξ,
      Lp.coeFn_smul c (continuousL2MulVector μ f ξ)] with x hsmul hξ hin hout
    change continuousL2MulVector μ f (c • ξ) x = (c • continuousL2MulVector μ f ξ) x
    rw [hsmul, hout]
    simp only [Pi.smul_apply]
    rw [hξ, hin]
    simp only [Pi.smul_apply]
    exact smul_comm _ _ _

theorem continuousL2MulVector_norm (f : C(X, ℂ)) (ξ : Lp H 2 μ) :
    ‖continuousL2MulVector μ f ξ‖ ≤ ‖f‖ * ‖ξ‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [continuousL2MulVector_ae μ f ξ] with x hx
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm f x) (norm_nonneg _)

def continuousL2Mul (f : C(X, ℂ)) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  (continuousL2MulLinear μ f).mkContinuous ‖f‖ (continuousL2MulVector_norm μ f)

theorem continuousL2Mul_ae (f : C(X, ℂ)) (ξ : Lp H 2 μ) :
    continuousL2Mul μ f ξ =ᵐ[μ] (fun x => f x • ξ x) := continuousL2MulVector_ae μ f ξ

end KadisonSimilarity.VectorL2

end

end OAI
