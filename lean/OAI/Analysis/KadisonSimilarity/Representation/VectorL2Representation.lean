import OAI.Analysis.KadisonSimilarity.Representation.VectorL2Multiplication
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! The actual unital star representation of continuous scalar functions
on the vector-valued L² space. -/

noncomputable section
namespace KadisonSimilarity.VectorL2
open MeasureTheory
open scoped InnerProductSpace

variable {X H : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem continuousL2Mul_star (f : C(X, ℂ)) :
    continuousL2Mul (H := H) μ (star f) = (continuousL2Mul μ f).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro ξ η
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousL2Mul_ae μ (star f) ξ, continuousL2Mul_ae μ f η] with x hx hy
  rw [hx, hy]
  simp [inner_smul_left, inner_smul_right]

def continuousRepresentation : C(X, ℂ) →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ) where
  toFun := continuousL2Mul μ
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply Lp.ext
    filter_upwards [continuousL2Mul_ae μ 0 ξ, Lp.coeFn_zero H 2 μ] with x hm hz
    change continuousL2Mul μ 0 ξ x = (0 : Lp H 2 μ) x
    rw [hm, hz]
    simp
  map_one' := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply Lp.ext
    filter_upwards [continuousL2Mul_ae μ 1 ξ] with x hm
    rw [hm]
    simp
  map_add' f g := by
    apply ContinuousLinearMap.ext
    intro ξ
    change continuousL2Mul μ (f + g) ξ = continuousL2Mul μ f ξ + continuousL2Mul μ g ξ
    apply Lp.ext
    filter_upwards [continuousL2Mul_ae μ (f + g) ξ, continuousL2Mul_ae μ f ξ,
      continuousL2Mul_ae μ g ξ,
      Lp.coeFn_add (continuousL2Mul μ f ξ) (continuousL2Mul μ g ξ)] with x hfg hf hg ha
    rw [hfg, ha]
    simp only [Pi.add_apply]
    rw [hf, hg, ContinuousMap.add_apply, add_smul]
  map_mul' f g := by
    apply ContinuousLinearMap.ext
    intro ξ
    change continuousL2Mul μ (f * g) ξ = continuousL2Mul μ f (continuousL2Mul μ g ξ)
    apply Lp.ext
    filter_upwards [continuousL2Mul_ae μ (f * g) ξ,
      continuousL2Mul_ae μ f (continuousL2Mul μ g ξ),
      continuousL2Mul_ae μ g ξ] with x hfg hf hg
    rw [hfg, hf, hg, ContinuousMap.mul_apply, mul_smul]
  commutes' z := by
    apply ContinuousLinearMap.ext
    intro ξ
    change continuousL2Mul μ (algebraMap ℂ C(X, ℂ) z) ξ = z • ξ
    apply Lp.ext
    filter_upwards [continuousL2Mul_ae μ (algebraMap ℂ C(X, ℂ) z) ξ,
      Lp.coeFn_smul z ξ] with x hm hz
    rw [hm, hz]
    rfl
  map_star' f := continuousL2Mul_star μ f

end KadisonSimilarity.VectorL2

end

end OAI
