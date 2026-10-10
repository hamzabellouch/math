import OAI.Analysis.KadisonKastler.WeakFieldNorm
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart

namespace OAI

/-! # Kernel projections of measurable operator fields

Cesàro averages of a positive contraction converge strongly to its kernel
projection. Applied pointwise, this proves measurability of the projection
without using a measurable selection or Borel functional calculus input.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology BigOperators CStarAlgebra

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace WeakOperatorRepresentative

/-- Evaluation is a star algebra homomorphism. -/
def evalHom (x : D) : WeakOperatorRepresentative (H := H) μ →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun F := eval F x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

@[simp] theorem evalHom_apply (x : D) (F : WeakOperatorRepresentative (H := H) μ) :
    evalHom x F = eval F x := rfl


/-- Pointwise equality determines a representative. -/
theorem ext_eval {F G : WeakOperatorRepresentative (H := H) μ}
    (h : ∀ x, eval F x = eval G x) : F = G := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  exact h x.ofTopology

local instance kernelSourceOrder : PartialOrder (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrder _
local instance kernelSourceStarOrder : StarOrderedRing (WeakOperatorRepresentative (H := H) μ) :=
  CStarAlgebra.spectralOrderedRing _
local instance kernelTargetOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance kernelTargetStarOrder : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

private def kernelAverage (F : WeakOperatorRepresentative (H := H) μ) (n : ℕ) :
    WeakOperatorRepresentative (H := H) μ :=
  (n : ℂ)⁻¹ • ∑ i ∈ Finset.range n, (1 - F) ^ i

private theorem norm_positive_complement_le (T : H →L[ℂ] H)
    (hT : 0 ≤ T) (hn : ‖T‖ ≤ 1) : ‖1 - T‖ ≤ 1 :=
  (CStarAlgebra.norm_sub_le_max_of_nonneg
    (show (0 : H →L[ℂ] H) ≤ 1 from zero_le_one) hT).trans
    (max_le (IsStarProjection.norm_le _ (IsStarProjection.one _)) hn)

omit [CompleteSpace H] in
private theorem starProjection_congr (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U = V) :
    U.starProjection = V.starProjection := by
  subst V
  rfl

private theorem operator_kernel_averages_tendsto (T : H →L[ℂ] H)
    (hT : 0 ≤ T) (hn : ‖T‖ ≤ 1) (ξ : H) :
    Tendsto (fun n => birkhoffAverage ℂ ((1 : H →L[ℂ] H) - T) id n ξ) atTop
      (𝓝 (T.ker.starProjection ξ)) := by
  have heq : (1 - T).eqLocus (1 : H →L[ℂ] H) = T.ker := by
    ext η
    change η - T η = η ↔ T η = 0
    simp only [sub_eq_self]
  have ht := (1 - T).tendsto_birkhoffAverage_orthogonalProjection
    (norm_positive_complement_le T hT hn) ξ
  change Tendsto (fun n => birkhoffAverage ℂ ((1 : H →L[ℂ] H) - T) id n ξ) atTop
    (𝓝 (((1 - T).eqLocus (1 : H →L[ℂ] H)).starProjection ξ)) at ht
  rw [starProjection_congr _ _ heq] at ht
  exact ht

private theorem kernelAverage_eval (F : WeakOperatorRepresentative (H := H) μ)
    (x : D) (ξ : H) (n : ℕ) : eval (kernelAverage F n) x ξ =
      birkhoffAverage ℂ ((1 : H →L[ℂ] H) - eval F x) id n ξ := by
  change (evalHom (H := H) (μ := μ) x ((n : ℂ)⁻¹ • ∑ i ∈ Finset.range n, (1 - F) ^ i)) ξ = _
  simp only [birkhoffAverage, birkhoffSum, map_smul, map_sum,
    map_pow, map_sub, map_one, evalHom_apply]
  simp only [smul_apply, sum_apply, FunLike.coe_pow_eq_iterate, id_eq]

private theorem kernelAverage_tendsto (F : WeakOperatorRepresentative (H := H) μ)
    (hF : 0 ≤ F) (hn : ‖F‖ ≤ 1) (x : D) (ξ : H) :
    Tendsto (fun n => eval (kernelAverage F n) x ξ) atTop
      (𝓝 ((eval F x).ker.starProjection ξ)) := by
  have ht := operator_kernel_averages_tendsto (eval F x)
    (map_nonneg (evalHom (H := H) (μ := μ) x) hF) ((eval_norm_le F x).trans hn) ξ
  simpa only [kernelAverage_eval] using ht

/-- Kernel projections of positive contraction fields are measurable. -/
theorem kernel_aestronglyMeasurable (F : WeakOperatorRepresentative (H := H) μ)
    (hF : 0 ≤ F) (hn : ‖F‖ ≤ 1) (ξ : H) :
    AEStronglyMeasurable (fun x => (eval F x).ker.starProjection ξ) μ := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (kernelAverage F n).eval_aestronglyMeasurable ξ)
  exact Eventually.of_forall fun x => kernelAverage_tendsto F hF hn x ξ

/-- The kernel projection is an actual measurable representative. -/
def kernelProjection (F : WeakOperatorRepresentative (H := H) μ)
    (hF : 0 ≤ F) (hn : ‖F‖ ≤ 1) : WeakOperatorRepresentative (H := H) μ :=
  mk (fun x => (eval F x).ker.starProjection) 1
    (fun x => IsStarProjection.norm_le _ (isStarProjection_starProjection (U := (eval F x).ker)))
    (kernel_aestronglyMeasurable F hF hn)
    (fun ξ => by
      have he (x : D) : star ((eval F x).ker.starProjection) = (eval F x).ker.starProjection :=
        (isStarProjection_starProjection (U := (eval F x).ker)).isSelfAdjoint.star_eq
      simpa only [he] using kernel_aestronglyMeasurable F hF hn ξ)

@[simp] theorem eval_kernelProjection (F : WeakOperatorRepresentative (H := H) μ)
    (hF : 0 ≤ F) (hn : ‖F‖ ≤ 1) (x : D) :
    eval (kernelProjection F hF hn) x = (eval F x).ker.starProjection := rfl

/-- Remove the contraction restriction by a positive scalar rescaling. -/
theorem positive_kernel_aestronglyMeasurable (F : WeakOperatorRepresentative (H := H) μ)
    (hF : 0 ≤ F) (ξ : H) :
    AEStronglyMeasurable (fun x => (eval F x).ker.starProjection ξ) μ := by
  let c : ℝ := ‖F‖ + 1
  have hc : 0 < c := by dsimp [c]; positivity
  let G : WeakOperatorRepresentative (H := H) μ := c⁻¹ • F
  have hG : 0 ≤ G := smul_nonneg (inv_nonneg.mpr hc.le) hF
  have hGn : ‖G‖ ≤ 1 := by
    dsimp [G]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    apply (inv_mul_le_iff₀ hc).mpr
    dsimp [c]
    linarith
  have he (x : D) : (eval G x).ker = (eval F x).ker := by
    ext η
    change c⁻¹ • eval F x η = 0 ↔ eval F x η = 0
    simp only [smul_eq_zero, inv_ne_zero hc.ne', false_or]
  simpa only [he] using kernel_aestronglyMeasurable G hG hGn ξ

/-- Kernel projection of a positive measurable field, with no norm restriction. -/
def positiveKernelProjection (F : WeakOperatorRepresentative (H := H) μ)
    (hF : 0 ≤ F) : WeakOperatorRepresentative (H := H) μ :=
  mk (fun x => (eval F x).ker.starProjection) 1
    (fun x => IsStarProjection.norm_le _ (isStarProjection_starProjection (U := (eval F x).ker)))
    (positive_kernel_aestronglyMeasurable F hF)
    (fun ξ => by
      have he (x : D) : star ((eval F x).ker.starProjection) = (eval F x).ker.starProjection :=
        (isStarProjection_starProjection (U := (eval F x).ker)).isSelfAdjoint.star_eq
      simpa only [he] using positive_kernel_aestronglyMeasurable F hF ξ)

@[simp] theorem eval_positiveKernelProjection (F : WeakOperatorRepresentative (H := H) μ)
    (hF : 0 ≤ F) (x : D) :
    eval (positiveKernelProjection F hF) x = (eval F x).ker.starProjection := rfl

/-- The pointwise kernel projection is a projection in the representative algebra. -/
theorem positiveKernelProjection_isStarProjection
    (F : WeakOperatorRepresentative (H := H) μ) (hF : 0 ≤ F) :
    IsStarProjection (positiveKernelProjection F hF) := by
  constructor
  · apply ext_eval
    intro x
    exact (isStarProjection_starProjection (U := (eval F x).ker)).isIdempotentElem.eq
  · apply ext_eval
    intro x
    exact (isStarProjection_starProjection (U := (eval F x).ker)).isSelfAdjoint.star_eq

end WeakOperatorRepresentative

end

end KadisonKastler

end OAI
