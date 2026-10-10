import OAI.Analysis.ModularTheory.ProjectionExhaustion
import OAI.Analysis.OInfinity.ProjectionCorner
import OAI.Analysis.JiangSu.Model
import OAI.Analysis.TracialSplitting.ChallengeDefinitions

namespace OAI

/-! Actual finite corners and their tracial vector functionals. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def modularFiniteProjectionInCore (S : StandardModularData H) (n : ℕ) :
    (modularCrossedProduct (volume : Measure ℝ) S).toStarSubalgebra :=
  ⟨modularFiniteProjection n, modularFiniteProjection_mem S n⟩

lemma modularFiniteProjectionInCore_star (S : StandardModularData H) (n : ℕ) :
    star (modularFiniteProjectionInCore S n) = modularFiniteProjectionInCore S n := by
  apply Subtype.ext
  exact (modularFiniteProjection_isStarProjection (H := H) n).isSelfAdjoint.star_eq

lemma modularFiniteProjectionInCore_mul (S : StandardModularData H) (n : ℕ) :
    modularFiniteProjectionInCore S n * modularFiniteProjectionInCore S n =
      modularFiniteProjectionInCore S n := by
  apply Subtype.ext
  exact (modularFiniteProjection_isStarProjection (H := H) n).isIdempotentElem.eq

abbrev ModularFiniteCorner (S : StandardModularData H) (n : ℕ) :=
  ProjectionCorner (modularFiniteProjectionInCore S n)
    (modularFiniteProjectionInCore_star S n) (modularFiniteProjectionInCore_mul S n)

def modularFiniteCornerRepresentation (S : StandardModularData H) (n : ℕ) :
    ModularFiniteCorner S n →⋆ₙₐ[ℂ]
      (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) :=
  (modularCrossedProduct (volume : Measure ℝ) S).toStarSubalgebra.subtype.toNonUnitalStarAlgHom.comp
    (projectionCornerInclusion _ _ _)

lemma modularFiniteCornerRepresentation_mem (S : StandardModularData H) (n : ℕ)
    (a : ModularFiniteCorner S n) :
    modularFiniteCornerRepresentation S n a ∈ modularCrossedProduct (volume : Measure ℝ) S :=
  a.val.property

lemma modularFiniteCornerRepresentation_right (S : StandardModularData H) (n : ℕ)
    (a : ModularFiniteCorner S n) :
    modularFiniteCornerRepresentation S n a * modularFiniteProjection n =
      modularFiniteCornerRepresentation S n a := congrArg Subtype.val a.property.2

lemma modularFiniteCornerRepresentation_left (S : StandardModularData H) (n : ℕ)
    (a : ModularFiniteCorner S n) :
    modularFiniteProjection n * modularFiniteCornerRepresentation S n a =
      modularFiniteCornerRepresentation S n a := congrArg Subtype.val a.property.1

def modularFiniteCornerFunctional (S : StandardModularData H) (n : ℕ) :
    ModularFiniteCorner S n →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun a := inner ℂ (modularCoreWeightVector S n)
        (modularFiniteCornerRepresentation S n a (modularCoreWeightVector S n))
      map_add' a b := by simp only [map_add, add_apply, inner_add_right]
      map_smul' c a := by simp only [map_smul, smul_apply, inner_smul_right,
        RingHom.id_apply, smul_eq_mul] }
    (fun a ha => (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (map_nonneg (modularFiniteCornerRepresentation S n) ha)).inner_nonneg_right _)

private lemma representation_square_inner {A K : Type*} [CStarAlgebra A]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (v : K) (a : A) :
    inner ℂ v (π (star a * a) v) = (‖π a v‖ ^ 2 : ℝ) := by
  rw [map_mul, map_star]
  change inner ℂ v ((π a).adjoint (π a v)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  simp only [Complex.ofReal_pow]
  rfl

lemma modularFiniteCornerFunctional_square (S : StandardModularData H) (n : ℕ)
    (a : ModularFiniteCorner S n) :
    modularFiniteCornerFunctional S n (star a * a) =
      (‖modularFiniteCornerRepresentation S n a (modularCoreWeightVector S n)‖ ^ 2 : ℝ) := by
  exact representation_square_inner (modularFiniteCornerRepresentation S n)
    (modularCoreWeightVector S n) a

theorem modularFiniteCornerFunctional_tracial (S : StandardModularData H) (n : ℕ)
    (a b : ModularFiniteCorner S n) :
    modularFiniteCornerFunctional S n (a * b) = modularFiniteCornerFunctional S n (b * a) := by
  apply NonunitalGamma.ExtendedTraceExtension.linearMap_tracial_of_star_mul
    (modularFiniteCornerFunctional S n).toLinearMap _ a b
  intro x
  have hn := modularCore_finite_corner_adjoint_norm S n
    (modularFiniteCornerRepresentation S n x)
    (modularFiniteCornerRepresentation_mem S n x)
    (modularFiniteCornerRepresentation_right S n x)
    (modularFiniteCornerRepresentation_left S n x)
  calc
    modularFiniteCornerFunctional S n (star x * x) =
        (‖modularFiniteCornerRepresentation S n x (modularCoreWeightVector S n)‖ ^ 2 : ℝ) :=
      modularFiniteCornerFunctional_square S n x
    _ = (‖star (modularFiniteCornerRepresentation S n x) (modularCoreWeightVector S n)‖ ^ 2 : ℝ) := by
      exact congrArg (fun r : ℝ => (r : ℂ)) hn.symm
    _ = modularFiniteCornerFunctional S n (x * star x) := by
      simpa only [map_star, star_star] using (modularFiniteCornerFunctional_square S n (star x)).symm

lemma modularFiniteCornerFunctional_one (S : StandardModularData H) (n : ℕ) :
    modularFiniteCornerFunctional S n 1 = (‖modularCoreWeightVector S n‖ ^ 2 : ℝ) := by
  change inner ℂ (modularCoreWeightVector S n)
    (modularFiniteProjection n (modularCoreWeightVector S n)) = _
  rw [modularFiniteProjection_weightVector S n n le_rfl, inner_self_eq_norm_sq_to_K]
  simp only [Complex.ofReal_pow]
  rfl

lemma modularWeightCutoffVector_succ_ne_zero (n : ℕ) :
    modularWeightCutoffVector (n + 1) ≠ 0 := by
  intro hz
  have ha : modularWeightCutoffFunction (n + 1) =ᵐ[volume] (0 : ℝ → ℂ) :=
    (modularWeightCutoffVector_ae (n + 1)).symm.trans (by
      rw [hz]
      exact Lp.coeFn_zero ℂ 2 volume)
  have hnull : volume (Icc (-(n + 1 : ℝ)) (n + 1)) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ha] with t ht hmem
    have he : (Real.exp (Real.pi * t) : ℂ) = 0 := by
      simpa only [modularWeightCutoffFunction, Nat.cast_add, Nat.cast_one,
        Set.indicator_of_mem hmem, Pi.zero_apply] using ht
    exact (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) he
  rw [Real.volume_Icc, ENNReal.ofReal_eq_zero] at hnull
  linarith [Nat.cast_nonneg (α := ℝ) n]

lemma modularCoreWeightVector_succ_ne_zero (S : StandardModularData H) (n : ℕ) :
    modularCoreWeightVector S (n + 1) ≠ 0 := by
  intro hz
  apply modularWeightCutoffVector_succ_ne_zero n
  apply (modularFourierInclusion S).injective
  change modularFourierInclusion S (modularWeightCutoffVector (n + 1)) = 0 at hz
  simpa only [map_zero] using hz

end WeakPureInfiniteness

end

end OAI
