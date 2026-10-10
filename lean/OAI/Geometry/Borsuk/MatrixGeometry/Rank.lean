import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.MatrixKernel

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section RankOne
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [DecidableEq ν] [Nonempty ν] in
lemma Admissible.lift_smul {f : E → ι → ℝ} (hf : Admissible f) (v : E) (t : ℝ) :
    homogeneousLift f (t • v) = t ^ 2 • homogeneousLift f v := by
  rcases le_total 0 t with ht | ht
  · exact homogeneousLift_smul_nonneg f v ht
  · have h := homogeneousLift_smul_nonneg f v (neg_nonneg.mpr ht)
    rw [neg_smul, hf.lift_even, neg_sq] at h
    exact h

noncomputable def rankOne (u : E) : Matrix ν ν ℝ := fun i j => u i * u j

omit [Nonempty ν] in
lemma rankOne_action (u x : E) : op (rankOne u) x = ⟪u, x⟫ • u := by
  ext i
  change ∑ j, (u i * u j) * x j = ⟪u, x⟫ * u i
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  simp only [mul_comm]

omit [DecidableEq ν] [Nonempty ν] in
lemma rankOne_nonneg (u : E) : 0 ≤ rankOne u := by
  apply Matrix.nonneg_iff_posSemidef.mpr
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp [rankOne, Matrix.conjTranspose_apply, mul_comm]
  · intro x
    have he : star x ⬝ᵥ (rankOne u) *ᵥ x = (∑ i, u i * x i) ^ 2 := by
      simp only [dotProduct, Matrix.mulVec, rankOne, Pi.star_apply, star_trivial]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      simp_rw [← mul_assoc, mul_comm (x _) (u _)]
      rw [← Finset.sum_mul, pow_two]
    rw [he]
    exact sq_nonneg _

omit [DecidableEq ν] [Nonempty ν] in
lemma rankOne_trace (u : E) : Matrix.trace (rankOne u) = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [Matrix.trace, Matrix.diag, rankOne, pow_two]

omit [Nonempty ν] in
lemma rankOne_mul_self (u : E) (hu : ‖u‖ = 1) : rankOne u * rankOne u = rankOne u := by
  apply (op).injective
  rw [map_mul]
  apply ContinuousLinearMap.ext
  intro x
  change op (rankOne u) (op (rankOne u) x) = op (rankOne u) x
  simp only [rankOne_action, inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]

omit [Nonempty ν] in
lemma rankOne_sqrt (u : E) (hu : ‖u‖ = 1) : CFC.sqrt (rankOne u) = rankOne u :=
  (CFC.sqrt_eq_iff _ _ (rankOne_nonneg u) (rankOne_nonneg u)).mpr
    (rankOne_mul_self u hu)

lemma Admissible.positiveExtension_rankOne {f : E → ι → ℝ} (hf : Admissible f)
    (u : E) (hu : ‖u‖ = 1) : positiveExtension f (rankOne u) = f u := by
  have hcoord (x : UnitSphere E) (i : ι) :
      homogeneousLift f (op (rankOne u) x) i = ⟪u, (x : E)⟫ ^ 2 * f u i := by
    rw [rankOne_action, hf.lift_smul, homogeneousLift_unit f hu]
    rfl
  have hm : (Fintype.card ν : ℝ) *
      ∫ x : UnitSphere E, ⟪u, (x : E)⟫ ^ 2 ∂sphereProbability E = 1 := by
    have hs := hf.positiveExtension_sum (rankOne_nonneg u)
    rw [rankOne_trace, hu, one_pow] at hs
    simp only [positiveExtension, rankOne_sqrt u hu, integralLift] at hs
    simp_rw [hcoord] at hs
    simp only [integral_mul_const, ← Finset.mul_sum] at hs
    rw [hf.sum_one u hu, mul_one] at hs
    exact hs
  ext i
  simp only [positiveExtension, rankOne_sqrt u hu, integralLift]
  simp_rw [hcoord]
  rw [integral_mul_const, ← mul_assoc, hm, one_mul]

end RankOne

end BorsukNine

end OAI
