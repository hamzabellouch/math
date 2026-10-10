import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothExponentialCurve
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieProductDifferential
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # Products of exponential curves

Coordinates of the second kind require only smoothness of each individual
one-parameter subgroup. Their differential at zero is the sum of the
specified tangent vectors.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

def exponentialProduct (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) :
    {n : ℕ} → (Fin n → E) → (Fin n → ℝ) → G
  | 0, _, _ => 1
  | _ + 1, v, x => Exp (x 0 • v 0) * exponentialProduct Exp (v ∘ Fin.succ) (x ∘ Fin.succ)

def tangentCombination {n : ℕ} (v : Fin n → E) :
    (Fin n → ℝ) →L[ℝ] E :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (v i)

@[simp] theorem tangentCombination_apply {n : ℕ}
    (v : Fin n → E) (x : Fin n → ℝ) :
    tangentCombination v x = ∑ i, x i • v i := by
  simp only [tangentCombination, sum_apply]
  rfl

def coordinateTail (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

@[simp] theorem coordinateTail_apply (n : ℕ) (x : Fin (n + 1) → ℝ) :
    coordinateTail n x = x ∘ Fin.succ := rfl

theorem tangentCombination_succ {n : ℕ}
    (v : Fin (n + 1) → E) :
    ((1 : ℝ →L[ℝ] ℝ).smulRight (v 0)).comp
        (ContinuousLinearMap.proj (0 : Fin (n + 1))) +
      (tangentCombination (E := E) (v ∘ Fin.succ)).comp (coordinateTail n) =
      tangentCombination (E := E) v := by
  ext x
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    tangentCombination_apply, coordinateTail_apply]
  change x 0 • v 0 + ∑ i : Fin n, x i.succ • v i.succ =
    ∑ i : Fin (n + 1), x i • v i
  rw [Fin.sum_univ_succ]

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] in
theorem IsGroupExponential.exponentialProduct_zero
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {n : ℕ} (v : Fin n → E) :
    exponentialProduct Exp v 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Exp ((0 : ℝ) • v 0) * exponentialProduct Exp (v ∘ Fin.succ) 0 = 1
    rw [zero_smul, ih, mul_one]
    exact hExp.map_zero

theorem IsGroupExponential.contMDiff_exponentialProduct
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {n : ℕ} (v : Fin n → E) :
    ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, E)) ∞ (exponentialProduct Exp v) := by
  induction n with
  | zero => exact contMDiff_const
  | succ n ih =>
    have hhead := (hExp.contMDiff_curve (v 0)).comp
      (ContinuousLinearMap.proj (0 : Fin (n + 1)) : (Fin (n + 1) → ℝ) →L[ℝ] ℝ).contDiff.contMDiff
    have htail := (ih (v ∘ Fin.succ)).comp (coordinateTail n).contDiff.contMDiff
    exact hhead.mul htail

theorem IsGroupExponential.hasMFDerivAt_exponentialProduct_zero
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {n : ℕ} (v : Fin n → E) :
    HasMFDerivAt (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, E))
      (exponentialProduct Exp v) 0 (tangentCombination (E := E) v) := by
  induction n with
  | zero =>
    apply (hasMFDerivAt_const (I := 𝓘(ℝ, Fin 0 → ℝ)) (I' := 𝓘(ℝ, E))
      (1 : G) (0 : Fin 0 → ℝ)).congr_mfderiv
    change (0 : (Fin 0 → ℝ) →L[ℝ] E) = tangentCombination (E := E) v
    simp [tangentCombination]
  | succ n ih =>
    have hhead := (hExp.hasMFDerivAt_zero (v 0)).comp (0 : Fin (n + 1) → ℝ)
      (ContinuousLinearMap.proj (0 : Fin (n + 1)) :
        (Fin (n + 1) → ℝ) →L[ℝ] ℝ).hasFDerivAt.hasMFDerivAt
    have htail := (ih (v ∘ Fin.succ)).comp (0 : Fin (n + 1) → ℝ)
      (coordinateTail n).hasFDerivAt.hasMFDerivAt
    have hp := PolycyclicRecognition.HasMFDerivAt.mul_at_one hhead htail (by
      change Exp ((0 : ℝ) • v 0) = 1
      rw [zero_smul]
      exact hExp.map_zero)
      (by simpa using hExp.exponentialProduct_zero (v ∘ Fin.succ))
    apply hp.congr_mfderiv
    exact tangentCombination_succ v

end PolycyclicRecognition

end

end OAI
