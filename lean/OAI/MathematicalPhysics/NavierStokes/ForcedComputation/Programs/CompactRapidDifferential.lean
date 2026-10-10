import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.CompactRapidEmbedding

namespace OAI

/-! The similarity has length scale 1/8.  Thus viscosity 64ν before the
similarity gives viscosity ν afterwards.  All identities are proved directly
from the coordinate derivatives used in the rapid construction. -/

noncomputable section
open Set
open scoped BigOperators
namespace RapidForcing.CompactEmbedding

theorem spatialD_field {u : Field Space} {t : ℝ}
    (hu : Differentiable ℝ (u t)) (i : Fin 3) (x : Space) :
    spatialD i (field u) t x = (8 * coordinateSign i) •
      linear (spatialD i u t (unembed x)) := by
  have hd := linear.hasFDerivAt.comp x
    ((hu (unembed x)).hasFDerivAt.comp x (unembed_hasFDerivAt x))
  simp only [Function.comp_def] at hd
  change fderiv ℝ (fun y => linear (u t (unembed y))) x (basis i) = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, inverseLinear_basis, map_smul, spatialD]

theorem divergence_field {u : Field Space} {t : ℝ}
    (hu : Differentiable ℝ (u t)) (x : Space) :
    divergence (field u) t x = divergence u t (unembed x) := by
  unfold divergence
  apply Finset.sum_congr rfl
  intro i _
  rw [spatialD_field hu, PiLp.smul_apply, linear_apply]
  by_cases hi : i = 0
  all_goals simp [coordinateSign, hi]
  all_goals ring

theorem advection_field {u : Field Space} {t : ℝ}
    (hu : Differentiable ℝ (u t)) (x : Space) :
    advection (field u) t x = linear (advection u t (unembed x)) := by
  unfold advection
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [spatialD_field hu, field, linear_apply, smul_smul, map_smul]
  congr 1
  by_cases hi : i = 0 <;> simp [coordinateSign, hi] <;> ring

theorem spatialD_const_smul {u : Field Space} {t : ℝ}
    (hu : Differentiable ℝ (u t)) (a : ℝ) (i : Fin 3) (x : Space) :
    spatialD i (fun t x => a • u t x) t x = a • spatialD i u t x := by
  change fderiv ℝ (a • u t) x (basis i) = _
  rw [((hu x).hasFDerivAt.const_smul a).fderiv]
  rfl

theorem spatialD_field_differentiable {u : Field Space} {t : ℝ}
    (hu : Differentiable ℝ (u t)) : Differentiable ℝ (field u t) :=
  linear.differentiable.comp (hu.comp (unembed_contDiff.differentiable (by simp)))

theorem spatialD_twice_field {u : Field Space} {t : ℝ}
    (hu : Differentiable ℝ (u t))
    (hdu : ∀ i, Differentiable ℝ (spatialD i u t)) (i : Fin 3) (x : Space) :
    spatialD i (spatialD i (field u)) t x =
      (64 : ℝ) • linear (spatialD i (spatialD i u) t (unembed x)) := by
  have he : spatialD i (field u) t =
      fun y => (8 * coordinateSign i) • field (spatialD i u) t y := by
    funext y
    exact spatialD_field hu i y
  change fderiv ℝ (spatialD i (field u) t) x (basis i) = _
  rw [he]
  change spatialD i (fun s y => (8 * coordinateSign i) • field (spatialD i u) s y) t x = _
  rw [spatialD_const_smul (spatialD_field_differentiable (hdu i)),
    spatialD_field (hdu i), smul_smul]
  congr 1
  by_cases hi : i = 0 <;> norm_num [coordinateSign, hi]

theorem laplace_field {u : Field Space} {t : ℝ}
    (hu : Differentiable ℝ (u t))
    (hdu : ∀ i, Differentiable ℝ (spatialD i u t)) (x : Space) :
    laplace (field u) t x = (64 : ℝ) • linear (laplace u t (unembed x)) := by
  unfold laplace
  rw [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => spatialD_twice_field hu hdu i x)

theorem timeD_field {u : Field Space} {t : ℝ} (ht : 0 ≤ t) (x : Space)
    (hu : DifferentiableWithinAt ℝ (fun s => u s (unembed x)) (Ici 0) t) :
    timeD (field u) t x = linear (timeD u t (unembed x)) := by
  have hd := linear.hasFDerivAt.comp_hasDerivWithinAt t hu.hasDerivWithinAt
  exact hd.derivWithin (uniqueDiffOn_Ici 0 t ht)

theorem residual_field {u : Field Space} {t : ℝ} (ht : 0 ≤ t)
    (hu : Differentiable ℝ (u t))
    (hdu : ∀ i, Differentiable ℝ (spatialD i u t))
    (htime : ∀ x, DifferentiableWithinAt ℝ (fun s => u s x) (Ici 0) t)
    (ν : ℝ) (x : Space) :
    residual ν (field u) t x = linear (residual (64 * ν) u t (unembed x)) := by
  unfold residual
  rw [timeD_field ht x (htime _), advection_field hu, laplace_field hu hdu,
    map_sub, map_add, map_smul, smul_smul]
  congr 1
  congr 1
  ring

theorem navierStokes_field {u f : Field Space} (ν : ℝ)
    (hNS : NavierStokes (64 * ν) f u (fun _ _ => 0))
    (hu : ∀ t, 0 ≤ t → Differentiable ℝ (u t))
    (hdu : ∀ t, 0 ≤ t → ∀ i, Differentiable ℝ (spatialD i u t))
    (htime : ∀ t, 0 ≤ t → ∀ x,
      DifferentiableWithinAt ℝ (fun s => u s x) (Ici 0) t) :
    NavierStokes ν (field f) (field u) (fun _ _ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht x
    have hres : residual (64 * ν) u t (unembed x) = f t (unembed x) := by
      have he := hNS.1 t ht (unembed x)
      simp [gradient, spatialD] at he
      unfold residual
      rw [he]
      abel
    have he := residual_field ht (hu t ht) (hdu t ht) (htime t ht) ν x
    rw [hres] at he
    change timeD (field u) t x + advection (field u) t x = _
    simp only [gradient, spatialD, fderiv_const_apply, zero_apply,
      zero_smul, Finset.sum_const_zero, neg_zero, zero_add]
    change timeD (field u) t x + advection (field u) t x =
      ν • laplace (field u) t x + linear (f t (unembed x))
    unfold residual at he
    rw [← he]
    abel
  · intro t ht x
    rw [divergence_field (hu t ht)]
    exact hNS.2.1 t ht (unembed x)
  · intro x
    simp [field, hNS.2.2]

end RapidForcing.CompactEmbedding

end

end OAI
