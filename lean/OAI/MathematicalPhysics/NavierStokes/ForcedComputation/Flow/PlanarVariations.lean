import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarDerivativeBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.VariationBounds

namespace OAI

/-! The variational equations used for the planar quantitative estimates.
The regularity input is the finite-dimensional smooth-dependence theorem:
Teschl, Ordinary Differential Equations and Dynamical Systems (2012),
Theorem 2.10, equations (2.49)--(2.51). The quantitative estimates follow
from these equations by Gronwall inequalities. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set
open scoped ContDiff

/-- The first two variational equations for a transition map. The second
time argument is elapsed time; the first is its initial phase. -/
structure PlanarVariations (V : ℝ → Plane → Plane)
    (Ψ : ℝ → ℝ → Plane → Plane) : Prop where
  initial : ∀ a, Ψ a 0 = id
  smooth : ∀ a t, ContDiff ℝ ∞ (Ψ a t)
  first : ∀ a x v t,
    HasDerivAt (fun s => fderiv ℝ (Ψ a s) x v)
      (fderiv ℝ (V (a + t)) (Ψ a t x) (fderiv ℝ (Ψ a t) x v)) t
  second : ∀ a x v w t,
    HasDerivAt (fun s => fderiv ℝ (fderiv ℝ (Ψ a s)) x v w)
      (fderiv ℝ (V (a + t)) (Ψ a t x) (fderiv ℝ (fderiv ℝ (Ψ a t)) x v w) +
        fderiv ℝ (fderiv ℝ (V (a + t))) (Ψ a t x)
          (fderiv ℝ (Ψ a t) x v) (fderiv ℝ (Ψ a t) x w)) t

theorem planar_first_variation_vector {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hv : PlanarVariations V Ψ)
    {K : ℝ} (hb : ∀ a x, ‖fderiv ℝ (V a) x‖ ≤ K)
    (a : ℝ) (x v : Plane) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (Ψ a t) x v‖ ≤ ‖v‖ * Real.exp (K * t) := by
  apply first_variation_bound_mul ht
    (fun s _ => (hv.first a x v s).continuousAt.continuousWithinAt)
    (fun s _ => hv.first a x v s)
  · rw [hv.initial]
    simp
  · intro s _
    exact ((fderiv ℝ (V (a + s)) (Ψ a s x)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hb _ _) (norm_nonneg _))

theorem planar_first_variation_operator {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hv : PlanarVariations V Ψ)
    {K : ℝ} (hb : ∀ a x, ‖fderiv ℝ (V a) x‖ ≤ K)
    (a : ℝ) (x : Plane) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (Ψ a t) x‖ ≤ Real.exp (K * t) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro v
  simpa only [mul_comm] using planar_first_variation_vector hv hb a x v ht

theorem planar_second_variation_vector {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hv : PlanarVariations V Ψ)
    {K : ℝ} (hK : 0 < K)
    (hb₁ : ∀ a x, ‖fderiv ℝ (V a) x‖ ≤ K)
    (hb₂ : ∀ a x, ‖fderiv ℝ (fderiv ℝ (V a)) x‖ ≤ K)
    (a : ℝ) (x v w : Plane) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (fderiv ℝ (Ψ a t)) x v w‖ ≤
      (‖v‖ * ‖w‖) * (Real.exp (4 * K * t) - Real.exp (2 * K * t)) := by
  apply second_variation_bound_mul hK (mul_nonneg (norm_nonneg v) (norm_nonneg w)) ht
    (fun s _ => (hv.second a x v w s).continuousAt.continuousWithinAt)
    (fun s _ => hv.second a x v w s)
  · rw [hv.initial]
    have he : fderiv ℝ (id : Plane → Plane) =
        fun _ => ContinuousLinearMap.id ℝ Plane := funext fun _ => fderiv_id
    rw [he]
    simp
  · intro s hs
    have hjv := planar_first_variation_vector hv hb₁ a x v hs.1
    have hjw := planar_first_variation_vector hv hb₁ a x w hs.1
    have he : Real.exp (K * s) * Real.exp (K * s) = Real.exp (2 * K * s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      ‖fderiv ℝ (V (a + s)) (Ψ a s x) (fderiv ℝ (fderiv ℝ (Ψ a s)) x v w) +
          fderiv ℝ (fderiv ℝ (V (a + s))) (Ψ a s x)
            (fderiv ℝ (Ψ a s) x v) (fderiv ℝ (Ψ a s) x w)‖ ≤
          ‖fderiv ℝ (V (a + s)) (Ψ a s x) (fderiv ℝ (fderiv ℝ (Ψ a s)) x v w)‖ +
          ‖fderiv ℝ (fderiv ℝ (V (a + s))) (Ψ a s x)
            (fderiv ℝ (Ψ a s) x v) (fderiv ℝ (Ψ a s) x w)‖ := norm_add_le _ _
      _ ≤ K * ‖fderiv ℝ (fderiv ℝ (Ψ a s)) x v w‖ +
          K * ‖fderiv ℝ (Ψ a s) x v‖ * ‖fderiv ℝ (Ψ a s) x w‖ := by
        apply add_le_add
        · exact ((fderiv ℝ (V (a + s)) (Ψ a s x)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hb₁ _ _) (norm_nonneg _))
        · exact ((fderiv ℝ (fderiv ℝ (V (a + s))) (Ψ a s x)).le_opNorm₂ _ _).trans
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hb₂ _ _) (norm_nonneg _)) (norm_nonneg _))
      _ ≤ K * ‖fderiv ℝ (fderiv ℝ (Ψ a s)) x v w‖ +
          K * (‖v‖ * Real.exp (K * s)) * (‖w‖ * Real.exp (K * s)) := by
        gcongr
      _ = K * ‖fderiv ℝ (fderiv ℝ (Ψ a s)) x v w‖ +
          (‖v‖ * ‖w‖) * K * Real.exp (2 * K * s) := by
        calc
          _ = K * ‖fderiv ℝ (fderiv ℝ (Ψ a s)) x v w‖ +
              (‖v‖ * ‖w‖) * K * (Real.exp (K * s) * Real.exp (K * s)) := by ring
          _ = _ := by rw [he]

theorem planar_second_variation_operator {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hv : PlanarVariations V Ψ)
    {K : ℝ} (hK : 0 < K)
    (hb₁ : ∀ a x, ‖fderiv ℝ (V a) x‖ ≤ K)
    (hb₂ : ∀ a x, ‖fderiv ℝ (fderiv ℝ (V a)) x‖ ≤ K)
    (a : ℝ) (x : Plane) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (fderiv ℝ (Ψ a t)) x‖ ≤
      Real.exp (4 * K * t) - Real.exp (2 * K * t) := by
  have hq : 0 ≤ Real.exp (4 * K * t) - Real.exp (2 * K * t) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    nlinarith
  apply ContinuousLinearMap.opNorm_le_bound _ hq
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hq (norm_nonneg v))
  intro w
  calc
    _ ≤ (‖v‖ * ‖w‖) * (Real.exp (4 * K * t) - Real.exp (2 * K * t)) :=
      planar_second_variation_vector hv hK hb₁ hb₂ a x v w ht
    _ = _ := by ring

def planarFlowBound (H : FieldExpr) : ℕ := 2 * planarVariationCoefficient H

theorem planar_quantitative_variations {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) {Ψ : ℝ → ℝ → Plane → Plane}
    (hv : PlanarVariations (planarSlice H) Ψ) (a : ℝ) (x : Plane) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖fderiv ℝ (Ψ a t) x‖ ≤ Real.exp ((planarFlowBound H : ℝ) * t) ∧
      ‖fderiv ℝ (fderiv ℝ (Ψ a t)) x‖ ≤
        Real.exp (2 * (planarFlowBound H : ℝ) * t) -
          Real.exp ((planarFlowBound H : ℝ) * t) := by
  have hK : (0 : ℝ) < planarVariationCoefficient H := by
    exact_mod_cast planarVariationCoefficient_pos H
  have hb₁ := fun s y => (planar_derivative_bounds hH hT s y).1
  have hb₂ := fun s y => (planar_derivative_bounds hH hT s y).2
  constructor
  · apply (planar_first_variation_operator hv hb₁ a x ht).trans
    apply Real.exp_le_exp.mpr
    simp only [planarFlowBound, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  · have h := planar_second_variation_operator hv hK hb₁ hb₂ a x ht
    simp only [planarFlowBound, Nat.cast_mul, Nat.cast_ofNat]
    rw [show 2 * (2 * (planarVariationCoefficient H : ℝ)) * t =
      4 * (planarVariationCoefficient H : ℝ) * t by ring]
    exact h

end ForcedComputation

end

end OAI
