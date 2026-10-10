import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.EuclideanDerivativeBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.SecondVariationSharp

namespace OAI

/-! The Euclidean specialization of the smooth-dependence equations
(Teschl, Theorem 2.10, equations (2.49)--(2.51)). These equations concern the
actual Euclidean-coordinate transition; the estimates are proved here. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set
open scoped ContDiff

/-- The first two variational equations for a transition map. The second
time argument is elapsed time; the first is its initial phase. -/
structure EuclideanVariations (V : ℝ → EuclideanPlane → EuclideanPlane)
    (Ψ : ℝ → ℝ → EuclideanPlane → EuclideanPlane) : Prop where
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

theorem euclidean_first_variation_vector {V : ℝ → EuclideanPlane → EuclideanPlane}
    {Ψ : ℝ → ℝ → EuclideanPlane → EuclideanPlane} (hv : EuclideanVariations V Ψ)
    {K : ℝ} (hb : ∀ a x, ‖fderiv ℝ (V a) x‖ ≤ K)
    (a : ℝ) (x v : EuclideanPlane) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (Ψ a t) x v‖ ≤ ‖v‖ * Real.exp (K * t) := by
  apply first_variation_bound_mul ht
    (fun s _ => (hv.first a x v s).continuousAt.continuousWithinAt)
    (fun s _ => hv.first a x v s)
  · rw [hv.initial]
    simp
  · intro s _
    exact ((fderiv ℝ (V (a + s)) (Ψ a s x)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hb _ _) (norm_nonneg _))

theorem euclidean_first_variation_operator {V : ℝ → EuclideanPlane → EuclideanPlane}
    {Ψ : ℝ → ℝ → EuclideanPlane → EuclideanPlane} (hv : EuclideanVariations V Ψ)
    {K : ℝ} (hb : ∀ a x, ‖fderiv ℝ (V a) x‖ ≤ K)
    (a : ℝ) (x : EuclideanPlane) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (Ψ a t) x‖ ≤ Real.exp (K * t) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro v
  simpa only [mul_comm] using euclidean_first_variation_vector hv hb a x v ht

theorem euclidean_second_variation_vector {V : ℝ → EuclideanPlane → EuclideanPlane}
    {Ψ : ℝ → ℝ → EuclideanPlane → EuclideanPlane} (hv : EuclideanVariations V Ψ)
    {K : ℝ} (hK : 0 < K)
    (hb₁ : ∀ a x, ‖fderiv ℝ (V a) x‖ ≤ K)
    (hb₂ : ∀ a x, ‖fderiv ℝ (fderiv ℝ (V a)) x‖ ≤ K)
    (a : ℝ) (x v w : EuclideanPlane) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (fderiv ℝ (Ψ a t)) x v w‖ ≤
      (‖v‖ * ‖w‖) * (Real.exp (4 * K * t) - Real.exp (2 * K * t)) := by
  apply second_variation_bound_mul hK (mul_nonneg (norm_nonneg v) (norm_nonneg w)) ht
    (fun s _ => (hv.second a x v w s).continuousAt.continuousWithinAt)
    (fun s _ => hv.second a x v w s)
  · rw [hv.initial]
    have he : fderiv ℝ (id : EuclideanPlane → EuclideanPlane) =
        fun _ => ContinuousLinearMap.id ℝ EuclideanPlane := funext fun _ => fderiv_id
    rw [he]
    simp
  · intro s hs
    have hjv := euclidean_first_variation_vector hv hb₁ a x v hs.1
    have hjw := euclidean_first_variation_vector hv hb₁ a x w hs.1
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

theorem euclidean_second_variation_operator {V : ℝ → EuclideanPlane → EuclideanPlane}
    {Ψ : ℝ → ℝ → EuclideanPlane → EuclideanPlane} (hv : EuclideanVariations V Ψ)
    {K : ℝ} (hK : 0 < K)
    (hb₁ : ∀ a x, ‖fderiv ℝ (V a) x‖ ≤ K)
    (hb₂ : ∀ a x, ‖fderiv ℝ (fderiv ℝ (V a)) x‖ ≤ K)
    (a : ℝ) (x : EuclideanPlane) {t : ℝ} (ht : 0 ≤ t) :
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
      euclidean_second_variation_vector hv hK hb₁ hb₂ a x v w ht
    _ = _ := by ring

theorem euclidean_second_variation_sharp_vector {V : ℝ → EuclideanPlane → EuclideanPlane}
    {Ψ : ℝ → ℝ → EuclideanPlane → EuclideanPlane} (hv : EuclideanVariations V Ψ)
    {K : ℝ} (hK : 0 < K)
    (hb₁ : ∀ a x, ‖fderiv ℝ (V a) x‖ ≤ K)
    (hb₂ : ∀ a x, ‖fderiv ℝ (fderiv ℝ (V a)) x‖ ≤ K)
    (a : ℝ) (x v w : EuclideanPlane) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (fderiv ℝ (Ψ a t)) x v w‖ ≤
      (‖v‖ * ‖w‖) * K * t * Real.exp (3 * K * t) := by
  apply second_variation_bound_sharp_mul hK (mul_nonneg (norm_nonneg v) (norm_nonneg w)) ht
    (fun s _ => (hv.second a x v w s).continuousAt.continuousWithinAt)
    (fun s _ => hv.second a x v w s)
  · rw [hv.initial]
    have he : fderiv ℝ (id : EuclideanPlane → EuclideanPlane) =
        fun _ => ContinuousLinearMap.id ℝ EuclideanPlane := funext fun _ => fderiv_id
    rw [he]
    simp
  · intro s hs
    have hjv := euclidean_first_variation_vector hv hb₁ a x v hs.1
    have hjw := euclidean_first_variation_vector hv hb₁ a x w hs.1
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


theorem euclidean_second_variation_sharp_operator {V : ℝ → EuclideanPlane → EuclideanPlane}
    {Ψ : ℝ → ℝ → EuclideanPlane → EuclideanPlane} (hv : EuclideanVariations V Ψ)
    {K : ℝ} (hK : 0 < K)
    (hb₁ : ∀ a x, ‖fderiv ℝ (V a) x‖ ≤ K)
    (hb₂ : ∀ a x, ‖fderiv ℝ (fderiv ℝ (V a)) x‖ ≤ K)
    (a : ℝ) (x : EuclideanPlane) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (fderiv ℝ (Ψ a t)) x‖ ≤ K * t * Real.exp (3 * K * t) := by
  have hq : 0 ≤ K * t * Real.exp (3 * K * t) := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hq
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hq (norm_nonneg v))
  intro w
  calc
    _ ≤ (‖v‖ * ‖w‖) * K * t * Real.exp (3 * K * t) :=
      euclidean_second_variation_sharp_vector hv hK hb₁ hb₂ a x v w ht
    _ = _ := by ring

def euclideanFlowBound (H : FieldExpr) : ℕ := 2 * euclideanVariationCoefficient H

theorem euclidean_quantitative_variations {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) {Ψ : ℝ → ℝ → EuclideanPlane → EuclideanPlane}
    (hv : EuclideanVariations (fun s => euclideanMap (planarSlice H s)) Ψ)
    (a : ℝ) (x : EuclideanPlane) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (Ψ a t) x‖ ≤ Real.exp ((euclideanFlowBound H : ℝ) * t) ∧
      ‖fderiv ℝ (fderiv ℝ (Ψ a t)) x‖ ≤
        Real.exp (2 * (euclideanFlowBound H : ℝ) * t) -
          Real.exp ((euclideanFlowBound H : ℝ) * t) := by
  have hK : (0 : ℝ) < euclideanVariationCoefficient H := by
    have hp := planarVariationCoefficient_pos H
    unfold euclideanVariationCoefficient
    exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hp
  have hb₁ := fun s y => (planar_euclidean_derivative_bounds hH hT s y).1
  have hb₂ := fun s y => (planar_euclidean_derivative_bounds hH hT s y).2
  constructor
  · apply (euclidean_first_variation_operator hv hb₁ a x ht).trans
    apply Real.exp_le_exp.mpr
    simp only [euclideanFlowBound, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  · have h := euclidean_second_variation_operator hv hK hb₁ hb₂ a x ht
    simp only [euclideanFlowBound, Nat.cast_mul, Nat.cast_ofNat]
    rw [show 2 * (2 * (euclideanVariationCoefficient H : ℝ)) * t =
      4 * (euclideanVariationCoefficient H : ℝ) * t by ring]
    exact h

end ForcedComputation

end

end OAI
