import Mathlib
import OAI.Geometry.IntegralFillings.Charts.Quadratic
import OAI.Geometry.IntegralFillings.Differentiation.LocalBounds
import OAI.Geometry.IntegralFillings.Charts.JacobianBound
import OAI.Geometry.IntegralFillings.Charts.CurrentContinuity
import OAI.Geometry.IntegralFillings.Charts.ScalarPieces
import OAI.Geometry.IntegralFillings.Slicing.CycleCoarea
import OAI.Geometry.IntegralFillings.Slicing.GeneralCoarea
import OAI.Geometry.IntegralFillings.Optimality.GoodRadius
import OAI.Geometry.IntegralFillings.Optimality.BallBoundary

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
namespace Optimality

lemma sphereArea_pos (n : ℕ) : 0 < sphereArea n :=
  mul_pos (by positivity) (omega_pos (n+1))

lemma fillingCoefficient_pos (n : ℕ) : 0 < fillingCoefficient n := by
  unfold fillingCoefficient
  exact one_div_pos.mpr (mul_pos (by positivity) (Real.rpow_pos_of_pos (sphereArea_pos n) _))

lemma sharp_ball_identity {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) :
    fillingCoefficient n * (sphereArea n * r^n) ^ fillingPower n = omega (n+1)*r^(n+1) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : fillingPower n = 1 + 1/(n:ℝ) := by unfold fillingPower; field_simp
  have hnp : (n:ℝ)*fillingPower n = ((n+1:ℕ):ℝ) := by
    unfold fillingPower
    push_cast
    field_simp
  rw [Real.mul_rpow (sphereArea_pos n).le (pow_nonneg hr _),
    ← Real.rpow_natCast_mul hr, hnp, Real.rpow_natCast]
  rw [hp, Real.rpow_add (sphereArea_pos n),Real.rpow_one]
  unfold fillingCoefficient
  have hroot : (sphereArea n)^(1/(n:ℝ)) ≠ 0 :=
    (Real.rpow_pos_of_pos (sphereArea_pos n) _).ne'
  have hdn : (n:ℝ)+1 ≠ 0 := by positivity
  calc 1 / (((n:ℝ)+1) * (sphereArea n)^(1/(n:ℝ))) *
        (sphereArea n * (sphereArea n)^(1/(n:ℝ)) * r^(n+1)) =
       (sphereArea n / ((n:ℝ)+1))*r^(n+1) := by field_simp
    _ = omega (n+1)*r^(n+1) := by unfold sphereArea; field_simp

lemma sharp_ball_bound {n : ℕ} (hn : 0 < n) {r m : ℝ} (hr : 0 < r)
    (hm : 0 ≤ m) (hmle : m ≤ sphereArea n*r^n) :
    fillingCoefficient n * m^fillingPower n ≤ omega (n+1)*r^(n+1) := by
  rw [← sharp_ball_identity hn hr.le]
  apply mul_le_mul_of_nonneg_left _ (fillingCoefficient_pos n).le
  apply Real.rpow_le_rpow hm hmle
  unfold fillingPower
  positivity

end Optimality

theorem coefficient_optimal (n : ℕ) (hn : 2 ≤ n) :
    ∃ T : IntegralCurrent (Euc (n + 1)) n,
      CompactlySupported T.val ∧ IsCycle T.val ∧ 0 < mass T.val ∧
      ∀ S : IntegralCurrent (Euc (n + 1)) (n + 1),
        CompactlySupported S.val → boundarySucc S.val = T.val →
        fillingCoefficient n * (mass T.val) ^ fillingPower n ≤ mass S.val := by
  obtain ⟨t,ht,hI,hM⟩ := Optimality.exists_good_inner_ball n
  have hAI := Optimality.ambientBall_integral hI
  let B := Optimality.ambientBall (n+1) t
  let T : IntegralCurrent (Euc (n+1)) n := ⟨boundarySucc B,Optimality.integral_boundary hAI⟩
  refine ⟨T,Optimality.ambientBall_boundary_compact n t hI.2.2.1,
    Optimality.boundary_isCycle hAI.1, Optimality.ambientBall_boundary_mass_pos n ht hAI.2.2.1, ?_⟩
  intro S hSc hSb
  have hmass : mass T.val ≤ sphereArea n * (-t)^n :=
    (Optimality.ambientBall_boundary_mass_le n t hI.2.2.1).trans hM
  calc fillingCoefficient n * mass T.val ^ fillingPower n ≤ omega (n+1)*(-t)^(n+1) :=
      Optimality.sharp_ball_bound (by omega) (neg_pos.mpr ht.2) (mass_nonneg _) hmass
    _ = (volume (Metric.ball (0 : Euc (n+1)) (-t))).toReal :=
      (Optimality.ball_volume_scaling (n+1) (neg_pos.mpr ht.2)).symm
    _ ≤ mass S.val := Optimality.allFillings_mass_ge_ball n ht.1 S.property.1 hSb

end SharpIntegralFillings

end

end OAI
