import OAI.MeasureTheory.Falconer.Shells.PositiveSuffix
import OAI.MeasureTheory.Falconer.Geometry.BinEstimates

namespace OAI

/-! # The scalar far kernel in the actual positive states

The one-dimensional bin estimate is applied to the two original tested
pair-distance laws. Both use the same profile normalization at the child
scale. No angular symbol is removed before this positive comparison.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

 theorem real_bin_kernel_le_max_collision (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {w : ℝ} (hw : 0 < w) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/w)^2) ∂μ.prod ν) ≤
      PlanarFalconer.binKernelConstant *
        max ((μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w})
          ((ν.prod ν) {z : ℝ × ℝ | |z.1-z.2| ≤ w}) := by
  have hb (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
      PlanarFalconer.binL2Norm ρ w ≤
        ((ρ.prod ρ) {z : ℝ × ℝ | |z.1-z.2| ≤ w})^(1/2:ℝ) := by
    have h := PlanarFalconer.real_bin_collision_bound ρ hw
    rw [← PlanarFalconer.binL2Norm_mul_self] at h
    have hh := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 1/2)
    rw [← pow_two,← ENNReal.rpow_two,← ENNReal.rpow_mul] at hh
    norm_num at hh
    exact hh
  apply (PlanarFalconer.real_bin_decaying_kernel_bound μ ν hw).trans
  apply mul_le_mul' le_rfl
  have hprod := mul_le_mul' (hb μ) (hb ν)
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)] at hprod
  apply hprod.trans
  have hh := ENNReal.rpow_le_rpow (mul_le_mul'
    (le_max_left ((μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w})
      ((ν.prod ν) {z : ℝ × ℝ | |z.1-z.2| ≤ w}))
    (le_max_right ((μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w})
      ((ν.prod ν) {z : ℝ × ℝ | |z.1-z.2| ≤ w})))
    (by norm_num : (0:ℝ) ≤ 1/2)
  rw [← pow_two,← ENNReal.rpow_two,← ENNReal.rpow_mul] at hh
  norm_num at hh
  exact le_max_iff.mpr hh

 theorem positiveCollision_kernel_max {d : ℕ}
    (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (A : ℕ → ℝ) (N : ℕ) (σ : ℝ) (J i q a t : ℕ)
    (X Y X' Y' : List (Fin d → Bool)) :
    ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a)) *
      (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+(2:ℝ)^t*|z.1-z.2|)^2)
        ∂(testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
          (policyTestPairs w₀ Q ρ m A N σ J i q a t)).prod
        (testedCellDistance ρ ρ (Q.descendant X') (Q.descendant Y')
          (policyTestPairs w₀ Q ρ m A N σ J i q a t))) ≤
      PlanarFalconer.binKernelConstant *
        max (positiveCollisionCount w₀ Q ρ m A N σ J i q a t X Y)
          (positiveCollisionCount w₀ Q ρ m A N σ J i q a t X' Y') := by
  let μ := testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
    (policyTestPairs w₀ Q ρ m A N σ J i q a t)
  let ν := testedCellDistance ρ ρ (Q.descendant X') (Q.descendant Y')
    (policyTestPairs w₀ Q ρ m A N σ J i q a t)
  let C : ℝ≥0∞ := ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a))
  have hw : 0 < 1/(2:ℝ)^t := by positivity
  have hh := real_bin_kernel_le_max_collision μ ν hw
  have he (z : ℝ × ℝ) : |z.1-z.2|/(1/(2:ℝ)^t) = (2:ℝ)^t*|z.1-z.2| := by
    simp only [one_div,div_inv_eq_mul,mul_comm]
  simp_rw [he] at hh
  have hwC : 1/(2:ℝ)^t ≤ (100*((d:ℝ)+1))/(2:ℝ)^t := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hμ : (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ 1/(2:ℝ)^t} ≤
      (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ (100*((d:ℝ)+1))/(2:ℝ)^t} :=
    measure_mono (fun _ hz => hz.trans hwC)
  have hν : (ν.prod ν) {z : ℝ × ℝ | |z.1-z.2| ≤ 1/(2:ℝ)^t} ≤
      (ν.prod ν) {z : ℝ × ℝ | |z.1-z.2| ≤ (100*((d:ℝ)+1))/(2:ℝ)^t} :=
    measure_mono (fun _ hz => hz.trans hwC)
  have h := mul_le_mul' (show C ≤ C from le_rfl)
    (hh.trans (mul_le_mul' le_rfl (max_le_max hμ hν)))
  change C * _ ≤ _
  apply h.trans_eq
  simp only [positiveCollisionCount,← mul_max,μ,ν,C]
  ring

end Falconer

end OAI
