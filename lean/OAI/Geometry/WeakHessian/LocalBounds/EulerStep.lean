import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatSymbol

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology

namespace WeakHessianFunctional

def eulerStep (t s : ℝ) : ℝ := s / (s+t*(1-s))

def eulerApproximation (t : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  eulerStep (t/(2:ℝ)^n) s ^ (2^n:ℕ)

lemma eulerStep_denom_pos {t s : ℝ} (ht : 0 < t) (hs : s ∈ Icc (0:ℝ) 1) :
    0 < s+t*(1-s) := by
  rcases hs.1.eq_or_lt with rfl | hsp
  · simpa using ht
  · exact add_pos_of_pos_of_nonneg hsp (mul_nonneg ht.le (sub_nonneg.mpr hs.2))

lemma eulerStep_nonneg {t s : ℝ} (ht : 0 < t) (hs : s ∈ Icc (0:ℝ) 1) :
    0 ≤ eulerStep t s := div_nonneg hs.1 (eulerStep_denom_pos ht hs).le

lemma eulerStep_le_one {t s : ℝ} (ht : 0 < t) (hs : s ∈ Icc (0:ℝ) 1) :
    eulerStep t s ≤ 1 := by
  rw [eulerStep, div_le_one (eulerStep_denom_pos ht hs)]
  nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hs.2)]

lemma eulerStep_continuousOn {t : ℝ} (ht : 0 < t) :
    ContinuousOn (eulerStep t) (Icc (0:ℝ) 1) := by
  apply continuousOn_id.div (continuousOn_id.add
    (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)))
  intro s hs
  exact (eulerStep_denom_pos ht hs).ne'

lemma eulerStep_of_pos (t : ℝ) {s : ℝ} (hs : 0 < s) :
    eulerStep t s = (1+t*(s⁻¹-1))⁻¹ := by
  rw [eulerStep]
  field_simp

lemma eulerStep_half_sq {t s : ℝ} (ht : 0 < t) (hs : s ∈ Icc (0:ℝ) 1) :
    (eulerStep (t/2) s)^2 ≤ eulerStep t s := by
  rcases hs.1.eq_or_lt with hsz | hsp
  · simp [← hsz, eulerStep]
  rw [eulerStep_of_pos (t/2) hsp, eulerStep_of_pos t hsp, inv_pow]
  have hr : 0 ≤ s⁻¹-1 := by
    have h := (one_le_inv₀ hsp).mpr hs.2
    linarith
  have hp : 0 < 1 + t*(s⁻¹-1) := by positivity
  have hp2 : 0 < (1+(t/2)*(s⁻¹-1))^2 := by positivity
  rw [inv_le_inv₀ hp2 hp]
  nlinarith [sq_nonneg ((t/2)*(s⁻¹-1))]

lemma eulerApproximation_antitone {t s : ℝ} (ht : 0 < t) (hs : s ∈ Icc (0:ℝ) 1) :
    Antitone (fun n => eulerApproximation t n s) := by
  apply antitone_nat_of_succ_le
  intro n
  have hn : 0 < t/(2:ℝ)^n := by positivity
  have H := eulerStep_half_sq hn hs
  have Hp := pow_le_pow_left₀ (sq_nonneg (eulerStep ((t/(2:ℝ)^n)/2) s)) H (2^n)
  dsimp [eulerApproximation]
  rw [pow_succ, ← div_div, Nat.pow_succ, mul_comm (2^n) 2, pow_mul]
  exact Hp

lemma eulerApproximation_tendsto {t s : ℝ} (ht : 0 < t) (hs : s ∈ Icc (0:ℝ) 1) :
    Tendsto (fun n => eulerApproximation t n s) atTop (𝓝 (heatSymbol t s)) := by
  rcases hs.1.eq_or_lt with hsz | hsp
  · simp only [← hsz, eulerApproximation, eulerStep, zero_div,
      zero_pow (pow_ne_zero _ (by norm_num : (2:ℕ) ≠ 0)), heatSymbol_nonpos ht le_rfl]
    exact tendsto_const_nhds
  let a : ℝ := t*(s⁻¹-1)
  have H := (Real.tendsto_one_add_div_pow_exp a).inv₀ (Real.exp_ne_zero a)
  have Hp : Tendsto (fun n : ℕ => (2:ℕ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have He : (Real.exp a)⁻¹ = heatSymbol t s := by
    rw [← Real.exp_neg, heatSymbol_of_pos ht.le hsp]
    congr 1
    dsimp [a]
    simp only [div_eq_mul_inv]
    ring
  rw [He] at H
  convert H.comp Hp using 1
  ext n
  rw [eulerApproximation, eulerStep_of_pos _ hsp]
  simp only [Function.comp_def, Nat.cast_pow, Nat.cast_ofNat, inv_pow]
  congr 2
  dsimp [a]
  ring

lemma eulerApproximation_uniform {t : ℝ} (ht : 0 < t) :
    TendstoUniformlyOn (eulerApproximation t) (heatSymbol t) atTop (Icc (0:ℝ) 1) := by
  apply Antitone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
    (fun n => (eulerStep_continuousOn (by positivity : 0 < t/(2:ℝ)^n)).pow (2^n))
    (fun s hs => eulerApproximation_antitone ht hs) (heatSymbol_continuous t).continuousOn
  exact fun s hs => eulerApproximation_tendsto ht hs

end WeakHessianFunctional

end
end InlinedFile0

end OAI
