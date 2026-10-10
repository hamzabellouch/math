import OAI.Probability.SLE.Mass.MassUniquenessSeparation
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Finite-variation estimates for the smooth separator on time partitions. -/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SLEExactGauge

def massPartitionRemainder (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  massSeparationTest (x N)-massSeparationTest (x 0) -
    ∑ i ∈ Finset.range N, massSeparationSlope (x i)*(x (i+1)-x i)

lemma massPartitionRemainder_eq_sum (x : ℕ → ℝ) (N : ℕ) :
    massPartitionRemainder x N = ∑ i ∈ Finset.range N,
      (massSeparationTest (x (i+1))-massSeparationTest (x i)-
        massSeparationSlope (x i)*(x (i+1)-x i)) := by
  rw [Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun i => massSeparationTest (x i)) N]
  rfl

lemma massPartitionRemainder_linear (x : ℕ → ℝ) (N : ℕ) :
    |massPartitionRemainder x N| ≤ 4*∑ i ∈ Finset.range N, |x (i+1)-x i| := by
  rw [massPartitionRemainder_eq_sum,Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun i _ => massSeparationTest_remainder_linear (x i) (x (i+1))))

lemma massPartitionRemainder_small (x : ℕ → ℝ) (N : ℕ) {ε : ℝ}
    (hx : ∀ i < N, |x (i+1)-x i| ≤ ε) :
    |massPartitionRemainder x N| ≤ (8*ε)*∑ i ∈ Finset.range N, |x (i+1)-x i| := by
  rw [massPartitionRemainder_eq_sum,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  exact (massSeparationTest_remainder_le (x i) (x (i+1))).trans (by
    rw [pow_two,mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hx i (Finset.mem_range.mp hi)) (abs_nonneg _)) (by norm_num))

lemma massDifference_partition_variation (A B : ℕ → ℝ)
    (hA : Monotone A) (hB : Monotone B) (N : ℕ) :
    (∑ i ∈ Finset.range N, |(A (i+1)-B (i+1))-(A i-B i)|) ≤
      (A N-A 0)+(B N-B 0) := by
  calc
    _ ≤ ∑ i ∈ Finset.range N, ((A (i+1)-A i)+(B (i+1)-B i)) := by
      apply Finset.sum_le_sum
      intro i _
      have hAi : 0 ≤ A (i+1)-A i := sub_nonneg.mpr (hA (Nat.le_succ i))
      have hBi : 0 ≤ B (i+1)-B i := sub_nonneg.mpr (hB (Nat.le_succ i))
      calc
        _ = |(A (i+1)-A i)-(B (i+1)-B i)| := by congr 1; ring
        _ ≤ |A (i+1)-A i|+|B (i+1)-B i| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg hAi,abs_of_nonneg hBi]
    _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_range_sub,Finset.sum_range_sub]

lemma massPartitionRemainder_tendsto_zero
    (x : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hvar : ∀ n, (∑ i ∈ Finset.range (N n), |x n (i+1)-x n i|) ≤ D)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i < N n, |x n (i+1)-x n i| ≤ ε) :
    Tendsto (fun n => massPartitionRemainder (x n) (N n)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε/(16*(D+1))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp (hsmall η hη)
  refine ⟨n₀,fun n hn => ?_⟩
  rw [Real.dist_eq,sub_zero]
  calc
    _ ≤ (8*η)*∑ i ∈ Finset.range (N n), |x n (i+1)-x n i| :=
      massPartitionRemainder_small (x n) (N n) (hn₀ n hn)
    _ ≤ (8*η)*D := mul_le_mul_of_nonneg_left (hvar n) (by positivity)
    _ < ε := by
      dsimp only [η]
      have hpos : 0 < D+1 := by linarith
      rw [show 8*(ε/(16*(D+1)))*D = (8*ε*D)/(16*(D+1)) by ring]
      apply (div_lt_iff₀ (by positivity : 0 < 16*(D+1))).mpr
      nlinarith

end SLEExactGauge

end

end OAI
