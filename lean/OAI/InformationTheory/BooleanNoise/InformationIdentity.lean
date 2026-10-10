import OAI.InformationTheory.BooleanNoise.FiniteInformation
import OAI.InformationTheory.BooleanNoise.FiniteDistribution
import OAI.InformationTheory.BooleanNoise.EntropyScalars

namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem sum_xlogx_signProbability (v : ℝ) :
    (∑ b : Bool, xlogx (signProbability v b)) = -entropy v := by
  rw [entropy_eq_binEntropy]
  have hhalf : 1 - (1 + v) / 2 = (1 - v) / 2 := by ring
  simp only [Fintype.sum_bool, signProbability, Bool.false_eq_true, ite_false, ite_true]
  rw [Real.binEntropy, hhalf]
  simp only [Real.log_inv, xlogx]
  ring

theorem binaryEntropy_eq_binEntropy (ε : ℝ) :
    binaryEntropy ε = Real.binEntropy ε / ell := by
  unfold binaryEntropy xlogx Real.binEntropy
  simp only [Real.log_inv]
  ring

theorem one_sub_binaryEntropy_eq_psi (ε : ℝ) :
    1 - binaryEntropy ε = psi (1 - 2 * ε) / ell := by
  rw [binaryEntropy_eq_binEntropy]
  have h := entropy_eq_binEntropy (1 - 2 * ε)
  rw [show (1 + (1 - 2 * ε)) / 2 = 1 - ε by ring, Real.binEntropy_one_sub] at h
  rw [← h]
  unfold entropy
  field_simp [ne_of_gt ell_pos]
  ring

theorem joint_xlogx_sum_bool (ε : ℝ) (f : Cube n → Bool) (y : Cube n) :
    (∑ b : Bool, xlogx (jointProbability ε f b y)) =
      xlogx (((2 : ℝ) ^ n)⁻¹) -
        entropy (noiseOperator (1 - 2 * ε) (signEncoding f) y) / (2 : ℝ) ^ n := by
  simp_rw [jointProbability_eq_posterior, div_eq_mul_inv, xlogx_mul]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    sum_signProbability, sum_xlogx_signProbability]
  ring

theorem joint_xlogx_sum (ε : ℝ) (f : Cube n → Bool) :
    (∑ b : Bool, ∑ y : Cube n, xlogx (jointProbability ε f b y)) =
      (2 : ℝ) ^ n * xlogx (((2 : ℝ) ^ n)⁻¹) -
        entropyAverage (noiseOperator (1 - 2 * ε) (signEncoding f)) := by
  rw [Finset.sum_comm]
  simp_rw [joint_xlogx_sum_bool]
  simp [Finset.sum_sub_distrib, entropyAverage, cubeAverage, Finset.sum_div]

theorem functionMarginal_xlogx_sum (ε : ℝ) (f : Cube n → Bool) :
    (∑ b : Bool, xlogx (functionMarginal ε f b)) =
      -entropy (cubeAverage (signEncoding f)) := by
  simp_rw [functionMarginal_eq_signProbability]
  exact sum_xlogx_signProbability _

theorem observationMarginal_xlogx_sum (ε : ℝ) (f : Cube n → Bool) :
    (∑ y : Cube n, xlogx (observationMarginal ε f y)) =
      (2 : ℝ) ^ n * xlogx (((2 : ℝ) ^ n)⁻¹) := by
  simp [observationMarginal_eq_uniform, one_div]

theorem mutualInformation_eq_informationDeficit (ε : ℝ) (f : Cube n → Bool)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ (1 : ℝ) / 2) :
    mutualInformation ε f =
      informationDeficit (noiseOperator (1 - 2 * ε) (signEncoding f)) / ell := by
  unfold mutualInformation functionMarginal observationMarginal
  rw [finite_kl_eq_entropy_sums (jointProbability ε f)
    (jointProbability_nonneg ε f hε0 hεhalf)]
  change ((∑ b : Bool, ∑ y : Cube n, xlogx (jointProbability ε f b y)) -
    (∑ b : Bool, xlogx (functionMarginal ε f b)) -
    (∑ y : Cube n, xlogx (observationMarginal ε f y))) / ell = _
  rw [joint_xlogx_sum, functionMarginal_xlogx_sum, observationMarginal_xlogx_sum]
  unfold informationDeficit
  rw [cubeAverage_noiseOperator]
  ring

theorem mutualInformation_nats (ε : ℝ) (f : Cube n → Bool)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ (1 : ℝ) / 2) :
    ell * mutualInformation ε f =
      informationDeficit (noiseOperator (1 - 2 * ε) (signEncoding f)) := by
  rw [mutualInformation_eq_informationDeficit ε f hε0 hεhalf]
  field_simp [ne_of_gt ell_pos]

theorem mutualInformation_nats_eq_entropy (ε : ℝ) (f : Cube n → Bool)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ (1 : ℝ) / 2) :
    ell * mutualInformation ε f = entropy (cubeAverage (signEncoding f)) -
      entropyAverage (noiseOperator (1 - 2 * ε) (signEncoding f)) := by
  rw [mutualInformation_nats ε f hε0 hεhalf]
  unfold informationDeficit
  rw [cubeAverage_noiseOperator]

theorem mutualInformation_nats_eq_psi (ε : ℝ) (f : Cube n → Bool)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ (1 : ℝ) / 2) :
    ell * mutualInformation ε f =
      cubeAverage (fun x => psi (noiseOperator (1 - 2 * ε) (signEncoding f) x)) -
        psi (cubeAverage (signEncoding f)) := by
  rw [mutualInformation_nats_eq_entropy ε f hε0 hεhalf]
  unfold entropyAverage entropy
  rw [cubeAverage_sub, cubeAverage_const]
  ring

end LeanBlast.CourtadeKumar

end

end OAI
