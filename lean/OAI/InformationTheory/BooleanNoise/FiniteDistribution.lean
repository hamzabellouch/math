import OAI.InformationTheory.BooleanNoise.Statement
import OAI.InformationTheory.BooleanNoise.FiniteNoise

namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

def signProbability (v : ℝ) (b : Bool) : ℝ :=
  if b then (1 + v) / 2 else (1 - v) / 2

theorem sum_signProbability (v : ℝ) : (∑ b : Bool, signProbability v b) = 1 := by
  simp only [Fintype.sum_bool, signProbability, Bool.false_eq_true, ite_false, ite_true]
  ring

theorem signProbability_signEncoding (f : Cube n → Bool) (x : Cube n) (b : Bool) :
    signProbability (signEncoding f x) b = if f x = b then 1 else 0 := by
  cases b <;> cases hfx : f x <;> simp [signProbability, signEncoding, hfx]

theorem noiseOperator_signProbability (u : ℝ) (g : Cube n → ℝ) (b : Bool) (x : Cube n) :
    noiseOperator u (fun y => signProbability (g y) b) x =
      signProbability (noiseOperator u g x) b := by
  cases b
  · change noiseOperator u (fun y => (1 - g y) / 2) x = (1 - noiseOperator u g x) / 2
    have hfun : (fun y => (1 - g y) / 2) = (fun y => (1 / 2 : ℝ) * (1 - g y)) := by
      funext y
      ring
    rw [hfun, noiseOperator_smul, noiseOperator_sub, noiseOperator_const]
    ring
  · change noiseOperator u (fun y => (1 + g y) / 2) x = (1 + noiseOperator u g x) / 2
    have hfun : (fun y => (1 + g y) / 2) = (fun y => (1 / 2 : ℝ) * (1 + g y)) := by
      funext y
      ring
    rw [hfun, noiseOperator_smul, noiseOperator_add, noiseOperator_const]
    ring

theorem cubeAverage_signProbability (g : Cube n → ℝ) (b : Bool) :
    cubeAverage (fun x => signProbability (g x) b) = signProbability (cubeAverage g) b := by
  cases b
  · change cubeAverage (fun y => (1 - g y) / 2) = (1 - cubeAverage g) / 2
    have hfun : (fun y => (1 - g y) / 2) = (fun y => (1 / 2 : ℝ) * (1 - g y)) := by
      funext y
      ring
    rw [hfun, cubeAverage_smul, cubeAverage_sub, cubeAverage_const]
    ring
  · change cubeAverage (fun y => (1 + g y) / 2) = (1 + cubeAverage g) / 2
    have hfun : (fun y => (1 + g y) / 2) = (fun y => (1 / 2 : ℝ) * (1 + g y)) := by
      funext y
      ring
    rw [hfun, cubeAverage_smul, cubeAverage_add, cubeAverage_const]
    ring

theorem bitFlipKernel_eq_noiseKernel (ε : ℝ) (x y : Cube n) :
    bitFlipKernel ε x y = noiseKernel (1 - 2 * ε) x y := by
  unfold bitFlipKernel noiseKernel
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> ring

theorem bitFlipKernel_nonneg {ε : ℝ} (hε0 : 0 ≤ ε) (hεhalf : ε ≤ (1 : ℝ) / 2)
    (x y : Cube n) : 0 ≤ bitFlipKernel ε x y := by
  rw [bitFlipKernel_eq_noiseKernel]
  exact noiseKernel_nonneg (by linarith) (by linarith) x y

theorem jointProbability_eq_posterior (ε : ℝ) (f : Cube n → Bool) (b : Bool) (y : Cube n) :
    jointProbability ε f b y =
      signProbability (noiseOperator (1 - 2 * ε) (signEncoding f) y) b / (2 : ℝ) ^ n := by
  have hterm (x : Cube n) :
      (if f x = b then bitFlipKernel ε x y else 0) =
        noiseKernel (1 - 2 * ε) y x * signProbability (signEncoding f x) b := by
    rw [signProbability_signEncoding]
    by_cases h : f x = b
    · simp only [h, ite_true, mul_one, bitFlipKernel_eq_noiseKernel]
      exact noiseKernel_symm _ x y
    · simp [h]
  unfold jointProbability cubeAverage
  simp_rw [hterm]
  change noiseOperator (1 - 2 * ε) (fun x => signProbability (signEncoding f x) b) y /
    (2 : ℝ) ^ n = _
  rw [noiseOperator_signProbability]

theorem functionMarginal_eq_signProbability (ε : ℝ) (f : Cube n → Bool) (b : Bool) :
    functionMarginal ε f b = signProbability (cubeAverage (signEncoding f)) b := by
  unfold functionMarginal
  simp_rw [jointProbability_eq_posterior]
  rw [← Finset.sum_div]
  change cubeAverage (fun y => signProbability (noiseOperator (1 - 2 * ε) (signEncoding f) y) b) = _
  rw [cubeAverage_signProbability, cubeAverage_noiseOperator]

theorem observationMarginal_eq_uniform (ε : ℝ) (f : Cube n → Bool) (y : Cube n) :
    observationMarginal ε f y = 1 / (2 : ℝ) ^ n := by
  unfold observationMarginal
  simp_rw [jointProbability_eq_posterior]
  rw [← Finset.sum_div, sum_signProbability]

theorem observationMarginal_pos (ε : ℝ) (f : Cube n → Bool) (y : Cube n) :
    0 < observationMarginal ε f y := by
  rw [observationMarginal_eq_uniform]
  exact div_pos zero_lt_one (cube_denominator_pos n)

theorem conditionalProbability_eq_signProbability (ε : ℝ) (f : Cube n → Bool)
    (b : Bool) (y : Cube n) :
    jointProbability ε f b y / observationMarginal ε f y =
      signProbability (noiseOperator (1 - 2 * ε) (signEncoding f) y) b := by
  rw [jointProbability_eq_posterior, observationMarginal_eq_uniform]
  field_simp

theorem jointProbability_nonneg (ε : ℝ) (f : Cube n → Bool)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ (1 : ℝ) / 2) (b : Bool) (y : Cube n) :
    0 ≤ jointProbability ε f b y := by
  apply cubeAverage_nonneg
  intro x
  split_ifs
  · exact bitFlipKernel_nonneg hε0 hεhalf x y
  · exact le_refl 0

theorem jointProbability_sum (ε : ℝ) (f : Cube n → Bool) :
    (∑ b : Bool, ∑ y : Cube n, jointProbability ε f b y) = 1 := by
  change (∑ b : Bool, functionMarginal ε f b) = 1
  simp_rw [functionMarginal_eq_signProbability]
  exact sum_signProbability _

end LeanBlast.CourtadeKumar

end

end OAI
