import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteExponential
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateProfile

namespace OAI

/-! The literal finite coordinate boxes are bounded by rational certificates. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimaryBoxBound (n : ℕ) : ℝ :=
  match n with
  | 4 => (20167/2500000:ℝ)
  | 7 => (8523/5000000:ℝ)
  | 13 => (843/5000000:ℝ)
  | 16 => (651/10000000:ℝ)
  | 19 => (11/400000:ℝ)
  | 25 => (59/10000000:ℝ)
  | 28 => (29/10000000:ℝ)
  | 31 => (3/2000000:ℝ)
  | 37 => (1/2000000:ℝ)
  | 43 => (1/5000000:ℝ)
  | 49 => (1/10000000:ℝ)
  | 52 => (1/10000000:ℝ)
  | 61 => (1/10000000:ℝ)
  | 64 => (1/10000000:ℝ)
  | 67 => (1/10000000:ℝ)
  | 73 => (1/10000000:ℝ)
  | 76 => (1/10000000:ℝ)
  | 79 => (1/10000000:ℝ)
  | 91 => (1/10000000:ℝ)
  | 97 => (1/10000000:ℝ)
  | 100 => (1/10000000:ℝ)
  | 103 => (1/10000000:ℝ)
  | 127 => (1/10000000:ℝ)
  | 133 => (1/10000000:ℝ)
  | 139 => (1/10000000:ℝ)
  | 148 => (1/10000000:ℝ)
  | 151 => (1/10000000:ℝ)
  | 193 => (1/10000000:ℝ)
  | 196 => (1/10000000:ℝ)
  | 217 => (1/10000000:ℝ)
  | 271 => (1/10000000:ℝ)
  | _ => 0

def cubicThetaPrimaryBoxWeight (p : CubicThetaIntegerPoint) : ℝ :=
  if p=(0,0) then 0 else
    let n : ℕ := ((1+3*p.1)^2-(1+3*p.1)*(3*p.2)+(3*p.2)^2).toNat
    (n:ℝ)*cubicThetaPrimaryBoxBound n

lemma cubicThetaPrimaryBox_point (p : CubicThetaIntegerPoint)
    (hp : p∈cubicThetaIntegerBox 3) :
    (if p=(0,0) then 0 else cubicThetaPrimaryTailMass p)≤cubicThetaPrimaryBoxWeight p := by
  rcases p with ⟨i,j⟩
  have hr := (cubicThetaIntegerBox_mem (i,j) 3).mp hp
  have hi : -3 ≤ i ∧ i ≤ 3 := by unfold cubicThetaIntegerRadius at hr; omega
  have hj : -3 ≤ j ∧ j ≤ 3 := by unfold cubicThetaIntegerRadius at hr; omega
  rcases hi with ⟨hilo,hihi⟩
  rcases hj with ⟨hjlo,hjhi⟩
  interval_cases i <;> interval_cases j
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_73 (by norm_num : (0:ℝ)≤73) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_52 (by norm_num : (0:ℝ)≤52) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_49 (by norm_num : (0:ℝ)≤49) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_64 (by norm_num : (0:ℝ)≤64) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_97 (by norm_num : (0:ℝ)≤97) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_148 (by norm_num : (0:ℝ)≤148) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_217 (by norm_num : (0:ℝ)≤217) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_61 (by norm_num : (0:ℝ)≤61) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_31 (by norm_num : (0:ℝ)≤31) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_19 (by norm_num : (0:ℝ)≤19) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_25 (by norm_num : (0:ℝ)≤25) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_49 (by norm_num : (0:ℝ)≤49) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_91 (by norm_num : (0:ℝ)≤91) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_151 (by norm_num : (0:ℝ)≤151) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_67 (by norm_num : (0:ℝ)≤67) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_28 (by norm_num : (0:ℝ)≤28) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_7 (by norm_num : (0:ℝ)≤7) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_4 (by norm_num : (0:ℝ)≤4) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_19 (by norm_num : (0:ℝ)≤19) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_52 (by norm_num : (0:ℝ)≤52) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_103 (by norm_num : (0:ℝ)≤103) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_91 (by norm_num : (0:ℝ)≤91) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_43 (by norm_num : (0:ℝ)≤43) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_13 (by norm_num : (0:ℝ)≤13) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · norm_num [cubicThetaPrimaryBoxWeight]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_7 (by norm_num : (0:ℝ)≤7) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_31 (by norm_num : (0:ℝ)≤31) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_73 (by norm_num : (0:ℝ)≤73) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_133 (by norm_num : (0:ℝ)≤133) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_76 (by norm_num : (0:ℝ)≤76) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_37 (by norm_num : (0:ℝ)≤37) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_16 (by norm_num : (0:ℝ)≤16) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_13 (by norm_num : (0:ℝ)≤13) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_28 (by norm_num : (0:ℝ)≤28) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_61 (by norm_num : (0:ℝ)≤61) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_193 (by norm_num : (0:ℝ)≤193) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_127 (by norm_num : (0:ℝ)≤127) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_79 (by norm_num : (0:ℝ)≤79) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_49 (by norm_num : (0:ℝ)≤49) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_37 (by norm_num : (0:ℝ)≤37) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_43 (by norm_num : (0:ℝ)≤43) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_67 (by norm_num : (0:ℝ)≤67) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_271 (by norm_num : (0:ℝ)≤271) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_196 (by norm_num : (0:ℝ)≤196) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_139 (by norm_num : (0:ℝ)≤139) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_100 (by norm_num : (0:ℝ)≤100) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_79 (by norm_num : (0:ℝ)≤79) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_76 (by norm_num : (0:ℝ)≤76) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_primary_exp_91 (by norm_num : (0:ℝ)≤91) using 1 <;>
      norm_num [cubicThetaPrimaryTailMass,cubicThetaPrimaryQuadratic,cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]

lemma cubicThetaPrimaryBox_finite :
    cubicThetaIntegerBox 3=({-3, -2, -1, 0, 1, 2, 3}:Finset ℤ).product {-3, -2, -1, 0, 1, 2, 3} := by
  unfold cubicThetaIntegerBox
  have h : Finset.Icc (-(3:ℤ)) 3={-3, -2, -1, 0, 1, 2, 3} := by decide
  simpa only [Nat.cast_ofNat] using congrArg₂ Finset.product h h


lemma cubicThetaPrimaryBox_sum :
    (∑ p∈cubicThetaIntegerBox 3,if p=(0,0) then 0 else cubicThetaPrimaryTailMass p)≤(8/125:ℝ) := by
  apply (Finset.sum_le_sum (fun p hp => cubicThetaPrimaryBox_point p hp)).trans
  rw [cubicThetaPrimaryBox_finite,Finset.product_eq_sprod,Finset.sum_product]
  norm_num [cubicThetaPrimaryBoxWeight,cubicThetaPrimaryBoxBound]

def cubicThetaRamifiedBoxBound (n : ℕ) : ℝ :=
  match n with
  | 1 => (28407/40000000:ℝ)
  | 3 => (3521/1000000000:ℝ)
  | 4 => (101/200000000:ℝ)
  | 7 => (1/200000000:ℝ)
  | 12 => (1/1000000000:ℝ)
  | _ => 0

def cubicThetaRamifiedBoxWeight (p : CubicThetaIntegerPoint) : ℝ :=
  if p=(0,0) then 0 else
    let n : ℕ := (p.1^2-p.1*p.2+p.2^2).toNat
    (n:ℝ)*cubicThetaRamifiedBoxBound n

lemma cubicThetaRamifiedBox_point (p : CubicThetaIntegerPoint)
    (hp : p∈cubicThetaIntegerBox 2) :
    (if p=(0,0) then 0 else cubicThetaRamifiedTailMass p)≤cubicThetaRamifiedBoxWeight p := by
  rcases p with ⟨i,j⟩
  have hr := (cubicThetaIntegerBox_mem (i,j) 2).mp hp
  have hi : -2 ≤ i ∧ i ≤ 2 := by unfold cubicThetaIntegerRadius at hr; omega
  have hj : -2 ≤ j ∧ j ≤ 2 := by unfold cubicThetaIntegerRadius at hr; omega
  rcases hi with ⟨hilo,hihi⟩
  rcases hj with ⟨hjlo,hjhi⟩
  interval_cases i <;> interval_cases j
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_4 (by norm_num : (0:ℝ)≤4) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_3 (by norm_num : (0:ℝ)≤3) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_4 (by norm_num : (0:ℝ)≤4) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_7 (by norm_num : (0:ℝ)≤7) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_12 (by norm_num : (0:ℝ)≤12) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_3 (by norm_num : (0:ℝ)≤3) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_1 (by norm_num : (0:ℝ)≤1) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_1 (by norm_num : (0:ℝ)≤1) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_3 (by norm_num : (0:ℝ)≤3) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_7 (by norm_num : (0:ℝ)≤7) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_4 (by norm_num : (0:ℝ)≤4) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_1 (by norm_num : (0:ℝ)≤1) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · norm_num [cubicThetaRamifiedBoxWeight]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_1 (by norm_num : (0:ℝ)≤1) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_4 (by norm_num : (0:ℝ)≤4) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_7 (by norm_num : (0:ℝ)≤7) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_3 (by norm_num : (0:ℝ)≤3) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_1 (by norm_num : (0:ℝ)≤1) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_1 (by norm_num : (0:ℝ)≤1) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_3 (by norm_num : (0:ℝ)≤3) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_12 (by norm_num : (0:ℝ)≤12) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_7 (by norm_num : (0:ℝ)≤7) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_4 (by norm_num : (0:ℝ)≤4) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_3 (by norm_num : (0:ℝ)≤3) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]
  · convert mul_le_mul_of_nonneg_left cubic_ramified_exp_4 (by norm_num : (0:ℝ)≤4) using 1 <;>
      norm_num [cubicThetaRamifiedTailMass,cubicThetaIntegerQuadratic,cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]

lemma cubicThetaRamifiedBox_finite :
    cubicThetaIntegerBox 2=({-2, -1, 0, 1, 2}:Finset ℤ).product {-2, -1, 0, 1, 2} := by
  unfold cubicThetaIntegerBox
  have h : Finset.Icc (-(2:ℤ)) 2={-2, -1, 0, 1, 2} := by decide
  simpa only [Nat.cast_ofNat] using congrArg₂ Finset.product h h


lemma cubicThetaRamifiedBox_sum :
    (∑ p∈cubicThetaIntegerBox 2,if p=(0,0) then 0 else cubicThetaRamifiedTailMass p)≤(11/2500:ℝ) := by
  apply (Finset.sum_le_sum (fun p hp => cubicThetaRamifiedBox_point p hp)).trans
  rw [cubicThetaRamifiedBox_finite,Finset.product_eq_sprod,Finset.sum_product]
  norm_num [cubicThetaRamifiedBoxWeight,cubicThetaRamifiedBoxBound]

end CubicFirstMoment

end

end OAI
