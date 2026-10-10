import OAI.Geometry.EinsteinFour.GradientCasimir

namespace OAI

/-! Actual generator commutators on the Bianchi gradient coordinates. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

abbrev RawGradient := Fin 3 → Fin 3 → Vec

def rawMatrixRotation (s : Fin 3) (Z : RawGradient) : RawGradient := fun a b =>
  (∑ c, rotation s a c • Z c b) - ∑ c, rotation s c b • Z a c

def rawGradientGenerator (s : Fin 3) (Z : RawGradient) : RawGradient := fun a b =>
  quaternion s (Z a b) + rawMatrixRotation s Z a b

@[simp] theorem rawMatrixRotation_matrix (s : Fin 3) (Z : Tensor) (a b : Fin 3) :
    rawMatrixRotation s Z.matrix a b = matrixRotation s Z a b := rfl

@[simp] theorem rawGradientGenerator_matrix (s : Fin 3) (Z : Tensor) (a b : Fin 3) :
    rawGradientGenerator s Z.matrix a b = gradientGenerator s Z a b := rfl

theorem rawGradientGenerator_add (s : Fin 3) (Z W : RawGradient) :
    rawGradientGenerator s (Z + W) = rawGradientGenerator s Z + rawGradientGenerator s W := by
  funext a b
  simp only [rawGradientGenerator, rawMatrixRotation, Pi.add_apply,
    quaternion_add, smul_add, Finset.sum_add_distrib]
  module

theorem rawGradientGenerator_smul (s : Fin 3) (r : ℝ) (Z : RawGradient) :
    rawGradientGenerator s (r • Z) = r • rawGradientGenerator s Z := by
  funext a b
  simp only [rawGradientGenerator, rawMatrixRotation, Pi.smul_apply,
    quaternion_smul, smul_smul, mul_comm, Finset.smul_sum, smul_sub, smul_add]

private theorem rawGenerator_commutator_0_0 (Z : RawGradient) (b : Fin 3) :
    rawGradientGenerator 0 (rawGradientGenerator 1 Z) 0 b -
      rawGradientGenerator 1 (rawGradientGenerator 0 Z) 0 b =
        (2 : ℝ) • rawGradientGenerator 2 Z 0 b := by
  ext u
  fin_cases b <;> fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem rawGenerator_commutator_0_1 (Z : RawGradient) (b : Fin 3) :
    rawGradientGenerator 0 (rawGradientGenerator 1 Z) 1 b -
      rawGradientGenerator 1 (rawGradientGenerator 0 Z) 1 b =
        (2 : ℝ) • rawGradientGenerator 2 Z 1 b := by
  ext u
  fin_cases b <;> fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem rawGenerator_commutator_0_2 (Z : RawGradient) (b : Fin 3) :
    rawGradientGenerator 0 (rawGradientGenerator 1 Z) 2 b -
      rawGradientGenerator 1 (rawGradientGenerator 0 Z) 2 b =
        (2 : ℝ) • rawGradientGenerator 2 Z 2 b := by
  ext u
  fin_cases b <;> fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem rawGenerator_commutator_1_0 (Z : RawGradient) (b : Fin 3) :
    rawGradientGenerator 1 (rawGradientGenerator 2 Z) 0 b -
      rawGradientGenerator 2 (rawGradientGenerator 1 Z) 0 b =
        (2 : ℝ) • rawGradientGenerator 0 Z 0 b := by
  ext u
  fin_cases b <;> fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem rawGenerator_commutator_1_1 (Z : RawGradient) (b : Fin 3) :
    rawGradientGenerator 1 (rawGradientGenerator 2 Z) 1 b -
      rawGradientGenerator 2 (rawGradientGenerator 1 Z) 1 b =
        (2 : ℝ) • rawGradientGenerator 0 Z 1 b := by
  ext u
  fin_cases b <;> fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem rawGenerator_commutator_1_2 (Z : RawGradient) (b : Fin 3) :
    rawGradientGenerator 1 (rawGradientGenerator 2 Z) 2 b -
      rawGradientGenerator 2 (rawGradientGenerator 1 Z) 2 b =
        (2 : ℝ) • rawGradientGenerator 0 Z 2 b := by
  ext u
  fin_cases b <;> fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem rawGenerator_commutator_2_0 (Z : RawGradient) (b : Fin 3) :
    rawGradientGenerator 2 (rawGradientGenerator 0 Z) 0 b -
      rawGradientGenerator 0 (rawGradientGenerator 2 Z) 0 b =
        (2 : ℝ) • rawGradientGenerator 1 Z 0 b := by
  ext u
  fin_cases b <;> fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem rawGenerator_commutator_2_1 (Z : RawGradient) (b : Fin 3) :
    rawGradientGenerator 2 (rawGradientGenerator 0 Z) 1 b -
      rawGradientGenerator 0 (rawGradientGenerator 2 Z) 1 b =
        (2 : ℝ) • rawGradientGenerator 1 Z 1 b := by
  ext u
  fin_cases b <;> fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

private theorem rawGenerator_commutator_2_2 (Z : RawGradient) (b : Fin 3) :
    rawGradientGenerator 2 (rawGradientGenerator 0 Z) 2 b -
      rawGradientGenerator 0 (rawGradientGenerator 2 Z) 2 b =
        (2 : ℝ) • rawGradientGenerator 1 Z 2 b := by
  ext u
  fin_cases b <;> fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, rotation, quaternion, Fin.sum_univ_succ]
  all_goals ring

/-- The three actual total generators obey the quaternion rotation bracket. -/
theorem rawGradientGenerator_commutator (s : Fin 3) (Z : RawGradient) :
    rawGradientGenerator s (rawGradientGenerator (next s) Z) -
      rawGradientGenerator (next s) (rawGradientGenerator s Z) =
        (2 : ℝ) • rawGradientGenerator (previous s) Z := by
  funext a b
  fin_cases s <;> fin_cases a
  · exact rawGenerator_commutator_0_0 Z b
  · exact rawGenerator_commutator_0_1 Z b
  · exact rawGenerator_commutator_0_2 Z b
  · exact rawGenerator_commutator_1_0 Z b
  · exact rawGenerator_commutator_1_1 Z b
  · exact rawGenerator_commutator_1_2 Z b
  · exact rawGenerator_commutator_2_0 Z b
  · exact rawGenerator_commutator_2_1 Z b
  · exact rawGenerator_commutator_2_2 Z b

private theorem rawGenerator_casimir_0_0 (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 0 0) =
      (-35 : ℝ) • Z.matrix 0 0 := by
  ext u
  have hc := congrArg (fun v : Vec => v u) (gradientCoupling_eq Z hb 0 0)
  have ht := congrArg (fun v : Vec => v u) hz
  fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, gradientCoupling,
      matrixRotation, rotation, quaternion, Tensor.matrix,
      Fin.sum_univ_succ] at hc ht ⊢
  all_goals first | linear_combination 2 * hc | linear_combination 2 * hc + 8 * ht

private theorem rawGenerator_casimir_0_1 (Z : Tensor)
    (_hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 0 1) =
      (-35 : ℝ) • Z.matrix 0 1 := by
  ext u
  have hc := congrArg (fun v : Vec => v u) (gradientCoupling_eq Z hb 0 1)
  fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, gradientCoupling,
      matrixRotation, rotation, quaternion, Tensor.matrix,
      Fin.sum_univ_succ] at hc ⊢
  all_goals linear_combination 2 * hc

private theorem rawGenerator_casimir_0_2 (Z : Tensor)
    (_hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 0 2) =
      (-35 : ℝ) • Z.matrix 0 2 := by
  ext u
  have hc := congrArg (fun v : Vec => v u) (gradientCoupling_eq Z hb 0 2)
  fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, gradientCoupling,
      matrixRotation, rotation, quaternion, Tensor.matrix,
      Fin.sum_univ_succ] at hc ⊢
  all_goals linear_combination 2 * hc

private theorem rawGenerator_casimir_1_0 (Z : Tensor)
    (_hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 1 0) =
      (-35 : ℝ) • Z.matrix 1 0 := by
  ext u
  have hc := congrArg (fun v : Vec => v u) (gradientCoupling_eq Z hb 1 0)
  fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, gradientCoupling,
      matrixRotation, rotation, quaternion, Tensor.matrix,
      Fin.sum_univ_succ] at hc ⊢
  all_goals linear_combination 2 * hc

private theorem rawGenerator_casimir_1_1 (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 1 1) =
      (-35 : ℝ) • Z.matrix 1 1 := by
  ext u
  have hc := congrArg (fun v : Vec => v u) (gradientCoupling_eq Z hb 1 1)
  have ht := congrArg (fun v : Vec => v u) hz
  fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, gradientCoupling,
      matrixRotation, rotation, quaternion, Tensor.matrix,
      Fin.sum_univ_succ] at hc ht ⊢
  all_goals first | linear_combination 2 * hc | linear_combination 2 * hc + 8 * ht

private theorem rawGenerator_casimir_1_2 (Z : Tensor)
    (_hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 1 2) =
      (-35 : ℝ) • Z.matrix 1 2 := by
  ext u
  have hc := congrArg (fun v : Vec => v u) (gradientCoupling_eq Z hb 1 2)
  fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, gradientCoupling,
      matrixRotation, rotation, quaternion, Tensor.matrix,
      Fin.sum_univ_succ] at hc ⊢
  all_goals linear_combination 2 * hc

private theorem rawGenerator_casimir_2_0 (Z : Tensor)
    (_hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 2 0) =
      (-35 : ℝ) • Z.matrix 2 0 := by
  ext u
  have hc := congrArg (fun v : Vec => v u) (gradientCoupling_eq Z hb 2 0)
  fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, gradientCoupling,
      matrixRotation, rotation, quaternion, Tensor.matrix,
      Fin.sum_univ_succ] at hc ⊢
  all_goals linear_combination 2 * hc

private theorem rawGenerator_casimir_2_1 (Z : Tensor)
    (_hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 2 1) =
      (-35 : ℝ) • Z.matrix 2 1 := by
  ext u
  have hc := congrArg (fun v : Vec => v u) (gradientCoupling_eq Z hb 2 1)
  fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, gradientCoupling,
      matrixRotation, rotation, quaternion, Tensor.matrix,
      Fin.sum_univ_succ] at hc ⊢
  all_goals linear_combination 2 * hc

private theorem rawGenerator_casimir_2_2 (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 2 2) =
      (-35 : ℝ) • Z.matrix 2 2 := by
  ext u
  have hc := congrArg (fun v : Vec => v u) (gradientCoupling_eq Z hb 2 2)
  have ht := congrArg (fun v : Vec => v u) hz
  fin_cases u <;>
    simp [rawGradientGenerator, rawMatrixRotation, gradientCoupling,
      matrixRotation, rotation, quaternion, Tensor.matrix,
      Fin.sum_univ_succ] at hc ht ⊢
  all_goals first | linear_combination 2 * hc | linear_combination 2 * hc + 8 * ht

private theorem rawGenerator_casimir_0 (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) (b : Fin 3) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 0 b) =
      (-35 : ℝ) • Z.matrix 0 b := by
  fin_cases b
  · exact rawGenerator_casimir_0_0 Z hz hb
  · exact rawGenerator_casimir_0_1 Z hz hb
  · exact rawGenerator_casimir_0_2 Z hz hb

private theorem rawGenerator_casimir_1 (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) (b : Fin 3) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 1 b) =
      (-35 : ℝ) • Z.matrix 1 b := by
  fin_cases b
  · exact rawGenerator_casimir_1_0 Z hz hb
  · exact rawGenerator_casimir_1_1 Z hz hb
  · exact rawGenerator_casimir_1_2 Z hz hb

private theorem rawGenerator_casimir_2 (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) (b : Fin 3) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) 2 b) =
      (-35 : ℝ) • Z.matrix 2 b := by
  fin_cases b
  · exact rawGenerator_casimir_2_0 Z hz hb
  · exact rawGenerator_casimir_2_1 Z hz hb
  · exact rawGenerator_casimir_2_2 Z hz hb

/-- The pointwise Casimir identity follows from the actual trace and Bianchi equations. -/
theorem rawGradientGenerator_casimir (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi)
    (a b : Fin 3) :
    (∑ s : Fin 3, rawGradientGenerator s (rawGradientGenerator s Z.matrix) a b) =
      (-35 : ℝ) • Z.matrix a b := by
  fin_cases a
  · exact rawGenerator_casimir_0 Z hz hb b
  · exact rawGenerator_casimir_1 Z hz hb b
  · exact rawGenerator_casimir_2 Z hz hb b

end
end PositiveEinsteinFour.Bianchi

end OAI
