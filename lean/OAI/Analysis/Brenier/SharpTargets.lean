import OAI.Analysis.Brenier.Atomic
import OAI.Analysis.Brenier.Wasserstein

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

/-- The first coordinate used in the sharpness construction. -/
def sharpAxis0 (d : ℕ) (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩

/-- The transverse coordinate used in the sharpness construction. -/
def sharpAxis1 (d : ℕ) (hd : 2 ≤ d) : Fin d := ⟨1, by omega⟩

/-- The two fixed outer slopes and the variable central slope. -/
def sharpAtoms (d : ℕ) (hd : 2 ≤ d) (b : ℝ) : Fin 3 → E d :=
  ![EuclideanSpace.single (sharpAxis0 d hd) (-1),
    EuclideanSpace.single (sharpAxis0 d hd) 1,
    EuclideanSpace.single (sharpAxis1 d hd) b]

/-- All three target masses are independent of the transverse slope. -/
def sharpWeights (a : ℝ) : Fin 3 → ℝ≥0∞ :=
  ![ENNReal.ofReal ((1 - a) / 2), ENNReal.ofReal ((1 - a) / 2), ENNReal.ofReal a]

/-- The common three-atom target family; use `b = 0` and `b = a / 2`. -/
def sharpTarget (d : ℕ) (hd : 2 ≤ d) (a b : ℝ) : Measure (E d) :=
  ∑ i, sharpWeights a i • Measure.dirac (sharpAtoms d hd b i)

lemma sharpAtoms_injective (d : ℕ) (hd : 2 ≤ d) (b : ℝ) :
    Function.Injective (sharpAtoms d hd b) := by
  intro i j h
  have hc := congrArg (fun x : E d => x (sharpAxis0 d hd)) h
  fin_cases i <;> fin_cases j <;>
    first | rfl | norm_num [sharpAtoms, sharpAxis0, sharpAxis1, PiLp.single_apply] at hc

lemma sharpAtoms_mem_cube (d : ℕ) (hd : 2 ≤ d) (b : ℝ)
    (hb : |b| ≤ 1) (i : Fin 3) : sharpAtoms d hd b i ∈ cube d := by
  intro j
  fin_cases i <;> simp [sharpAtoms, PiLp.single_apply] <;> split_ifs <;> simp_all

lemma sharpWeights_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (i : Fin 3) :
    0 < sharpWeights a i := by
  fin_cases i <;> simp [sharpWeights, ENNReal.ofReal_pos] <;> linarith

lemma sharpWeights_sum {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∑ i, sharpWeights a i) = 1 := by
  have hw : 0 ≤ (1 - a) / 2 := by linarith
  rw [Fin.sum_univ_three]
  change ENNReal.ofReal ((1-a)/2) + ENNReal.ofReal ((1-a)/2) + ENNReal.ofReal a = 1
  rw [← ENNReal.ofReal_add hw hw, ← ENNReal.ofReal_add (add_nonneg hw hw) ha]
  have hsum : (1 - a) / 2 + (1 - a) / 2 + a = 1 := by ring
  rw [hsum, ENNReal.ofReal_one]

lemma sharpTarget_hasExactlyThreeAtoms (d : ℕ) (hd : 2 ≤ d) {a b : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : |b| ≤ 1) :
    HasExactlyThreeAtoms (sharpTarget d hd a b) (cube d) := by
  exact ⟨sharpAtoms d hd b, sharpAtoms_injective d hd b,
    sharpAtoms_mem_cube d hd b hb, sharpWeights a,
    sharpWeights_pos ha ha1, sharpWeights_sum ha.le ha1.le, rfl⟩

lemma sharpTarget_isProbabilityMeasure (d : ℕ) (hd : 2 ≤ d) {a : ℝ}
    (b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    IsProbabilityMeasure (sharpTarget d hd a b) := by
  exact finite_atomic_probability (sharpAtoms d hd b) (sharpWeights a)
    (sharpWeights_sum ha ha1)

lemma sharpTarget_isSupported (d : ℕ) (hd : 2 ≤ d) (a b : ℝ)
    (hb : |b| ≤ 1) : IsSupported (sharpTarget d hd a b) (cube d) := by
  exact finite_atomic_supported (sharpAtoms d hd b) (sharpWeights a)
    (sharpAtoms_mem_cube d hd b hb)

/-- The zero atom distinguishes the two sharpness targets. -/
lemma sharpTarget_apply_zero (d : ℕ) (hd : 2 ≤ d) (a b : ℝ) :
    sharpTarget d hd a b {0} = if b = 0 then ENNReal.ofReal a else 0 := by
  classical
  simp [sharpTarget, Fin.sum_univ_three, sharpWeights, sharpAtoms,
    Measure.add_apply, Measure.smul_apply, smul_eq_mul, Pi.single_apply]

lemma sharpTarget_ne (d : ℕ) (hd : 2 ≤ d) {a b : ℝ}
    (ha : 0 < a) (hb : b ≠ 0) :
    sharpTarget d hd a 0 ≠ sharpTarget d hd a b := by
  intro h
  have hm := congrArg (fun μ : Measure (E d) => μ {0}) h
  simp [sharpTarget_apply_zero, hb] at hm
  exact (not_le_of_gt ha) hm

end Problem358

namespace Problem358

/-- All source atoms lie in the transverse zero-coordinate hyperplane. -/
lemma sharpTarget_ae_axis1_zero (d : ℕ) (hd : 2 ≤ d) (a : ℝ) :
    ∀ᵐ x ∂sharpTarget d hd a 0, x (sharpAxis1 d hd) = 0 := by
  unfold sharpTarget
  rw [ae_finsetSum_measure_iff]
  intro i hi
  apply Measure.ae_smul_measure
  have hcoord : sharpAtoms d hd 0 i (sharpAxis1 d hd) = 0 := by
    fin_cases i <;> simp [sharpAtoms, sharpAxis0, sharpAxis1]
  simpa using hcoord

/-- The target's transverse second moment only sees its central atom. -/
lemma sharpTarget_axis1_moment (d : ℕ) (hd : 2 ≤ d) (a b : ℝ) :
    (∫⁻ x, ENNReal.ofReal ((x (sharpAxis1 d hd)) ^ 2)
      ∂sharpTarget d hd a b) = ENNReal.ofReal a * ENNReal.ofReal (b ^ 2) := by
  simp [sharpTarget, Fin.sum_univ_three, sharpWeights, sharpAtoms,
    sharpAxis0, sharpAxis1, lintegral_smul_measure]

/-- The atomwise matching plan changes only the central atom. -/
lemma quadraticPlanCost_sharpMatching (d : ℕ) (hd : 2 ≤ d) (a b : ℝ) :
    quadraticPlanCost (atomicMatchingPlan (sharpWeights a)
      (sharpAtoms d hd 0) (sharpAtoms d hd b)) =
      ENNReal.ofReal a * ENNReal.ofReal (b ^ 2) := by
  have hn : ‖EuclideanSpace.single (sharpAxis1 d hd) (0 : ℝ) -
      EuclideanSpace.single (sharpAxis1 d hd) b‖ ^ 2 = b ^ 2 := by
    rw [← PiLp.single_sub]
    simp [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  rw [quadraticPlanCost_atomicMatchingPlan]
  simp only [Fin.sum_univ_three, sharpWeights, sharpAtoms, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, sub_self,
    norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero,
    mul_zero, zero_add, hn]

/-- Exact quadratic Wasserstein distance for the three-atom sharpness family. -/
lemma wasserstein2_sharpTarget (d : ℕ) (hd : 2 ≤ d) {a : ℝ}
    (b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    wasserstein2 (sharpTarget d hd a 0) (sharpTarget d hd a b) =
      Real.sqrt (a * b ^ 2) := by
  have hπ : IsCoupling (sharpTarget d hd a 0) (sharpTarget d hd a b)
      (atomicMatchingPlan (sharpWeights a) (sharpAtoms d hd 0) (sharpAtoms d hd b)) :=
    atomicMatchingPlan_isCoupling _ _ _ (sharpWeights_sum ha ha1)
  have hcost : quadraticPlanCost (atomicMatchingPlan (sharpWeights a)
      (sharpAtoms d hd 0) (sharpAtoms d hd b)) =
      ∫⁻ y, ENNReal.ofReal ((y (sharpAxis1 d hd)) ^ 2) ∂sharpTarget d hd a b := by
    rw [quadraticPlanCost_sharpMatching, sharpTarget_axis1_moment]
  rw [wasserstein2_eq_sqrt_coordinate_moment (sharpAxis1 d hd)
    (sharpTarget_ae_axis1_zero d hd a) hπ hcost,
    sharpTarget_axis1_moment, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal (sq_nonneg b)]

/-- Nonzero transverse displacement gives strictly positive target distance. -/
lemma wasserstein2_sharpTarget_pos (d : ℕ) (hd : 2 ≤ d) {a b : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : b ≠ 0) :
    0 < wasserstein2 (sharpTarget d hd a 0) (sharpTarget d hd a b) := by
  rw [wasserstein2_sharpTarget d hd b ha.le ha1]
  exact Real.sqrt_pos.2 (mul_pos ha (sq_pos_of_ne_zero hb))

/-- The standard choice `b = a / 2` has squared transport cost `a^3 / 4`. -/
lemma wasserstein2_sharpTarget_half (d : ℕ) (hd : 2 ≤ d) {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    wasserstein2 (sharpTarget d hd a 0) (sharpTarget d hd a (a / 2)) =
      Real.sqrt (a ^ 3 / 4) := by
  rw [wasserstein2_sharpTarget d hd (a / 2) ha ha1]
  congr 1
  ring

end Problem358

end

end OAI
