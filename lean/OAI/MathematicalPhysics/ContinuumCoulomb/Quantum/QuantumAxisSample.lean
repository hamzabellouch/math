import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalSquareRoot
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBlockCoefficientBounds

namespace OAI

/-! Rational sampling of the fixed algebraic constants in the four-spin encoding. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open scoped Classical

def inverseScale (a : Fin 2) : ℝ := if a = 0 then Real.sqrt 3/384 else 3/4

theorem inverseScale_mul (a : Fin 2) : inverseScale a*qmaFourAxisScale a = 1 := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases a
  · dsimp [inverseScale,qmaFourAxisScale]
    nlinarith
  · norm_num [inverseScale,qmaFourAxisScale]

theorem inverseScale_bounds (a : Fin 2) : 0 ≤ inverseScale a ∧ inverseScale a ≤ 1 := by
  have hs := Real.sqrt_nonneg 3
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases a
  · dsimp [inverseScale]
    constructor <;> nlinarith
  · norm_num [inverseScale]

def value (k : ℕ) (a : Fin 2) : ℚ :=
  if a = 0 then RationalSquareRoot.value (k,3)/384 else 3/4

theorem root_nonneg (k : ℕ) (q : ℚ) : 0 ≤ RationalSquareRoot.value (k,q) := by
  unfold RationalSquareRoot.value DyadicRootProgram.value
  positivity

theorem value_nonneg (k : ℕ) (a : Fin 2) : 0 ≤ value k a := by
  unfold value
  split_ifs
  · exact div_nonneg (root_nonneg k 3) (by norm_num)
  · norm_num

theorem value_error (k : ℕ) (a : Fin 2) :
    |(value k a:ℝ)-inverseScale a| ≤ (2:ℝ)⁻¹^k := by
  have h := RationalSquareRoot.value_error k (by norm_num : (0:ℚ) ≤ 3)
  have hd : 0 ≤ (2:ℝ)⁻¹^k := by positivity
  norm_num only [Rat.cast_ofNat] at h
  by_cases ha : a = 0
  · simp only [value,inverseScale,ha,ite_true,Rat.cast_div,Rat.cast_ofNat]
    obtain ⟨hl,hu⟩ := abs_le.mp h
    apply abs_le.mpr
    constructor <;> linarith
  · simp [value,inverseScale,ha]

theorem value_bounds (k : ℕ) (a : Fin 2) : 0 ≤ (value k a:ℝ) ∧ (value k a:ℝ) ≤ 1 := by
  have hn : (0:ℝ) ≤ value k a := by exact_mod_cast value_nonneg k a
  refine ⟨hn,?_⟩
  have h := RationalSquareRoot.value_error k (by norm_num : (0:ℚ) ≤ 3)
  have hd : (2:ℝ)⁻¹^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hs := Real.sqrt_nonneg 3
  have hs2 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  by_cases ha : a = 0
  · simp only [value,ha,ite_true,Rat.cast_div,Rat.cast_ofNat]
    have hh := (abs_le.mp h).2
    norm_num only [Rat.cast_ofNat] at hh
    nlinarith
  · norm_num [value,ha]

theorem product_error (k : ℕ) (a b : Fin 2) :
    |(value k a:ℝ)*(value k b:ℝ)-inverseScale a*inverseScale b| ≤ 2*(2:ℝ)⁻¹^k := by
  have hd : 0 ≤ (2:ℝ)⁻¹^k := by positivity
  have ha := value_error k a
  have hb := value_error k b
  have hav : |inverseScale a| ≤ 1 := by rw [abs_of_nonneg (inverseScale_bounds a).1]; exact (inverseScale_bounds a).2
  have hbv : |(value k b:ℝ)| ≤ 1 := by rw [abs_of_nonneg (value_bounds k b).1]; exact (value_bounds k b).2
  calc
    _ = |((value k a:ℝ)-inverseScale a)*(value k b:ℝ)+inverseScale a*((value k b:ℝ)-inverseScale b)| := by
      congr 1
      ring
    _ ≤ |((value k a:ℝ)-inverseScale a)*(value k b:ℝ)|+|inverseScale a*((value k b:ℝ)-inverseScale b)| := abs_add_le _ _
    _ = |(value k a:ℝ)-inverseScale a| * |(value k b:ℝ)|+
        |inverseScale a| * |(value k b:ℝ)-inverseScale b| := by rw [abs_mul,abs_mul]
    _ ≤ (2:ℝ)⁻¹^k*1+1*(2:ℝ)⁻¹^k := add_le_add
      (mul_le_mul ha hbv (abs_nonneg _) hd) (mul_le_mul hav hb (abs_nonneg _) (by norm_num))
    _ = _ := by ring

def radicand (k : ℕ) (a b : Fin 2) (t : ℚ) : ℚ := (8/3)*|t| *value k a*value k b

theorem radicand_nonneg (k : ℕ) (a b : Fin 2) (t : ℚ) : 0 ≤ radicand k a b t := by
  unfold radicand
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg t)) (value_nonneg k a))
    (value_nonneg k b)

theorem coupling_eq (a b : Fin 2) (t : ℝ) :
    qmaFourCouplingSize a b t = Real.sqrt ((8/3)*|t| *inverseScale a*inverseScale b) := by
  unfold qmaFourCouplingSize
  congr 1
  have ha := inverseScale_mul a
  have hb := inverseScale_mul b
  have han := (qmaFourAxisScale_pos a).ne'
  have hbn := (qmaFourAxisScale_pos b).ne'
  apply (div_eq_iff (mul_ne_zero (mul_ne_zero (by norm_num) han) hbn)).mpr
  calc
    _ = 8*|t| *(inverseScale a*qmaFourAxisScale a)*(inverseScale b*qmaFourAxisScale b) := by rw [ha,hb]; ring
    _ = _ := by ring

theorem radicand_error (k : ℕ) (a b : Fin 2) (t : ℚ) :
    |(radicand k a b t:ℝ)-(8/3)*|(t:ℝ)| *inverseScale a*inverseScale b| ≤
      (16/3)*|(t:ℝ)| *(2:ℝ)⁻¹^k := by
  simp only [radicand,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_abs]
  calc
    _ = |((8/3)*|(t:ℝ)|)*((value k a:ℝ)*(value k b:ℝ)-inverseScale a*inverseScale b)| := by
      congr 1
      ring
    _ = ((8/3)*|(t:ℝ)|)*|(value k a:ℝ)*(value k b:ℝ)-inverseScale a*inverseScale b| := by
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (8/3:ℝ)*|(t:ℝ)|)]
    _ ≤ ((8/3)*|(t:ℝ)|)*(2*(2:ℝ)⁻¹^k) :=
      mul_le_mul_of_nonneg_left (product_error k a b) (by positivity)
    _ = _ := by ring

def coupling (k l : ℕ) (a b : Fin 2) (t : ℚ) : ℚ :=
  RationalSquareRoot.value (l,radicand k a b t)

theorem coupling_error (k l : ℕ) (a b : Fin 2) (t : ℚ) :
    |(coupling k l a b t:ℝ)-qmaFourCouplingSize a b (t:ℝ)| ≤
      (2:ℝ)⁻¹^l+Real.sqrt ((16/3)*|(t:ℝ)| *(2:ℝ)⁻¹^k) := by
  have hr := RationalSquareRoot.value_error l (radicand_nonneg k a b t)
  have hs := RationalSquareRoot.sqrt_perturbation
    (show (0:ℝ) ≤ radicand k a b t by exact_mod_cast radicand_nonneg k a b t)
    (show 0 ≤ (8/3)*|(t:ℝ)| *inverseScale a*inverseScale b from
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (inverseScale_bounds a).1)
        (inverseScale_bounds b).1)
  rw [coupling_eq]
  exact (abs_sub_le _ _ _).trans (add_le_add hr (hs.trans (Real.sqrt_le_sqrt (radicand_error k a b t))))

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
