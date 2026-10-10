import OAI.NumberTheory.TwoPoint.Halasz.HalaszNormalizedStep

namespace OAI

/-! The geometric defect in the classical Vinogradov iteration. -/
namespace TwoPointCorrelations

def halaszTriangularDegree (k : ℕ) : ℕ := k*(k-1)/2

def halaszTotalDegree (k : ℕ) : ℕ := k+halaszTriangularDegree k

noncomputable def halaszClassicalDefect (k n : ℕ) : ℝ :=
  (halaszTriangularDegree k:ℝ)*(1-1/(k:ℝ))^n

noncomputable def halaszClassicalExponent (k n : ℕ) : ℝ :=
  2*(((n+1)*k:ℕ):ℝ)-(halaszTotalDegree k:ℝ)+halaszClassicalDefect k n

lemma halasz_triangular_degree_cast {k : ℕ} (hk : 0<k) :
    (halaszTriangularDegree k:ℝ)=(k:ℝ)*(k-1)/2 := by
  have h := Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one k)
  have hR : (2:ℝ)*(halaszTriangularDegree k:ℝ)=(k:ℝ)*((k-1:ℕ):ℝ) := by
    exact_mod_cast h
  rw [Nat.cast_sub hk,Nat.cast_one] at hR
  linarith

lemma halasz_total_degree_cast {k : ℕ} (hk : 0<k) :
    (halaszTotalDegree k:ℝ)=(k:ℝ)*(k+1)/2 := by
  simp only [halaszTotalDegree,Nat.cast_add,halasz_triangular_degree_cast hk]
  ring

lemma halasz_classical_ratio_bounds {k : ℕ} (hk : 0<k) :
    0≤1-1/(k:ℝ) ∧ 1-1/(k:ℝ)≤1 := by
  have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
  have hk0 : (0:ℝ)<k := by exact_mod_cast hk
  have hi : 1/(k:ℝ)≤1 := (div_le_one hk0).mpr hk1
  constructor <;> linarith [one_div_pos.mpr hk0]

lemma halasz_classical_defect_bounds {k : ℕ} (hk : 0<k) (n : ℕ) :
    0≤halaszClassicalDefect k n ∧
      halaszClassicalDefect k n≤(halaszTriangularDegree k:ℝ) := by
  have hr := halasz_classical_ratio_bounds hk
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr.1 _)
  · exact mul_le_of_le_one_right (Nat.cast_nonneg _)
      (pow_le_one₀ hr.1 hr.2)

lemma halasz_classical_defect_successor (k n : ℕ) :
    halaszClassicalDefect k (n+1)=(1-1/(k:ℝ))*halaszClassicalDefect k n := by
  simp only [halaszClassicalDefect,pow_succ]
  ring

lemma halasz_classical_exponent_zero (k : ℕ) : halaszClassicalExponent k 0=k := by
  simp only [halaszClassicalExponent,halaszClassicalDefect,pow_zero,mul_one,
    zero_add,one_mul,halaszTotalDegree,Nat.cast_add]
  ring

lemma halasz_classical_exponent_successor (k n : ℕ) :
    halaszClassicalExponent k (n+1)=halaszClassicalExponent k n+2*k-
      halaszClassicalDefect k n/(k:ℝ) := by
  simp only [halaszClassicalExponent,halasz_classical_defect_successor,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  ring

lemma halasz_classical_exponent_bounds {k : ℕ} (hk : 0<k) (n : ℕ) :
    (k:ℝ)≤halaszClassicalExponent k n ∧
      halaszClassicalExponent k n≤(halaszStepExponent ((n+1)*k) k:ℝ) := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast hk
  have hd (n : ℕ) : halaszClassicalDefect k n/(k:ℝ)≤k := by
    apply (div_le_iff₀ hk0).mpr
    have hh := (halasz_classical_defect_bounds hk n).2
    rw [halasz_triangular_degree_cast hk] at hh
    nlinarith
  constructor
  · induction n with
    | zero => exact (halasz_classical_exponent_zero k).ge
    | succ n ih =>
      rw [halasz_classical_exponent_successor]
      linarith [hd n]
  · have hh := (halasz_classical_defect_bounds hk n).2
    simp only [halaszClassicalExponent,halaszTotalDegree,Nat.cast_add,
      halaszStepExponent,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    change 2*(((n:ℝ)+1)*k)-((k:ℝ)+(halaszTriangularDegree k:ℝ))+
      halaszClassicalDefect k n ≤ 2*(((n:ℝ)+1)*k)+(halaszTriangularDegree k:ℝ)
    linarith [show (0:ℝ)≤(halaszTriangularDegree k:ℝ) from Nat.cast_nonneg _]

lemma halasz_classical_exponent_normalization {k : ℕ} (hk : 0<k) (n : ℕ) :
    (k:ℝ)+halaszClassicalExponent k n +
      ((halaszStepExponent ((n+1)*k) k:ℝ)-halaszClassicalExponent k n)/(k:ℝ) =
      halaszClassicalExponent k (n+1) := by
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  have ha : (halaszStepExponent ((n+1)*k) k:ℝ) =
      2*(((n+1)*k:ℕ):ℝ)+(halaszTriangularDegree k:ℝ) := by
    simp only [halaszStepExponent,halaszTriangularDegree,Nat.cast_add,Nat.cast_mul,
      Nat.cast_ofNat]
  rw [ha]
  simp only [halaszClassicalExponent,halasz_classical_defect_successor,
    Nat.cast_add,Nat.cast_mul,Nat.cast_one]
  rw [halasz_total_degree_cast hk,halasz_triangular_degree_cast hk]
  field_simp
  ring

end TwoPointCorrelations

end OAI
