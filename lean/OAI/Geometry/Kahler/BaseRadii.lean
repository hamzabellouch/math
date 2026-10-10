import OAI.Geometry.Kahler.BaseSeriesBounds

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

def testRadius (Q : ℕ) (η : ℝ) (N : ℕ) : ℝ := 1-η/(Q:ℝ)^N

lemma testRadius_mem {Q : ℕ} (hQ : 2 ≤ Q) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (N : ℕ) : 0 < testRadius Q η N ∧ testRadius Q η N < 1 := by
  have hQ1 : 1 ≤ (Q:ℝ) := by exact_mod_cast (show 1 ≤ Q by omega)
  have hp : 1 ≤ (Q:ℝ)^N := one_le_pow₀ hQ1
  have hd : 0 < η/(Q:ℝ)^N := div_pos hη (by positivity)
  have hd1 : η/(Q:ℝ)^N < 1 := (div_lt_one (by positivity)).2 (hη1.trans_le hp)
  dsimp [testRadius]
  constructor <;> linarith

lemma testRadius_near {Q : ℕ} (hQ : 2 ≤ Q) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    {N j : ℕ} (hj : j+1 ≤ N) : 1-η ≤ (testRadius Q η N)^(Q^(j+1)) := by
  have hp : 0 < (Q:ℝ)^N := by positivity
  have hp1 : 1 ≤ (Q:ℝ)^N := one_le_pow₀ (by exact_mod_cast (show 1 ≤ Q by omega))
  have hd : η/(Q:ℝ)^N ≤ 1 := (div_le_one hp).2 (hη1.le.trans hp1)
  have hbern := one_add_mul_le_pow (a := -η/(Q:ℝ)^N) (by rw [neg_div]; linarith : -2 ≤ -η/(Q:ℝ)^N) (Q^(j+1))
  have hk : (Q:ℝ)^(j+1) ≤ (Q:ℝ)^N := pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ Q by omega)) hj
  have hm : (Q:ℝ)^(j+1)*(η/(Q:ℝ)^N) ≤ η := by
    calc _ ≤ (Q:ℝ)^N*(η/(Q:ℝ)^N) := mul_le_mul_of_nonneg_right hk (div_nonneg hη.le hp.le)
         _ = η := mul_div_cancel₀ η hp.ne'
  simp only [Nat.cast_pow,neg_div,mul_neg,← sub_eq_add_neg] at hbern
  exact (by linarith : 1-η ≤ 1-(Q:ℝ)^(j+1)*(η/(Q:ℝ)^N)).trans hbern

lemma testRadius_tail {Q : ℕ} (hQ : 2 ≤ Q) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (N m : ℕ) : (testRadius Q η N)^(Q^(m+N+1)) ≤ (Real.exp (-η))^(m+1) := by
  have hp : 0 < (Q:ℝ)^N := by positivity
  have hbase : testRadius Q η N ≤ Real.exp (-η/(Q:ℝ)^N) := by
    simpa only [testRadius,neg_div] using Real.one_sub_le_exp_neg (η/(Q:ℝ)^N)
  have hpow := pow_le_pow_left₀ (testRadius_mem hQ hη hη1 N).1.le hbase (Q^(m+N+1))
  rw [← Real.exp_nat_mul] at hpow
  have heq : ((Q^(m+N+1):ℕ):ℝ)*(-η/(Q:ℝ)^N) = -η*(Q:ℝ)^(m+1) := by
    rw [Nat.cast_pow,show m+N+1=N+(m+1) by omega,pow_add]
    field_simp
  rw [heq] at hpow
  have hdeg : (m+1:ℝ) ≤ (Q:ℝ)^(m+1) := by exact_mod_cast lacunary_degree_ge hQ m
  calc _ ≤ Real.exp (-η*(Q:ℝ)^(m+1)) := hpow
       _ ≤ Real.exp ((m+1)*(-η)) := Real.exp_le_exp.mpr (by nlinarith)
       _ = (Real.exp (-η))^(m+1) := by simpa using Real.exp_nat_mul (-η) (m+1)

lemma testRadius_log {Q : ℕ} (hQ : 2 ≤ Q) {η : ℝ} (hη : 0 < η) (N : ℕ) :
    Real.log (1/(1-testRadius Q η N)) = (N:ℝ)*Real.log Q-Real.log η := by
  have hp : (Q:ℝ)^N ≠ 0 := by positivity
  rw [testRadius]
  have heq : 1/(1-(1-η/(Q:ℝ)^N)) = (Q:ℝ)^N/η := by field_simp [hη.ne']; ring
  rw [heq,Real.log_div hp hη.ne',Real.log_pow]

end PinchedHartogs.BaseConstruction

end

end OAI
