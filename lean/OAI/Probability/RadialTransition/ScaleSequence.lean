import OAI.Probability.RadialTransition.FamilyControls

namespace OAI

noncomputable section
open scoped BigOperators
open Set Filter
namespace RadialTransition

def doublePower (q : ℝ) (n : ℕ) : ℝ := q^(2^n)
lemma doublePower_zero (q : ℝ) : doublePower q 0=q := by simp [doublePower]
lemma doublePower_succ (q : ℝ) (n : ℕ) : doublePower q (n+1)=(doublePower q n)^2 := by
  change q^(2^(n+1))=(q^(2^n))^2
  rw [Nat.pow_succ,pow_mul]
lemma doublePower_pos {q : ℝ} (hq : 0 < q) (n : ℕ) : 0 < doublePower q n := pow_pos hq _
lemma doublePower_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) : doublePower q n ≤ q := by
  have hh : 1 ≤ 2^n := Nat.one_le_pow n 2 (by norm_num)
  simpa only [doublePower,pow_one] using pow_le_pow_of_le_one hq hq1 hh
lemma doublePower_le_geometric {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    doublePower q n ≤ q^(n+1) := pow_le_pow_of_le_one hq hq1 (Nat.succ_le_iff.mpr Nat.lt_two_pow_self)
lemma summable_doublePower {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) : Summable (doublePower q) := by
  apply Summable.of_nonneg_of_le (fun n => pow_nonneg hq _) (doublePower_le_geometric hq hq1.le)
  simpa only [pow_succ] using (summable_geometric_of_lt_one hq hq1).mul_right q
lemma tsum_doublePower_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1/2) : ∑' n, doublePower q n ≤ 2*q := by
  have hq1' : q < 1 := by linarith
  have hg := (summable_geometric_of_lt_one hq hq1').mul_right q
  have hh := (summable_doublePower hq hq1').tsum_le_tsum (doublePower_le_geometric hq hq1'.le)
    (show Summable (fun n => q^(n+1)) by simpa only [pow_succ] using hg)
  have heq : (∑' n, q^(n+1))=q/(1-q) := by
    simp_rw [pow_succ]
    rw [tsum_mul_right,tsum_geometric_of_lt_one hq hq1']
    ring
  rw [heq] at hh
  apply hh.trans
  apply (div_le_iff₀ (by linarith : 0 < 1-q)).mpr
  nlinarith
lemma doublePower_pow (q : ℝ) (k n : ℕ) : doublePower (q^k) n=(doublePower q n)^k := by
  dsimp [doublePower]
  rw [← pow_mul,← pow_mul,Nat.mul_comm k]
lemma doublePower_mul (q r : ℝ) (n : ℕ) : doublePower (q*r) n=doublePower q n*doublePower r n := mul_pow _ _ _
lemma doublePower_inv (q : ℝ) (n : ℕ) : doublePower q⁻¹ n=(doublePower q n)⁻¹ := inv_pow _ _

def scaleRange (b : ℝ) (n : ℕ) : ℝ := (doublePower b n)^32

def scaleTail (b : ℝ) (n : ℕ) : ℝ := (doublePower b n)⁻¹^4

lemma doublePower_one_le {b : ℝ} (hb : 1 ≤ b) (n : ℕ) : 1 ≤ doublePower b n := one_le_pow₀ hb
lemma doublePower_le_self {b : ℝ} (hb : 1 ≤ b) (n : ℕ) : b ≤ doublePower b n := by
  simpa only [doublePower,pow_one] using pow_le_pow_right₀ hb (Nat.one_le_pow n 2 (by norm_num))
lemma scaleRange_pos {b : ℝ} (hb : 0 < b) (n : ℕ) : 0 < scaleRange b n := pow_pos (doublePower_pos hb n) _
lemma scaleRange_one_le {b : ℝ} (hb : 1 ≤ b) (n : ℕ) : 1 ≤ scaleRange b n := one_le_pow₀ (doublePower_one_le hb n)
lemma scaleRange_base_le {b : ℝ} (hb : 1 ≤ b) (n : ℕ) : b ≤ scaleRange b n := by
  exact (doublePower_le_self hb n).trans (by
    change doublePower b n ≤ (doublePower b n)^32
    simpa only [pow_one] using pow_le_pow_right₀ (doublePower_one_le hb n) (by norm_num : 1≤32))
lemma scaleRange_succ (b : ℝ) (n : ℕ) : scaleRange b (n+1)=(scaleRange b n)^2 := by
  dsimp [scaleRange]
  rw [doublePower_succ,← pow_mul,← pow_mul]
lemma scaleRange_mono {b : ℝ} (hb : 1 ≤ b) : Monotone (scaleRange b) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [scaleRange_succ]
  nlinarith [scaleRange_one_le hb n]
lemma scaleTail_pos {b : ℝ} (hb : 0 < b) (n : ℕ) : 0 < scaleTail b n := pow_pos (inv_pos.mpr (doublePower_pos hb n)) _
lemma scaleTail_eq (b : ℝ) (n : ℕ) : scaleTail b n=doublePower (b⁻¹^4) n := by
  rw [doublePower_pow,doublePower_inv]
  rfl
lemma scaleTail_succ (b : ℝ) (n : ℕ) : scaleTail b (n+1)=(scaleTail b n)^2 := by
  simp only [scaleTail_eq,doublePower_succ]
lemma scaleTail_le {b : ℝ} (hb : 1 ≤ b) (n : ℕ) : scaleTail b n ≤ b⁻¹^4 := by
  rw [scaleTail_eq]
  exact doublePower_le (by positivity) (pow_le_one₀ (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hb)) n
lemma scaleTail_le_one {b : ℝ} (hb : 1 ≤ b) (n : ℕ) : scaleTail b n ≤ 1 :=
  (scaleTail_le hb n).trans (pow_le_one₀ (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hb))
lemma inv_fourth_le_half {b : ℝ} (hb : 2 ≤ b) : b⁻¹^4 ≤ 1/2 := by
  have h0 : 0 < b := by linarith
  have h1 : b⁻¹ ≤ 1/2 := by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hb
  have h2 := pow_le_pow_left₀ (inv_nonneg.mpr h0.le) h1 4
  norm_num only [one_div,inv_pow] at *
  linarith
lemma summable_scaleTail {b : ℝ} (hb : 2 ≤ b) : Summable (scaleTail b) := by
  have h0 : 0 ≤ b⁻¹^4 := by positivity
  have h1 : b⁻¹^4 < 1 := by linarith [inv_fourth_le_half hb]
  convert summable_doublePower h0 h1 using 1
  ext n
  exact scaleTail_eq b n
lemma tsum_scaleTail_le {b : ℝ} (hb : 2 ≤ b) : ∑' n, scaleTail b n ≤ 2*b⁻¹^4 := by
  simpa only [scaleTail_eq] using tsum_doublePower_le (by positivity : 0 ≤ b⁻¹^4) (inv_fourth_le_half hb)
lemma sum_scaleTail_le {b : ℝ} (hb : 2 ≤ b) (n : ℕ) : ∑ j ∈ Finset.range n, scaleTail b j ≤ 2*b⁻¹^4 := by
  exact ((summable_scaleTail hb).sum_le_tsum (Finset.range n) (fun j _ => (scaleTail_pos (by linarith) j).le)).trans (tsum_scaleTail_le hb)

lemma scaleRange_root {b : ℝ} (hb : 0 < b) (n : ℕ) : (scaleRange b n)^(1/32:ℝ)=doublePower b n := by
  dsimp [scaleRange]
  rw [← Real.rpow_natCast_mul (doublePower_pos hb n).le]
  norm_num
lemma scaleTail_literal {b : ℝ} (hb : 0 < b) (n : ℕ) : scaleTail b n=(scaleRange b (n+1))^(-(1/16:ℝ)) := by
  dsimp [scaleRange,scaleTail]
  rw [← Real.rpow_natCast_mul (doublePower_pos hb (n+1)).le]
  norm_num
  rw [doublePower_succ]
  ring
lemma scaleTail_weight {b : ℝ} (hb : 0 < b) (n : ℕ) :
    scaleTail b n*(scaleRange b (n+1))^(1/32:ℝ)=doublePower (b⁻¹^2) n := by
  rw [scaleRange_root hb,doublePower_succ,doublePower_pow,doublePower_inv]
  dsimp [scaleTail]
  field_simp
lemma summable_scaleTail_weight {b : ℝ} (hb : 2 ≤ b) :
    Summable (fun n => scaleTail b n*(scaleRange b (n+1))^(1/32:ℝ)) := by
  have h0 : 0 < b := by linarith
  have h1 : b⁻¹ ≤ 1/2 := by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hb
  have hh := pow_le_pow_left₀ (inv_nonneg.mpr h0.le) h1 2
  have hh' : b⁻¹^2 < 1 := by norm_num only [one_div,inv_pow] at *; linarith
  convert summable_doublePower (by positivity : 0 ≤ b⁻¹^2) hh' using 1
  ext n
  exact scaleTail_weight h0 n

lemma scale_kac_succ {b : ℝ} (hb : 1 ≤ b) (n : ℕ) :
    Real.sqrt (scaleRange b n/scaleRange b (n+1))=(scaleTail b (n+1))^2 := by
  have h0 : 0 < doublePower b n := doublePower_pos (by linarith) n
  apply (Real.sqrt_le_iff.mpr ?_).antisymm
  · apply (Real.le_sqrt (sq_nonneg _) (div_nonneg (scaleRange_pos (by linarith) n).le (scaleRange_pos (by linarith) (n+1)).le)).mpr
    dsimp [scaleRange,scaleTail]
    rw [doublePower_succ]
    field_simp
    norm_num
  · constructor
    · positivity
    · dsimp [scaleRange,scaleTail]
      rw [doublePower_succ]
      field_simp
      norm_num
lemma scale_kac_zero {b : ℝ} (hb : 2 ≤ b) :
    Real.sqrt (2/scaleRange b 0) ≤ 2*(scaleTail b 0)^2 := by
  have h0 : 0 < b := by linarith
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · simp only [scaleRange,scaleTail,doublePower_zero]
    have hp : 1 ≤ b^16 := one_le_pow₀ (by linarith : 1≤b)
    field_simp
    nlinarith

end RadialTransition
end

end OAI
