import OAI.Analysis.FreeEntropy.BlockEnsembleLower

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
namespace FiniteEntropySeparation
variable {p d : ℕ}
 theorem two_pow_le_exp (k : ℕ) : (2:ℝ)^k≤Real.exp k := by
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (show (2:ℝ)≤Real.exp 1 from by linarith [Real.add_one_le_exp (1:ℝ)]) k
  simpa only [← Real.exp_nat_mul,mul_one] using hh
 theorem blockEvent_gaussian_four (hd : 64≤d) {v : ℝ} (hv : 0<v)
    (hvs : Real.sqrt v≤(2:ℝ)^25) (hpv : 32768*v≤p) (hp : (p:ℝ)≤Real.exp 64) :
    (normalLaw (v/d)) (blockEvent p d (Real.sqrt ((p:ℝ)*d)/4) (4*Real.sqrt (v*p*d)))≤
      ENNReal.ofReal (Real.exp (-4*(d:ℝ)^2)) := by
  have hd0 : 0<d := by omega
  have hd' : (64:ℝ)≤d := by exact_mod_cast hd
  have hdpos : (0:ℝ)<d := by linarith
  have hp0 : 0<(p:ℝ) := by nlinarith
  have hpd : 0<(p:ℝ)*d := mul_pos hp0 hdpos
  have hsq : 0<Real.sqrt v := Real.sqrt_pos.mpr hv
  let ε : ℝ := 1/(64*Real.sqrt v)
  have hε : 0<ε := by dsimp [ε]; positivity
  have hroot : Real.sqrt (v*p*d)=Real.sqrt v*Real.sqrt ((p:ℝ)*d) := by
    rw [mul_assoc,Real.sqrt_mul hv.le]
  have hgap : Real.sqrt ((p:ℝ)*d)/4-2*ε*(4*Real.sqrt (v*p*d))=Real.sqrt ((p:ℝ)*d)/8 := by
    rw [hroot]
    dsimp [ε]
    field_simp
    ring
  have hbase : 1+2/ε≤Real.exp 34 := by
    have hb : 1+2/ε≤(2:ℝ)^34 := by
      have he : 1+2/ε=1+128*Real.sqrt v := by dsimp [ε]; field_simp; ring
      rw [he]
      norm_num at hvs ⊢
      linarith
    exact hb.trans (two_pow_le_exp 34)
  have htail : -((Real.sqrt ((p:ℝ)*d)/8)^2)/(4*(v/d))≤-128*(d:ℝ)^2 := by
    rw [div_pow,Real.sq_sqrt hpd.le]
    have he : -((p:ℝ)*d/(8:ℝ)^2)/(4*(v/d))=-(p:ℝ)*(d:ℝ)^2/(256*v) := by field_simp; ring
    rw [he]
    apply (div_le_iff₀ (by positivity : 0<256*v)).mpr
    have hh := mul_le_mul_of_nonneg_right hpv (sq_nonneg (d:ℝ))
    nlinarith
  have h1 : (p:ℝ)^d≤Real.exp ((d:ℝ)^2) := by
    calc
      _ ≤ (Real.exp 64)^d := pow_le_pow_left₀ hp0.le hp d
      _ = Real.exp ((d:ℝ)*64) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : (1+2/ε)^(2*d^2)≤Real.exp (68*(d:ℝ)^2) := by
    calc
      _ ≤ (Real.exp 34)^(2*d^2) := pow_le_pow_left₀ (by positivity) hbase _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : Real.exp (-((Real.sqrt ((p:ℝ)*d)/8)^2)/(4*(v/d)))≤Real.exp (-128*(d:ℝ)^2) := Real.exp_le_exp.mpr htail
  have h4 : Real.sqrt 2^(2*d^2)≤Real.exp (2*(d:ℝ)^2) := by
    have hs : Real.sqrt 2≤Real.exp 1 := by
      apply le_trans (show Real.sqrt 2≤2 from by nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),Real.sqrt_nonneg (2:ℝ)])
      linarith [Real.add_one_le_exp (1:ℝ)]
    calc
      _ ≤ (Real.exp 1)^(2*d^2) := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hb := blockEvent_gaussian_bound (p := p) hd0 (div_pos hv hdpos) hε
    (show 0≤Real.sqrt ((p:ℝ)*d)/4-2*ε*(4*Real.sqrt (v*p*d)) by rw [hgap]; positivity)
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  rw [hgap]
  calc
    _ ≤ Real.exp ((d:ℝ)^2)*Real.exp (68*(d:ℝ)^2)*Real.exp (-128*(d:ℝ)^2)*Real.exp (2*(d:ℝ)^2) :=
      mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le) h3 (by positivity) (by positivity)) h4 (by positivity) (by positivity)
    _ = Real.exp (-57*(d:ℝ)^2) := by simp only [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (d:ℝ)])
 def chosenP : ℕ := 2^64
 def chosenTime : ℝ := 2^48
 instance chosenP_neZero : NeZero chosenP := ⟨by norm_num [chosenP]⟩
 theorem chosenP_ge_two : 2≤chosenP := by norm_num [chosenP]
 theorem chosenTime_pos : 0<chosenTime := by norm_num [chosenTime]
 theorem chosen_time_noise_budget : 256*chosenTime≤(chosenP:ℝ) := by norm_num [chosenTime,chosenP]
 theorem chosen_gaussian_block (hd : 64≤d) {h : ℝ} (hh : 0<h) (hh1 : h<1) :
    (normalLaw ((1+h+chosenTime)/d))
      (blockEvent chosenP d (Real.sqrt ((chosenP:ℝ)*d)/4) (4*Real.sqrt ((1+h+chosenTime)*chosenP*d)))≤
      ENNReal.ofReal (Real.exp (-4*(d:ℝ)^2)) := by
  apply blockEvent_gaussian_four hd (by have := chosenTime_pos; linarith)
  · apply (Real.sqrt_le_left (by positivity : (0:ℝ)≤(2:ℝ)^25)).mpr
    norm_num [chosenTime] at *
    linarith
  · norm_num [chosenP,chosenTime] at *
    linarith
  · simpa only [chosenP,Nat.cast_pow,Nat.cast_ofNat] using two_pow_le_exp 64
end FiniteEntropySeparation

end

end OAI
