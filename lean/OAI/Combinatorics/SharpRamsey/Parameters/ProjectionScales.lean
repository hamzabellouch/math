import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.ProjectionPublic

namespace OAI

section
namespace SharpLogRamsey.Projection
open Real
open scoped Topology

lemma source_numeric {i : ℕ} {σ q N T b : ℝ}
    (hσ : 1000000000000 ≤ σ) (hqeq : exp σ=q)
    (hN : 0<N) (hT : 0<T) (hNT : N≤T) (hb : b≤σ/5)
    (hlo : q^(i+5)*exp (-b)≤N*T) (hhi : N*T≤2*q^(i+5)) :
    N≤q^(i+3)/100000 ∧ 1000000*q≤T ∧
      sqrt (100*(300000*q^(i+5)/T)/q^(i+3))≤1/2 ∧
      q*(sqrt (100*(300000*q^(i+5)/T)/q^(i+3)))^7≤1 := by
  have hs : 0≤σ := by linarith
  have hq : 0<q := hqeq ▸ exp_pos σ
  have hexp (k : ℕ) : q^k=exp ((k:ℝ)*σ) := by rw [←hqeq,exp_nat_mul]
  have hTlow : exp (12*σ/5)≤T := by
    have he : exp (24*σ/5)≤q^(i+5)*exp (-b) := by
      rw [hexp,←exp_add]
      apply exp_le_exp.mpr
      push_cast
      nlinarith [mul_nonneg (show 0≤(i:ℝ) by positivity) hs]
    have hh : (exp (12*σ/5))^2≤T^2 := by
      rw [←exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show (2:ℝ)*(12*σ/5)=24*σ/5 by ring]
      have hp := mul_le_mul_of_nonneg_right hNT hT.le
      nlinarith only [he,hlo,hp]
    exact (sq_le_sq₀ (exp_pos _).le hT.le).mp hh
  have hNup : N≤2*exp (((i+5:ℕ):ℝ)*σ/2) := by
    have he : (exp (((i+5:ℕ):ℝ)*σ/2))^2=q^(i+5) := by
      rw [hexp,←exp_nat_mul]
      congr 1
      push_cast
      ring
    have hp := mul_le_mul_of_nonneg_left hNT hN.le
    have hn : 0<exp (((i+5:ℕ):ℝ)*σ/2) := exp_pos _
    nlinarith only [hp,hhi,he,hn]
  have hcN : 200000≤exp (σ/2) := by
    have hh := add_one_le_exp (σ/2)
    linarith
  have hsN : exp (((i+5:ℕ):ℝ)*σ/2)*exp (σ/2)≤q^(i+3) := by
    rw [hexp,←exp_add]
    apply exp_le_exp.mpr
    push_cast
    nlinarith [mul_nonneg (show 0≤(i:ℝ) by positivity) hs]
  have hsmall : N≤q^(i+3)/100000 := by
    have hh := mul_le_mul_of_nonneg_left hcN (exp_pos (((i+5:ℕ):ℝ)*σ/2)).le
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<100000)).mpr
    nlinarith only [hh,hsN,hNup]
  have hcT : 1000000≤exp (7*σ/5) := by
    have hh := add_one_le_exp (7*σ/5)
    linarith
  have hlarge : 1000000*q≤T := by
    have hh := mul_le_mul_of_nonneg_left hcT hq.le
    have he : q*exp (7*σ/5)=exp (12*σ/5) := by
      rw [←hqeq,←exp_add]
      congr 1
      ring
    rw [he] at hh
    nlinarith only [hh,hTlow]
  have hcR : 30000000≤exp (σ/15) := by
    have hh := add_one_le_exp (σ/15)
    linarith
  have hTR : 30000000*exp (7*σ/3)≤T := by
    have hh := mul_le_mul_of_nonneg_right hcR (exp_pos (7*σ/3)).le
    rw [←exp_add,show σ/15+7*σ/3=12*σ/5 by ring] at hh
    exact hh.trans hTlow
  have heQ : q^(i+5)=q^(i+3)*q^2 := by rw [←pow_add]
  have hratio : 100*(300000*q^(i+5)/T)/q^(i+3)=30000000*q^2/T := by
    rw [heQ]
    field_simp
    ring
  have hr : 30000000*q^2/T≤exp (-σ/3) := by
    apply (div_le_iff₀ hT).mpr
    have hh := mul_le_mul_of_nonneg_left hTR (exp_pos (-σ/3)).le
    have he : exp (-σ/3)*(30000000*exp (7*σ/3))=30000000*q^2 := by
      rw [hexp]
      calc
        _ = 30000000*(exp (-σ/3)*exp (7*σ/3)) := by ring
        _ = _ := by rw [←exp_add]; congr 2; norm_num; ring
    rwa [he] at hh
  have hroot : sqrt (100*(300000*q^(i+5)/T)/q^(i+3))≤exp (-σ/6) := by
    rw [hratio]
    apply (sqrt_le_iff).mpr
    refine ⟨(exp_pos _).le,hr.trans_eq ?_⟩
    rw [←exp_nat_mul]
    congr 1
    norm_num
    ring
  have hhalf : exp (-σ/6)≤1/2 := by
    have he : 2≤exp (σ/6) := by have hh := add_one_le_exp (σ/6); linarith
    rw [show -σ/6=-(σ/6) by ring,exp_neg]
    simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) he)
  refine ⟨hsmall,hlarge,hroot.trans hhalf,?_⟩
  calc
    _ ≤ q*(exp (-σ/6))^7 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sqrt_nonneg _) hroot _) hq.le
    _ = exp (-σ/6) := by
      rw [←hqeq,←exp_nat_mul,←exp_add]
      congr 1
      norm_num
      ring
    _ ≤ 1 := hhalf.trans (by norm_num)

end SharpLogRamsey.Projection

end

end OAI
