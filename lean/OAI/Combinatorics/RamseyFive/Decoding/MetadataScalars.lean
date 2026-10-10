import Mathlib

namespace OAI

namespace SharpRamseyFive.Metadata
open Filter
open scoped Topology

lemma list_length_bounds (σ g h p : ℝ) (_hh : 0≤h) (hp : 0≤p)
    (hg : 0≤g) (hghi : g≤σ+Real.log 4)
    (hlen : h*Real.exp (2*σ)≤Real.exp (3*σ/2+g))
    (plen : p*Real.exp (σ+17*g/15)≤Real.exp (3*σ/2+g)) :
    h≤4*Real.exp (σ/2) ∧ p≤Real.exp (σ/2) ∧ h*p≤4*Real.exp (13*σ/15) := by
  have hb : h≤Real.exp (g-σ/2) := by
    have hb := (le_div_iff₀ (Real.exp_pos (2*σ))).mpr hlen
    rw [←Real.exp_sub] at hb
    convert hb using 1; congr 1; ring
  have pb : p≤Real.exp (σ/2-2*g/15) := by
    have pb := (le_div_iff₀ (Real.exp_pos (σ+17*g/15))).mpr plen
    rw [←Real.exp_sub] at pb
    convert pb using 1; congr 1; ring
  refine ⟨?_,pb.trans (Real.exp_le_exp.mpr (by linarith)),?_⟩
  · calc
      h≤Real.exp (σ/2+Real.log 4) := hb.trans (Real.exp_le_exp.mpr (by linarith))
      _=4*Real.exp (σ/2) := by rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4)];ring
  · calc
      _≤Real.exp (g-σ/2)*Real.exp (σ/2-2*g/15) := mul_le_mul hb pb hp (Real.exp_nonneg _)
      _=Real.exp (13*g/15) := by rw [←Real.exp_add];congr 1;ring
      _≤Real.exp (13*σ/15+Real.log 4) := Real.exp_le_exp.mpr (by have := Real.log_nonneg (by norm_num : (1:ℝ)≤4);linarith)
      _=4*Real.exp (13*σ/15) := by rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4)];ring

lemma sigma_exp_absorb (C σ : ℝ) (hC : 0≤C) (hσ : 225*C≤σ) (hσ0 : 0≤σ) :
    C*σ*Real.exp (13*σ/15)≤Real.exp σ := by
  have hp := Real.pow_div_factorial_le_exp (2*σ/15) (by positivity : (0:ℝ)≤2*σ/15) 2
  norm_num only [Nat.factorial,Finset.prod_range_succ,Nat.cast_ofNat] at hp
  have hc : C*σ≤Real.exp (2*σ/15) := by nlinarith
  calc
    _≤Real.exp (2*σ/15)*Real.exp (13*σ/15) := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _=Real.exp σ := by rw [←Real.exp_add];congr 1;ring

lemma metadata_budget (σ H J B V : ℝ) (hσ : 100000≤σ)
    (hH : 0≤H) (hJ : 0≤J) (_hB : 0<B) (_hV : 0<V)
    (hHhi : H≤5*Real.exp (σ/2)) (hJhi : J≤5*Real.exp (13*σ/15))
    (hHlog : Real.log (H+1)≤σ) (hBlog : Real.log B≤6*σ) (hVlog : Real.log V≤5*σ) :
    2*Real.log (H+1)+(10*H)*Real.log V+(1+2*H+J)*Real.log B≤Real.exp σ := by
  have hσ0 : 0≤σ := by linarith
  have he : Real.exp (σ/2)≤Real.exp (13*σ/15) := Real.exp_le_exp.mpr (by linarith)
  have he1 : 1≤Real.exp (13*σ/15) := Real.one_le_exp_iff.mpr (by positivity)
  have hh : H≤5*Real.exp (13*σ/15) := hHhi.trans (mul_le_mul_of_nonneg_left he (by norm_num))
  have h₁ := mul_le_mul_of_nonneg_left hVlog (by positivity : (0:ℝ)≤10*H)
  have h₂ := mul_le_mul_of_nonneg_left hBlog (by positivity : (0:ℝ)≤1+2*H+J)
  have h₃ := mul_le_mul_of_nonneg_left hh hσ0
  have h₄ := mul_le_mul_of_nonneg_left hJhi hσ0
  have h₅ := mul_le_mul_of_nonneg_left he1 hσ0
  apply le_trans _ (sigma_exp_absorb 400 σ (by norm_num) (by linarith) hσ0)
  nlinarith only [hHlog,h₁,h₂,h₃,h₄,h₅,mul_nonneg hσ0 (Real.exp_nonneg (13*σ/15))]

end SharpRamseyFive.Metadata

end OAI
