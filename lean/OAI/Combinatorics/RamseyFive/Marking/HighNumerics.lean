import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.HighFourPreRound

namespace OAI

namespace SharpRamseyFive.Marking

section
open Filter Asymptotics Real ParameterHierarchy FiniteEntropy
open scoped Topology
noncomputable section

lemma high_bad_uniform {σ D b C : ℝ} (hσ : 1≤σ) (_ : 0<b)
    (hD : σ^b≤D) (hC : 0≤C) :
    highBadMass (D*σ^(3*b)) (D*σ^b) C≤
      Real.exp (-σ^(4*b))+51*σ^(-2*b)+(50*C+Real.log 2+32)/σ^(4*b) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hd : 0<D := (Real.rpow_pos_of_pos hs b).trans_le hD
  have hlow : σ^(4*b)≤D*σ^(3*b) := by
    calc
      _ = σ^b*σ^(3*b) := by rw [←Real.rpow_add hs];congr 1;ring
      _ ≤_ := mul_le_mul_of_nonneg_right hD (by positivity)
  have he : (D*σ^b)/(D*σ^(3*b))=σ^(-2*b) := by
    rw [mul_div_mul_left _ _ hd.ne',←Real.rpow_sub hs]
    congr 1
    ring
  have hc : 0≤50*C+Real.log 2+32 := by have := Real.log_nonneg (by norm_num : (1:ℝ)≤2);positivity
  have hc' := div_le_div_of_nonneg_left hc (Real.rpow_pos_of_pos hs _) hlow
  unfold highBadMass
  calc
    _ =Real.exp (-(D*σ^(3*b)))+51*((D*σ^b)/(D*σ^(3*b)))+
      (50*C+Real.log 2+32)/(D*σ^(3*b)) := by ring
    _ ≤_ := by rw [he];gcongr

lemma high_four_variance {q s σ : ℝ} {r' : ℕ} (hq : 1≤q)
    (he : Real.exp σ=q) (hr : 2≤r') (hs : 2*s≤σ/2) :
    64*q^5*(2*Real.exp s/q^r')*(Real.exp s/q^4)≤128*Real.exp (-σ/2) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hp := pow_le_pow_right₀ hq hr
  calc
    _ ≤64*q^5*(2*Real.exp s/q^2)*(Real.exp s/q^4) := by gcongr
    _ =128*(Real.exp s*Real.exp s/q) := by field_simp;ring
    _ =128*Real.exp (2*s-σ) := by rw [Real.exp_sub,←Real.exp_add,he];congr 2;congr 1;ring
    _ ≤_ := by gcongr;linarith

lemma high_four_growth {q σ b : ℝ} {h : ℕ} (hq : 1≤q)
    (hl : q*σ^b≤h) :
    (1-1/(5*q))^h≤Real.exp (-(σ^b)/5) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hnon : 0≤1-1/(5*q) := by
    have hh : 1/(5*q)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  calc
    _ ≤(Real.exp (-(1/(5*q))))^h := pow_le_pow_left₀ hnon (Real.one_sub_le_exp_neg _) h
    _ = Real.exp (-(h:ℝ)/(5*q)) := by rw [←Real.exp_nat_mul];congr 1;ring
    _ ≤_ := by
      apply Real.exp_le_exp.mpr
      have hh : σ^b/5≤(h:ℝ)/(5*q) := (le_div_iff₀ (by positivity)).mpr (by nlinarith [hl])
      simpa only [neg_div] using neg_le_neg hh

lemma high_four_conflict {σ q b : ℝ} {h : ℕ} (hσ : 0<σ) (hq : 0<q)
    (hh : (h:ℝ)≤2*q*σ^b) :
    12*h*(σ^(-2000*b)/q)≤24*σ^(-1999*b) := by
  calc
    _ ≤12*(2*q*σ^b)*(σ^(-2000*b)/q) := by gcongr
    _ =24*(σ^b*σ^(-2000*b)) := by field_simp;ring
    _ =_ := by rw [←Real.rpow_add hσ];congr 2;ring

lemma highFourLoss_bound {σ D b : ℝ} {q r' h : ℕ}
    (hσ : 1≤σ) (hb : 0<b) (hD : σ^b≤D) (hq : 1≤q)
    (he : Real.exp σ=q) (hr : 2≤r') (hs : 2*(D*σ^(3*b))≤σ/2)
    (hl : (q:ℝ)*σ^b≤h) (hh : (h:ℝ)≤2*q*σ^b) :
    highFourLoss q r' h (D*σ^(3*b)) (D*σ^b) (σ^(-2000*b)/q)≤
      Real.exp (-σ^(4*b))+51*σ^(-2*b)+(50*153+Real.log 2+32)/σ^(4*b)+
      128*Real.exp (-σ/2)+3*Real.exp (-(σ^b)/5)+24*σ^(-1999*b) := by
  unfold highFourLoss
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  apply add_le_add
  · apply add_le_add
    · exact add_le_add (high_bad_uniform hσ hb hD (by norm_num)) (high_four_variance hq' he hr hs)
    · exact mul_le_mul_of_nonneg_left (high_four_growth hq' hl) (by norm_num)
  · exact high_four_conflict (zero_lt_one.trans_le hσ) (zero_lt_one.trans_le hq') hh

theorem eventually_high_four_loss {η : ℝ} (hη : 0<η) (ρ : ℝ) (hρ : 0<ρ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (q r' h : ℕ),σ^beta η≤D→D≤σ^(1-η/2)→
      1≤q→Real.exp σ=q→2≤r'→(q:ℝ)*σ^beta η≤h→(h:ℝ)≤2*q*σ^beta η→
      highFourLoss q r' h (D*σ^(3*beta η)) (D*σ^beta η) (σ^(-2000*beta η)/q)≤ρ := by
  have hb:=beta_pos hη
  have hpow:=tendsto_rpow_atTop hb
  have h4 : 0<4*beta η := by positivity
  have ht1 := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_rpow_atTop h4)
  have ht2 := (tendsto_rpow_neg_atTop (by positivity : 0<2*beta η)).const_mul 51
  have ht3 : Tendsto (fun σ : ℝ=>(50*153+Real.log 2+32)/σ^(4*beta η)) atTop (𝓝 0) :=
    (tendsto_rpow_atTop h4).const_div_atTop _
  have ht4 : Tendsto (fun σ : ℝ=>128*Real.exp (-σ/2)) atTop (𝓝 0) := by
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2))
    simpa only [Function.comp_apply,id_eq,neg_div,mul_zero] using ht.const_mul 128
  have ht5 : Tendsto (fun σ : ℝ=>3*Real.exp (-(σ^beta η)/5)) atTop (𝓝 0) := by
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hpow.atTop_div_const (by norm_num : (0:ℝ)<5))
    simpa only [Function.comp_apply,id_eq,neg_div,mul_zero] using ht.const_mul 3
  have ht6 := (tendsto_rpow_neg_atTop (by positivity : 0<1999*beta η)).const_mul 24
  have ht:=((((ht1.add ht2).add ht3).add ht4).add ht5).add ht6
  simp only [Function.comp_apply,mul_zero,add_zero] at ht
  have he : 0<η/2-3*beta η := by unfold beta;linarith
  have hsmall:=(tendsto_rpow_neg_atTop he).eventually_lt_const (by norm_num : (0:ℝ)<1/4)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_lt_const hρ,hsmall] with σ hσ hρ' hsmall
  intro D q r' h hlo hhi hq heq hr hhlo hhhi
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hDsmall : 2*(D*σ^(3*beta η))≤σ/2 := by
    have hl : D*σ^(3*beta η)≤σ*σ^(-(η/2-3*beta η)) := by
      calc
        _ ≤σ^(1-η/2)*σ^(3*beta η) := mul_le_mul_of_nonneg_right hhi (by positivity)
        _ =_ := by
          rw [←Real.rpow_add hs]
          nth_rw 2 [←Real.rpow_one σ]
          rw [←Real.rpow_add hs]
          congr 1
          ring
    nlinarith [mul_lt_mul_of_pos_left hsmall hs]
  exact (highFourLoss_bound hσ hb hlo hq heq hr hDsmall hhlo hhhi).trans (by simpa only [neg_mul] using hρ'.le)
end
end

open Filter Real ParameterHierarchy FiniteEntropy
open scoped Topology
noncomputable section

lemma eventually_stage_scale {η : ℝ} (_ : 0<η) (a δ : ℝ)
    (ha : a*beta η<η/2) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀D : ℝ,D≤σ^(1-η/2)→D*σ^(a*beta η)≤δ*σ := by
  have he : 0<η/2-a*beta η := sub_pos.mpr ha
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_neg_atTop he).eventually_lt_const hδ] with σ hσ ht
  intro D hD
  have hs : 0<σ := zero_lt_one.trans_le hσ
  calc
    _ ≤ σ^(1-η/2)*σ^(a*beta η) := mul_le_mul_of_nonneg_right hD (by positivity)
    _ = σ^(-(η/2-a*beta η))*σ := by
      rw [←Real.rpow_add hs,show 1-η/2+a*beta η= -(η/2-a*beta η)+1 by ring,
        Real.rpow_add hs,Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right ht.le hs.le

lemma highBadMass_le_highFourLoss (q r' h : ℕ) (hq : 1≤q) (s d ε : ℝ) (he : 0≤ε) :
    highBadMass s d 153≤highFourLoss q r' h s d ε := by
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  have hh : 0<5*(q:ℝ) := by linarith
  have hz : 0≤1-1/(5*(q:ℝ)) := sub_nonneg.mpr ((div_le_one hh).mpr (by linarith))
  unfold highFourLoss
  have h1 : 0≤64*(q:ℝ)^5*(2*Real.exp s/(q:ℝ)^r')*(Real.exp s/(q:ℝ)^4) := by positivity
  have h2 : 0≤3*(1-1/(5*(q:ℝ)))^h := by positivity
  have h3 : 0≤12*h*ε := by positivity
  linarith

lemma high_small_geometry {q s ε : ℝ} (hq : 0<q)
    (h1 : 80*Real.exp s≤q) (h2 : 256*Real.exp (2*s)≤q)
    (h3 : 640032*(ε*q)<1) :
    2*q^2*(2*Real.exp s/q^4)≤1/(20*q) ∧
    64*q^5*(Real.exp s/q^3)*(Real.exp s/q^3)≤(1:ℝ)/4 ∧
    80004*ε<1/(8*q) := by
  refine ⟨?_,?_,?_⟩
  · apply (le_div_iff₀ (by positivity : 0<20*q)).mpr
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg q)]
  · have he : Real.exp (2*s)=Real.exp s*Real.exp s := by rw [two_mul,Real.exp_add]
    rw [he] at h2
    have hh : 64*q^5*(Real.exp s/q^3)*(Real.exp s/q^3)=64*Real.exp s*Real.exp s/q := by field_simp
    rw [hh]
    exact (div_le_iff₀ hq).mpr (by linarith)
  · apply (lt_div_iff₀ (by positivity : 0<8*q)).mpr
    nlinarith

theorem eventually_high_geometry {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀D : ℝ,D≤σ^(1-η/2)→
      2*(Real.exp σ)^2*(2*Real.exp (D*σ^(3*beta η))/(Real.exp σ)^4)≤1/(20*Real.exp σ) ∧
      64*(Real.exp σ)^5*(Real.exp (D*σ^(3*beta η))/(Real.exp σ)^3)*
        (Real.exp (D*σ^(3*beta η))/(Real.exp σ)^3)≤(1:ℝ)/4 ∧
      80004*(σ^(-2000*beta η)/Real.exp σ)<1/(8*Real.exp σ) := by
  have ha : 3*beta η<η/2 := by unfold beta;linarith
  have ht : Tendsto (fun σ : ℝ=>640032*σ^(-2000*beta η)) atTop (𝓝 0) := by
    have hb : 0<2000*beta η := by exact mul_pos (by norm_num) (beta_pos hη)
    simpa only [neg_mul,mul_zero] using (tendsto_rpow_neg_atTop hb).const_mul 640032
  filter_upwards [eventually_stage_scale hη 3 (1/4) ha (by norm_num),
    eventually_ge_atTop (4*Real.log 256),eventually_ge_atTop (0:ℝ),
    ht.eventually_lt_const (by norm_num : (0:ℝ)<1)] with σ hscale hσ hσ0 he
  intro D hD
  have hs:=hscale D hD
  apply high_small_geometry (Real.exp_pos σ)
  · calc
      _ ≤256*Real.exp (D*σ^(3*beta η)) := mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_nonneg _)
      _ =Real.exp (Real.log 256+D*σ^(3*beta η)) := by rw [Real.exp_add,Real.exp_log (by norm_num)]
      _ ≤_ := Real.exp_le_exp.mpr (by linarith)
  · calc
      _ =Real.exp (Real.log 256+2*(D*σ^(3*beta η))) := by rw [Real.exp_add,Real.exp_log (by norm_num)]
      _ ≤_ := Real.exp_le_exp.mpr (by linarith)
  · simpa only [div_mul_cancel₀ _ (Real.exp_ne_zero σ)] using he
end

end SharpRamseyFive.Marking

end OAI
