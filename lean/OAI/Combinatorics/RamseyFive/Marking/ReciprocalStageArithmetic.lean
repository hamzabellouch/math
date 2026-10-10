import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.WindowCodeDomains
import OAI.Combinatorics.RamseyFive.Marking.HighNumerics

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real Marking ProjectiveIncidence SelectedTuple
open scoped Topology NNReal
noncomputable section

def domainSlackConstant : ℝ := 4+Real.log 4+Real.log (2*(320/(9/100000)+320)^2)

lemma domainSlackConstant_pos : 0<domainSlackConstant := by
  have h1 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have h2 : 0≤Real.log (2*(320/(9/100000)+320)^2) := Real.log_nonneg (by norm_num)
  unfold domainSlackConstant
  linarith

lemma reciprocal_domain_slack_bound {σ η D : ℝ} (hη : 0<η) (hσ : 1≤σ)
    (hD : σ^beta η≤D) :
    codeDomainSlack (D*σ^(6*beta η)) (D*σ^(2*beta η))≤domainSlackConstant*D*σ^(6*beta η) := by
  have hb:=beta_pos hη
  have h1 : 1≤D := (Real.one_le_rpow hσ hb.le).trans hD
  have hpow : σ^(2*beta η)≤σ^(6*beta η) := Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
  have hpow1 : 1≤σ^(6*beta η) := Real.one_le_rpow hσ (by positivity)
  have hk : 1≤D*σ^(6*beta η) := by nlinarith
  have hl : 0≤Real.log 4+1+Real.log (2*(320/(9/100000)+320)^2) := by
    have h1 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
    have h2 : 0≤Real.log (2*(320/(9/100000)+320)^2) := Real.log_nonneg (by norm_num)
    linarith
  have hh:=mul_le_mul_of_nonneg_left hpow (show 0≤2*D by linarith)
  have hh':=mul_le_mul_of_nonneg_left hk hl
  dsimp only [codeDomainSlack,domainSlackConstant]
  nlinarith

lemma eventually_reciprocal_local_numbers {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀D : ℝ,σ^beta η≤D→D≤σ^(1-η/2)→
      2≤D*σ^(2*beta η) ∧
      Real.log 32+D*σ^(3*beta η)+3*(D*σ^(2*beta η))<σ ∧
      Real.log 32+3*(D*σ^(2*beta η))<D*σ^(3*beta η) ∧
      0≤D*σ^(6*beta η)+2*(D*σ^(2*beta η))+Real.log 4 ∧
      D*σ^(6*beta η)+2*(D*σ^(2*beta η))+Real.log 4≤(3+Real.log 4)*D*σ^(6*beta η) ∧
      ((4*Real.exp 1)^2*80004)*(σ^(-2000*beta η)/Real.exp σ)≤1/(4*Real.exp σ) := by
  have hb:=beta_pos hη
  have he : 0<2000*beta η := by positivity
  have ht : Tendsto (fun σ : ℝ=>4*((4*Real.exp 1)^2*80004)*σ^(-2000*beta η)) atTop (𝓝 0) := by
    simpa only [neg_mul,mul_zero] using (tendsto_rpow_neg_atTop he).const_mul (4*((4*Real.exp 1)^2*80004))
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (4*Real.log 32+1),
    (tendsto_rpow_atTop hb).eventually (eventually_ge_atTop (4+Real.log 32)),
    eventually_stage_scale hη 3 (1/16) (by unfold beta;linarith) (by norm_num),
    ht.eventually_lt_const (by norm_num : (0:ℝ)<1)] with σ hσ hs hg hscale hε
  intro D hD hDhi
  have hp : 0<σ := zero_lt_one.trans_le hσ
  have hl : 0≤Real.log 32 := Real.log_nonneg (by norm_num)
  have hl4 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have h1 : 1≤D := (Real.one_le_rpow hσ hb.le).trans hD
  have hs1 : 1≤D*σ^(2*beta η) := by
    have := Real.one_le_rpow hσ (show 0≤2*beta η by positivity)
    nlinarith
  have h2 : 2≤D*σ^(2*beta η) := by
    have hh : σ^beta η≤σ^(2*beta η) := Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
    nlinarith
  have h23 : D*σ^(2*beta η)≤D*σ^(3*beta η) := by
    apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hσ (by linarith)) (by linarith)
  have h6 : D*σ^(2*beta η)≤D*σ^(6*beta η) := by
    apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hσ (by linarith)) (by linarith)
  have hwide : Real.log 32+3*(D*σ^(2*beta η))<D*σ^(3*beta η) := by
    have heq : D*σ^(3*beta η)=(D*σ^(2*beta η))*σ^beta η := by
      rw [mul_assoc,←Real.rpow_add hp];congr 2;ring
    rw [heq]
    nlinarith
  refine ⟨h2,by have := hscale D hDhi;linarith,hwide,by positivity,?_,?_⟩
  · nlinarith
  · apply (le_div_iff₀ (by positivity : 0<4*Real.exp σ)).mpr
    have hh : ((4*Real.exp 1)^2*80004)*(σ^(-2000*beta η)/Real.exp σ)*(4*Real.exp σ)=
        4*((4*Real.exp 1)^2*80004)*σ^(-2000*beta η) := by field_simp
    rw [hh]
    exact hε.le

lemma eventually_public_integers {b : ℝ} (hb : 0<b) :
    ∀ᶠ σ : ℝ in atTop,∀w : ℕ,(w:ℝ)≤σ^2→
      let H:=⌈σ^(b/2)⌉₊
      let R:=⌈σ^b⌉₊
      1≤H ∧ w<2^H ∧ (H:ℝ)≤σ^b ∧ σ^b≤R ∧ (R:ℝ)≤2*σ^b+2 := by
  have hb2 : 0<b/2 := by linarith
  have ht := (isLittleO_log_rpow_atTop hb2).tendsto_div_nhds_zero
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hb2).eventually (eventually_ge_atTop (2:ℝ)),
    ht.eventually_lt_const (show (0:ℝ)<Real.log 2/3 by positivity)] with σ hσ hg hlog
  intro w hw
  dsimp only
  have hp : 0<σ := by linarith
  have hs : 0<σ^(b/2) := Real.rpow_pos_of_pos hp _
  have hceil:=Nat.le_ceil (σ^(b/2))
  have hceilhi:=Nat.ceil_lt_add_one hs.le
  have hpow : σ^(b/2)*σ^(b/2)=σ^b := by rw [←Real.rpow_add hp];congr 1;ring
  have hdepth : (3:ℝ)*Real.log σ≤(⌈σ^(b/2)⌉₊:ℝ)*Real.log 2 := by
    have hl : Real.log σ<(Real.log 2/3)*σ^(b/2) := (div_lt_iff₀ hs).mp hlog
    have hh:=mul_le_mul_of_nonneg_right hceil (show 0≤Real.log 2 by positivity)
    linarith
  have hpow3 : σ^3≤(2:ℝ)^⌈σ^(b/2)⌉₊ := by
    calc
      σ^3 = Real.exp (3*Real.log σ) := by simpa only [Nat.cast_ofNat,Real.exp_log hp] using (Real.exp_nat_mul (Real.log σ) 3).symm
      _ ≤ Real.exp ((⌈σ^(b/2)⌉₊:ℝ)*Real.log 2) := Real.exp_le_exp.mpr hdepth
      _ = _ := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  have hwlt : (w:ℝ)<(2:ℝ)^⌈σ^(b/2)⌉₊ := by
    apply (hw.trans_lt _).trans_le hpow3
    have := mul_pos (sq_pos_of_pos hp) (show 0<σ-1 by linarith)
    nlinarith
  refine ⟨?_,by exact_mod_cast hwlt,?_,Nat.le_ceil _,?_⟩
  · have hh : (1:ℝ)≤⌈σ^(b/2)⌉₊ := by linarith
    exact_mod_cast hh
  · rw [←hpow]
    nlinarith
  · have hh:=Nat.ceil_lt_add_one (Real.rpow_nonneg hp.le b)
    have hh':=Real.rpow_nonneg hp.le b
    linarith
end
end SharpRamseyFive.ParameterHierarchy

end OAI
