import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.HighRankExtraction

namespace OAI

section
namespace SharpLogRamsey.ActualHighRank
open Finset Real Filter HighRankBudgets
open scoped Topology BigOperators
noncomputable section

def rawRows (σ η : ℝ) : ℕ := ⌈exp σ*σ^beta η⌉₊
def rawThreshold (σ η : ℝ) : ℕ := ⌈(rawRows σ η:ℝ)/(10*exp σ)⌉₊
def richDensity : ℝ := 1/(100*exp (1/2))
def rawError (σ η D : ℝ) (d : ℕ) : ℝ :=
  4365*σ^(-2*beta η)+100*1024^2*exp (2*scaleK σ η D)/exp σ+
    (d*exp (-3*(rawRows σ η:ℝ)/(20*d*exp σ))+exp (1-(rawRows σ η:ℝ)/(10*exp σ)))+
    4*(rawRows σ η)* (2*σ^(-2000*beta η)/exp σ)+2048*exp (scaleK σ η D)/exp σ

lemma density_positive : 0<richDensity := by unfold richDensity; positivity
lemma density_small : richDensity≤1/20 := by
  have h : 1≤exp ((1:ℝ)/2) := one_le_exp (by norm_num)
  unfold richDensity
  apply (div_le_iff₀ (by positivity : 0<100*exp ((1:ℝ)/2))).mpr
  linarith
lemma density_scaled : 20*exp (1/2)*richDensity≤1 := by
  unfold richDensity
  rw [←mul_div_assoc,mul_one]
  apply (div_le_iff₀ (by positivity : 0<100*exp ((1:ℝ)/2))).mpr
  nlinarith [exp_pos ((1:ℝ)/2)]

lemma rawError_le {σ η D : ℝ} {d : ℕ} (hσ : 1≤σ) (hη : 0<η) (hd : 0<d) :
    rawError σ η D d≤error σ η D 5000 d := by
  have hσ0 : 0<σ := by linarith
  have hq : 1≤exp σ := one_le_exp (by linarith)
  have hx : 1≤σ^beta η := one_le_rpow hσ (by unfold beta; positivity)
  obtain ⟨hlo,hhi⟩:=row_size hq hx
  change exp σ*σ^beta η≤(rawRows σ η:ℝ) at hlo
  change (rawRows σ η:ℝ)≤2*exp σ*σ^beta η at hhi
  have h1 : -3*(rawRows σ η:ℝ)/(20*d*exp σ)≤-(3/(20*d))*σ^beta η := by
    apply (div_le_iff₀ (by positivity : 0<(20:ℝ)*d*exp σ)).mpr
    have he : -(3/((20:ℝ)*d))*σ^beta η*(20*d*exp σ)=-3*(exp σ*σ^beta η) := by field_simp
    rw [he]
    linarith
  have h2 : 1-(rawRows σ η:ℝ)/(10*exp σ)≤1-(1/10)*σ^beta η := by
    have hh:=(div_le_div_iff_of_pos_right (by positivity : 0<(10:ℝ)*exp σ)).mpr hlo
    have he : exp σ*σ^beta η/(10*exp σ)=(1/10)*σ^beta η := by field_simp
    rw [he] at hh
    linarith
  have h3 : 4*(rawRows σ η:ℝ)*(2*σ^(-2000*beta η)/exp σ)≤16*σ^(-(1999*beta η)) := by
    calc
      _ ≤ 4*(2*exp σ*σ^beta η)*(2*σ^(-2000*beta η)/exp σ) := by gcongr
      _ = 16*σ^(-(1999*beta η)) := by
        have he : σ^beta η*σ^(-2000*beta η)=σ^(-(1999*beta η)) := by
          rw [←rpow_add hσ0]; congr 1; ring
        calc
          _ = 16*(σ^beta η*σ^(-2000*beta η)) := by field_simp; ring
          _ = _ := by rw [he]
  have hg1:=mul_le_mul_of_nonneg_left (exp_le_exp.mpr h1) (show (0:ℝ)≤d by positivity)
  have hg2:=exp_le_exp.mpr h2

  have he2 : exp (1-(1/10)*σ^beta η)=exp 1*exp (-(1/10)*σ^beta η) := by
    rw [show -(1/10)*σ^beta η=-((1/10)*σ^beta η) by ring,exp_neg,exp_sub]; ring
  rw [he2] at hg2
  unfold rawError error
  have hp : 0≤σ^(-4*beta η) := rpow_nonneg hσ0.le _
  have hp' : 0≤σ^(-2*beta η) := rpow_nonneg hσ0.le _
  have hp'' : 0≤σ^(-(1999*beta η)) := rpow_nonneg hσ0.le _
  have he : 0≤exp (2*scaleK σ η D)/exp σ := by positivity
  have he' : 0≤exp (scaleK σ η D)/exp σ := by positivity
  simp only [show -(2*beta η)=-2*beta η by ring,show -(4*beta η)=-4*beta η by ring]
  simp only [mul_div_assoc] at *
  linarith

theorem eventual_budgets {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 0<d) :
    ∀ᶠ σ : ℝ in atTop, ∀ D : ℝ, σ^beta η≤D → D≤σ^(1-η/2) →
      1≤σ ∧ 2*d≤rawRows σ η ∧ d+2≤rawThreshold σ η ∧
      (rawRows σ η:ℝ)/(10*exp σ)≤rawThreshold σ η ∧
      (rawThreshold σ η:ℝ)≤(rawRows σ η:ℝ)/(10*exp σ)+1 ∧
      richDensity≤2048*exp (scaleK σ η D) ∧
      4300*σ^(-2*beta η)≤1/4 ∧ 20480*exp (scaleK σ η D)≤exp σ ∧
      rawError σ η D d≤1/8 := by
  have hb : 0<beta η := by unfold beta; positivity
  have ht:=tendsto_rpow_atTop hb
  have hs : Tendsto (fun σ : ℝ=>4300*σ^(-2*beta η)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (show 0<2*beta η by positivity)).const_mul 4300 using 1 <;> congr 2 <;> ring_nf
  filter_upwards [eventually_ge_atTop (1:ℝ),
    ht.eventually (eventually_ge_atTop (10*((d:ℝ)+2))),
    hs.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/4)),
    eventually_exp_K_over_q hη 20480 1 1 (by norm_num) (by norm_num) (by norm_num),
    eventually_error hη 5000 (1/8) (by norm_num) (by norm_num) d hd]
    with σ hσ hx hs he herr D hD hD'
  have hq : 1≤exp σ := one_le_exp (by linarith)
  have hx0 : 0≤σ^beta η := by positivity
  have hlo : exp σ*σ^beta η≤(rawRows σ η:ℝ) := Nat.le_ceil _
  have hlo' : σ^beta η≤(rawRows σ η:ℝ) := (le_mul_of_one_le_left hx0 hq).trans hlo
  have hh : 2*d≤rawRows σ η := by exact_mod_cast (show 2*(d:ℝ)≤(rawRows σ η:ℝ) by linarith)
  have hTlo : (rawRows σ η:ℝ)/(10*exp σ)≤rawThreshold σ η := Nat.le_ceil _
  have hThi : (rawThreshold σ η:ℝ)≤(rawRows σ η:ℝ)/(10*exp σ)+1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hT : d+2≤rawThreshold σ η := by
    have ht : (d:ℝ)+2≤(rawRows σ η:ℝ)/(10*exp σ) := by
      apply (le_div_iff₀ (by positivity : 0<10*exp σ)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hx (exp_nonneg σ)]
    exact_mod_cast ht.trans hTlo
  have hκ : 0 ≤ scaleK σ η D := mul_nonneg ((rpow_nonneg (by linarith) _).trans hD) (by positivity)
  have hu := density_small
  have hue : richDensity≤2048*exp (scaleK σ η D) := by
    have he : 1≤exp (scaleK σ η D) := one_le_exp hκ
    linarith
  have hescape : 20480*exp (scaleK σ η D)≤exp σ := by
    have h:=he D hD'
    rw [one_mul] at h
    exact ((div_lt_one (exp_pos σ)).mp h).le
  exact ⟨hσ,hh,hT,hTlo,hThi,hue,hs,hescape,(rawError_le hσ hη hd).trans (herr D hD').le⟩
end
end SharpLogRamsey.ActualHighRank

end

end OAI
