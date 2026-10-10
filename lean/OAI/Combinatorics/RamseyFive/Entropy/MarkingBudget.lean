import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.Beta

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section

lemma marking_budget_bound {σ q η k n A Δ E D : ℝ}
    (hσ : 1≤σ) (_hq : 0<q) (hk : 0<k) (hn : n≤k)
    (hA : 0≤A) (hΔ : 0≤Δ) (hE : E≤9600*q*σ)
    (hlen : q*σ^(1+η)≤2*k)
    (hD : D=σ^beta η*(1+A/k+Δ*σ^(-η))) :
    39*(A+n*Real.log 800+E*Δ)≤(39*(19201+Real.log 800))*k*D*σ^(-beta η) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hcancel : D*σ^(-beta η)=1+A/k+Δ*σ^(-η) := by
    rw [hD,mul_right_comm,←Real.rpow_add hs]
    simp
  have hbase : k*D*σ^(-beta η)=k+A+k*Δ*σ^(-η) := by
    rw [mul_assoc,hcancel]
    field_simp
  have hh : q*σ≤2*k*σ^(-η) := by
    have hh:=mul_le_mul_of_nonneg_right hlen (Real.rpow_nonneg hs.le (-η))
    have he : q*σ^(1+η)*σ^(-η)=q*σ := by
      rw [mul_assoc,←Real.rpow_add hs,show 1+η+-η=(1:ℝ) by ring,Real.rpow_one]
    rwa [he] at hh
  have hlog : 0≤Real.log 800 := Real.log_nonneg (by norm_num)
  have h1:=mul_le_mul_of_nonneg_right hE hΔ
  have h2:=mul_le_mul_of_nonneg_right hh hΔ
  have h3:=mul_le_mul_of_nonneg_right hn hlog
  have hx : 0≤k*Δ*σ^(-η) := by positivity
  have ha : 0≤A*Real.log 800 := mul_nonneg hA hlog
  have hb : 0≤(k*Δ*σ^(-η))*Real.log 800 := mul_nonneg hx hlog
  calc
    _ ≤39*(A+k*Real.log 800+19200*(k*Δ*σ^(-η))) := by nlinarith
    _ ≤(39*(19201+Real.log 800))*(k+A+k*Δ*σ^(-η)) := by nlinarith
    _ =_ := by rw [←hbase];ring

lemma marking_budget_length {σ D k l C c : ℝ} (hσ : 0≤σ) (hD : 0≤D)
    (hC : 0≤C) (hc : 0<c) (hlen : c*k≤l) (b : ℝ) :
    C*k*D*σ^b≤(C/c)*l*D*σ^b := by
  have hh : k≤l/c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hlen)
  calc
    _ ≤C*(l/c)*D*σ^b := by gcongr
    _ =_ := by ring
end
end SharpRamseyFive.ParameterHierarchy

end OAI
