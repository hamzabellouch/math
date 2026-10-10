import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.Beta

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics Real
open scoped Topology
noncomputable section

lemma stage_cost_monomial {σ D P H w Cw b η : ℝ} (hσ : 1≤σ)
    (hD : 0≤D) (hP : 0≤P) (hH : 0≤H) (hw : 0≤w) (_hC : 0≤Cw)
    (hb : 0≤b) (hη : 0≤η)
    (hP' : P≤4*D*σ^(9*b)) (hH' : H≤σ^b)
    (hw' : D*w≤Cw*σ^(1+η/2)) :
    P*H*(σ+w*P)≤(4+16*Cw)*D*σ^(1+η/2+19*b) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hPH : P*H≤4*D*σ^(10*b) := by
    calc
      _ ≤ (4*D*σ^(9*b))*σ^b := mul_le_mul hP' hH' hH (by positivity)
      _ = _ := by rw [mul_assoc,←Real.rpow_add hs];congr 2;ring
  have hwP : w*P≤4*Cw*σ^(1+η/2+9*b) := by
    calc
      w*P≤w*(4*D*σ^(9*b)) := mul_le_mul_of_nonneg_left hP' hw
      _ =4*(D*w)*σ^(9*b) := by ring
      _ ≤4*(Cw*σ^(1+η/2))*σ^(9*b) := by gcongr
      _ = _ := by rw [Real.rpow_add hs (1+η/2) (9*b)];ring
  have hfirst : (4*D*σ^(10*b))*σ≤4*D*σ^(1+η/2+19*b) := by
    calc
      _ =4*D*σ^(1+10*b) := by rw [Real.rpow_add hs,Real.rpow_one];ring
      _ ≤_ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hσ (by linarith)) (by positivity)
  have hsecond : (4*D*σ^(10*b))*(4*Cw*σ^(1+η/2+9*b))=
      16*Cw*D*σ^(1+η/2+19*b) := by
    calc
      _ =16*Cw*D*(σ^(10*b)*σ^(1+η/2+9*b)) := by ring
      _ =_ := by rw [←Real.rpow_add hs];congr 2;ring
  calc
    P*H*(σ+w*P)≤(4*D*σ^(10*b))*(σ+4*Cw*σ^(1+η/2+9*b)) :=
      mul_le_mul hPH (add_le_add le_rfl hwP) (by positivity) (by positivity)
    _ = (4*D*σ^(10*b))*σ+(4*D*σ^(10*b))*(4*Cw*σ^(1+η/2+9*b)) := by ring
    _ ≤4*D*σ^(1+η/2+19*b)+16*Cw*D*σ^(1+η/2+19*b) := by rw [hsecond];exact add_le_add hfirst le_rfl
    _ =_ := by ring

theorem eventually_stage_entropy_bound {η : ℝ} (hη : 0<η)
    (C Cw : ℝ) (hC : 0≤C) (hCw : 0≤Cw) :
    ∀ᶠ σ : ℝ in atTop,∀ (q D P H w k Λ : ℝ),0<q→0≤D→0≤P→0≤H→0≤w→
      P≤4*D*σ^(9*beta η)→H≤σ^beta η→D*w≤Cw*σ^(1+η/2)→
      q*σ^(1+η)≤2*k→Λ≤C*q*(P*H*(σ+w*P))→Λ/k≤D*σ^(-η/3) := by
  have he : 0<η/6-19*beta η := by unfold beta;linarith
  have ht : Tendsto (fun σ : ℝ=>2*C*(4+16*Cw)*σ^(-(η/6-19*beta η))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop he).const_mul (2*C*(4+16*Cw))
  filter_upwards [eventually_ge_atTop (1:ℝ),
    ht.eventually_lt_const (by norm_num : (0:ℝ)<1)] with σ hσ hsmall
  intro q D P H w k Λ hq hD hP hH hw hP' hH' hw' hk hΛ
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hkp : 0<k := by have := mul_pos hq (Real.rpow_pos_of_pos hs (1+η));linarith
  have hmono:=stage_cost_monomial hσ hD hP hH hw hCw (beta_pos hη).le hη.le hP' hH' hw'
  have h1 : Λ≤C*q*((4+16*Cw)*D*σ^(1+η/2+19*beta η)) :=
    hΛ.trans (mul_le_mul_of_nonneg_left hmono (by positivity))
  have hpow : σ^(1+η/2+19*beta η)=σ^(-(η/6-19*beta η))*σ^(-η/3)*σ^(1+η) := by
    rw [←Real.rpow_add hs,←Real.rpow_add hs]
    congr 1
    ring
  have hsmall' : 2*C*(4+16*Cw)*σ^(-(η/6-19*beta η))≤1 := hsmall.le
  have h2 : C*q*((4+16*Cw)*D*σ^(1+η/2+19*beta η))≤D*σ^(-η/3)*k := by
    rw [hpow]
    calc
      _ = (2*C*(4+16*Cw)*σ^(-(η/6-19*beta η)))*(D*σ^(-η/3))*(q*σ^(1+η)/2) := by ring
      _ ≤ 1*(D*σ^(-η/3))*(2*k/2) := by gcongr
      _ = _ := by ring
  exact (div_le_iff₀ hkp).mpr (h1.trans h2)

theorem eventually_stage_recurrence {η : ℝ} (hη : 0<η) (CΔ : ℝ) (_hCΔ : 0≤CΔ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D A Δ : ℝ),0≤D→A≤D*σ^(-η/3)→Δ≤CΔ*D*σ^(6*beta η)→
      σ^beta η*(1+A+Δ*σ^(-η))≤σ^(2*beta η)+D*σ^(-η/4) := by
  have h1 : 0<η/12-beta η := by unfold beta;linarith
  have h2 : 0<3*η/4-7*beta η := by unfold beta;linarith
  have ht1:=tendsto_rpow_neg_atTop h1
  have ht2 : Tendsto (fun σ : ℝ=>CΔ*σ^(-(3*η/4-7*beta η))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop h2).const_mul CΔ
  filter_upwards [eventually_ge_atTop (1:ℝ),
    ht1.eventually_lt_const (by norm_num : (0:ℝ)<1/2),
    ht2.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with σ hσ hs1 hs2
  intro D A Δ hD hA hΔ
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hbase : σ^beta η≤σ^(2*beta η) := Real.rpow_le_rpow_of_exponent_le hσ (by have := beta_pos hη;linarith)
  have hp1 : σ^beta η*(D*σ^(-η/3))=D*σ^(-η/4)*σ^(-(η/12-beta η)) := by
    calc
      _ =D*(σ^beta η*σ^(-η/3)) := by ring
      _ =_ := by rw [←Real.rpow_add hs,mul_assoc,←Real.rpow_add hs];congr 2;ring
  have hp2 : σ^beta η*(CΔ*D*σ^(6*beta η)*σ^(-η))=
      D*σ^(-η/4)*(CΔ*σ^(-(3*η/4-7*beta η))) := by
    calc
      _ =CΔ*D*(σ^beta η*σ^(6*beta η)*σ^(-η)) := by ring
      _ =_ := by rw [←Real.rpow_add hs,←Real.rpow_add hs];
                 rw [show D*σ^(-η/4)*(CΔ*σ^(-(3*η/4-7*beta η)))=
                   CΔ*D*(σ^(-η/4)*σ^(-(3*η/4-7*beta η))) by ring,
                   ←Real.rpow_add hs];congr 2;ring
  calc
    _ ≤ σ^beta η*(1+D*σ^(-η/3)+(CΔ*D*σ^(6*beta η))*σ^(-η)) := by gcongr
    _ = σ^beta η+D*σ^(-η/4)*σ^(-(η/12-beta η))+
        D*σ^(-η/4)*(CΔ*σ^(-(3*η/4-7*beta η))) := by
      rw [mul_add,mul_add,mul_one,hp1,hp2]
    _ ≤ σ^(2*beta η)+D*σ^(-η/4)*(1/2)+D*σ^(-η/4)*(1/2) := by gcongr
    _ = _ := by ring
end
end SharpRamseyFive.ParameterHierarchy

end OAI
