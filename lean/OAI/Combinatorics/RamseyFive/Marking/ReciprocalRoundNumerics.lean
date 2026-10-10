import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.Beta

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section

lemma reciprocal_round_ratio {σ q D η c C Cₘ w n B T rem M : ℝ}
    (_hη : 0<η) (hσ : 1≤σ) (hq : 0<q) (hc : 0<c) (hC : 0≤C) (hCm : 0≤Cₘ)
    (hD : σ^beta η≤D) (hw : 0≤w) (hn : 0<n) (_hB : 0≤B)
    (hBhi : B≤C*(4*w*n)*D*σ^(-beta η))
    (hT : q*D*σ^(3000*beta η)/2≤T)
    (hr : n/2≤rem) (_hM : 0≤M) (hMhi : M≤Cₘ*σ)
    (closed : Bool) (hlen : closed=true→c*q*σ^(1+η)≤n) :
    B/(D*σ^beta η)+(2*B/T+(if closed then 16*w*n*M/rem else 0))/(σ^(-2000*beta η)/q)≤
      (w*n)*(4*C*σ^(-2*beta η)+16*C*σ^(-1001*beta η)+
        (32*Cₘ/c)*σ^(2000*beta η-η)) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hDp : 0<D := (Real.rpow_pos_of_pos hs _).trans_le hD
  have hTp : 0<T := (by positivity : 0<q*D*σ^(3000*beta η)/2).trans_le hT
  have hrp : 0<rem := (by positivity : 0<n/2).trans_le hr
  have hp (a : ℝ) : 0<σ^a := Real.rpow_pos_of_pos hs a
  have hfirst : B/(D*σ^beta η)≤w*n*(4*C*σ^(-2*beta η)) := by
    calc
      _ ≤(C*(4*w*n)*D*σ^(-beta η))/(D*σ^beta η) := div_le_div_of_nonneg_right hBhi (by positivity)
      _ =w*n*(4*C*(σ^(-beta η)/σ^beta η)) := by field_simp
      _ =_ := by rw [←Real.rpow_sub hs];congr 3;ring
  have hsecond : (2*B/T)/(σ^(-2000*beta η)/q)≤w*n*(16*C*σ^(-1001*beta η)) := by
    calc
      _ ≤(2*(C*(4*w*n)*D*σ^(-beta η))/(q*D*σ^(3000*beta η)/2))/(σ^(-2000*beta η)/q) := by gcongr
      _ =w*n*(16*C*(σ^(-beta η)/(σ^(3000*beta η)*σ^(-2000*beta η)))) := by field_simp; ring
      _ =_ := by rw [←Real.rpow_add hs,←Real.rpow_sub hs];congr 3;ring
  have hthird : (if closed then 16*w*n*M/rem else 0)/(σ^(-2000*beta η)/q)≤
      w*n*((32*Cₘ/c)*σ^(2000*beta η-η)) := by
    cases closed with
    | false => simp only [Bool.false_eq_true,ite_false,zero_div];positivity
    | true =>
      simp only [ite_true]
      have hlen':=hlen rfl
      have hh : (16*w*n*M/rem)/(σ^(-2000*beta η)/q)≤32*w*Cₘ*q*σ/σ^(-2000*beta η) := by
        calc
          _ ≤(16*w*n*(Cₘ*σ)/(n/2))/(σ^(-2000*beta η)/q) := by gcongr
          _ =_ := by field_simp; ring
      apply hh.trans
      have he : 32*w*Cₘ*q*σ/σ^(-2000*beta η)=
          (32*Cₘ/c)*w*(c*q*σ^(1+η))*σ^(2000*beta η-η) := by
        rw [mul_assoc ((32*Cₘ/c)*w),mul_assoc (c*q),←Real.rpow_add hs]
        have he : 1+η+(2000*beta η-η)=1-(-2000*beta η) := by ring
        rw [he,Real.rpow_sub hs,Real.rpow_one]
        field_simp
      rw [he]
      calc
        _ ≤(32*Cₘ/c)*w*n*σ^(2000*beta η-η) := by gcongr
        _ =_ := by ring
  rw [add_div]
  nlinarith [hfirst,hsecond,hthird]

lemma eventually_reciprocal_round_fraction {η : ℝ} (hη : 0<η)
    (c C Cₘ δ : ℝ) (hc : 0<c) (hC : 0≤C) (hCm : 0≤Cₘ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ q D w n B T rem M : ℝ,
      0<q→σ^beta η≤D→0≤w→0<n→0≤B→B≤C*(4*w*n)*D*σ^(-beta η)→
      q*D*σ^(3000*beta η)/2≤T→n/2≤rem→0≤M→M≤Cₘ*σ→
      ∀closed : Bool,(closed=true→c*q*σ^(1+η)≤n)→
      B/(D*σ^beta η)+(2*B/T+(if closed then 16*w*n*M/rem else 0))/(σ^(-2000*beta η)/q)≤w*n*δ := by
  have h2 : 0<2*beta η := by have:=beta_pos hη;positivity
  have h1001 : 0<1001*beta η := by have:=beta_pos hη;positivity
  have h2000 : 0<η-2000*beta η := by unfold beta;linarith
  have ht : Tendsto (fun σ : ℝ=>4*C*σ^(-2*beta η)+16*C*σ^(-1001*beta η)+
      (32*Cₘ/c)*σ^(2000*beta η-η)) atTop (𝓝 0) := by
    have he : 2000*beta η-η= -(η-2000*beta η) := by ring
    simpa only [neg_mul,he,mul_zero,add_zero] using
      (((tendsto_rpow_neg_atTop h2).const_mul (4*C)).add
        ((tendsto_rpow_neg_atTop h1001).const_mul (16*C))).add
          ((tendsto_rpow_neg_atTop h2000).const_mul (32*Cₘ/c))
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_lt_const hδ] with σ hσ ht
  intro q D w n B T rem M hq hD hw hn hB hBhi hT hr hM hMhi closed hlen
  exact (reciprocal_round_ratio hη hσ hq hc hC hCm hD hw hn hB hBhi hT hr hM hMhi closed hlen).trans
    (mul_le_mul_of_nonneg_left ht.le (mul_nonneg hw hn.le))
end
end SharpRamseyFive.ParameterHierarchy

end OAI
