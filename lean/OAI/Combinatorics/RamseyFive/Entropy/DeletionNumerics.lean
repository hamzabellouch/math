import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.Beta

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section

lemma deletion_budget_monomial {σ q D k budget rounds rem C Cb Cc Cn b η : ℝ}
    (hσ : 1≤σ) (hq : 0<q) (hD : 0<D) (hk : 0≤k)
    (hCb : 0≤Cb) (hCc : 0≤Cc) (hCn : 0<Cn)
    (hb : budget≤Cb*k*D*σ^(-b))
    (hr : q*D*σ^(3000*b)/2≤rounds)
    (hn : q*σ^(1+η/2)/Cn≤rem) (hC : C≤Cc*σ*k) :
    budget/(D*σ^b)+(2*budget/rounds+C/rem)/(σ^(-2000*b)/q)≤
      k*(Cb*σ^(-2*b)+4*Cb*σ^(-1001*b)+Cc*Cn*σ^(2000*b-η/2)) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hround : 0<q*D*σ^(3000*b)/2 := by positivity
  have hrem : 0<q*σ^(1+η/2)/Cn := by positivity
  have hd : 0<D*σ^b := by positivity
  have he : 0<σ^(-2000*b)/q := by positivity
  have h1 : budget/(D*σ^b)≤Cb*k*σ^(-2*b) := by
    calc
      _ ≤ (Cb*k*D*σ^(-b))/(D*σ^b) := div_le_div_of_nonneg_right hb hd.le
      _ = Cb*k*(σ^(-b)/σ^b) := by field_simp
      _ = _ := by rw [←Real.rpow_sub hs];congr 2;ring
  have h2 : (2*budget/rounds)/(σ^(-2000*b)/q)≤4*Cb*k*σ^(-1001*b) := by
    have ht : 2*budget/rounds≤(2*(Cb*k*D*σ^(-b)))/(q*D*σ^(3000*b)/2) := by
      apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) (hround.trans_le hr).le).trans
      exact div_le_div_of_nonneg_left (by positivity) hround hr
    calc
      _ ≤ ((2*(Cb*k*D*σ^(-b)))/(q*D*σ^(3000*b)/2))/(σ^(-2000*b)/q) :=
        div_le_div_of_nonneg_right ht he.le
      _ =4*Cb*k*(σ^(-b)/(σ^(3000*b)*σ^(-2000*b))) := by field_simp;ring
      _ = _ := by rw [←Real.rpow_add hs,←Real.rpow_sub hs];congr 2;ring
  have h3 : (C/rem)/(σ^(-2000*b)/q)≤Cc*Cn*k*σ^(2000*b-η/2) := by
    have ht : C/rem≤(Cc*σ*k)/(q*σ^(1+η/2)/Cn) := by
      apply (div_le_div_of_nonneg_right hC (hrem.trans_le hn).le).trans
      exact div_le_div_of_nonneg_left (by positivity) hrem hn
    calc
      _ ≤ ((Cc*σ*k)/(q*σ^(1+η/2)/Cn))/(σ^(-2000*b)/q) :=
        div_le_div_of_nonneg_right ht he.le
      _ = Cc*Cn*k*(σ/(σ^(1+η/2)*σ^(-2000*b))) := by field_simp
      _ = _ := by
        rw [←Real.rpow_add hs]
        nth_rw 1 [←Real.rpow_one σ]
        rw [←Real.rpow_sub hs]
        congr 2
        ring
  rw [add_div]
  calc
    _ ≤ Cb*k*σ^(-2*b)+ (4*Cb*k*σ^(-1001*b)+Cc*Cn*k*σ^(2000*b-η/2)) :=
      add_le_add h1 (add_le_add h2 h3)
    _ = _ := by ring

theorem eventually_deletion_budget {η : ℝ} (hη : 0<η) (Cb Cc Cn ε : ℝ)
    (hCb : 0≤Cb) (hCc : 0≤Cc) (hCn : 0<Cn) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop,∀q D k budget rounds rem C : ℝ,
      0<q→0<D→0≤k→budget≤Cb*k*D*σ^(-beta η)→
      q*D*σ^(3000*beta η)/2≤rounds→q*σ^(1+η/2)/Cn≤rem→C≤Cc*σ*k→
      budget/(D*σ^beta η)+(2*budget/rounds+C/rem)/(σ^(-2000*beta η)/q)≤ε*k := by
  have hb:=beta_pos hη
  have h1 : 0<2*beta η := by positivity
  have h2 : 0<1001*beta η := by positivity
  have h3 : 0<η/2-2000*beta η := by unfold beta;linarith
  have ht : Tendsto (fun σ : ℝ=>Cb*σ^(-2*beta η)+4*Cb*σ^(-1001*beta η)+
      Cc*Cn*σ^(2000*beta η-η/2)) atTop (𝓝 0) := by
    convert ((tendsto_rpow_neg_atTop h1).const_mul Cb).add
      ((tendsto_rpow_neg_atTop h2).const_mul (4*Cb)) |>.add
      ((tendsto_rpow_neg_atTop h3).const_mul (Cc*Cn)) using 1 <;> ring_nf
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_lt_const hε] with σ hσ hsmall
  intro q D k budget rounds rem C hq hD hk hb hr hn hC
  exact (deletion_budget_monomial hσ hq hD hk hCb hCc hCn hb hr hn hC).trans
    (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hsmall.le hk)
end
end SharpRamseyFive.ParameterHierarchy

end OAI
