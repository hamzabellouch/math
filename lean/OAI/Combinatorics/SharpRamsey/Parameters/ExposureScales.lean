import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.IntegerScales

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

lemma rpow_ratio (x : ℝ) (hx : 0<x) (a b : ℝ) : x^a/x^b=x^(a-b) := by
  rw [rpow_sub hx]

theorem eventually_integer_bad_small (η C c ε : ℝ)
    (hη : 0<η) (hC : 0≤C) (hc : 0<c) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop, ∀ q D N budget M n k : ℝ,
      0<q → 0<D → 0≤N → budget≤C*N*D*σ^(-beta η) → M≤C*σ →
      c*q*D*σ^(3000*beta η)≤k → c*q*σ^(1+η/2)≤n →
      let a:=σ^(-2000*beta η)/q
      budget/(D*σ^beta η)+2*budget/(k*a)+4*N*M/(n*a)≤N*ε := by
  have hb:=beta_pos hη
  have hexp : 2000*beta η-η/2<0 := by dsimp [beta]; linarith
  have h1 : Tendsto (fun σ : ℝ=>C*σ^(-2*beta η)) atTop (𝓝 0) := by
    simpa only [mul_zero,neg_mul] using
      (tendsto_rpow_neg_atTop (by positivity : 0<2*beta η)).const_mul C
  have h2 : Tendsto (fun σ : ℝ=>(2*C/c)*σ^(-1001*beta η)) atTop (𝓝 0) := by
    simpa only [mul_zero,neg_mul] using
      (tendsto_rpow_neg_atTop (by positivity : 0<1001*beta η)).const_mul (2*C/c)
  have h3 : Tendsto (fun σ : ℝ=>(4*C/c)*σ^(2000*beta η-η/2)) atTop (𝓝 0) := by
    simpa only [mul_zero,neg_neg] using (tendsto_rpow_neg_atTop (neg_pos.mpr hexp)).const_mul (4*C/c)
  have ht := (h1.add h2).add h3
  simp only [add_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hε),eventually_gt_atTop (0:ℝ)] with σ hsmall hσ
  intro q D N budget M n k hq hD hN hbudget hM hk hn
  dsimp only
  let a:=σ^(-2000*beta η)/q
  have ha : 0<a := div_pos (rpow_pos_of_pos hσ _) hq
  have hka : c*D*σ^(1000*beta η)≤k*a := by
    have hh:=mul_le_mul_of_nonneg_right hk ha.le
    have he : (c*q*D*σ^(3000*beta η))*a=c*D*σ^(1000*beta η) := by
      dsimp [a]
      have hr : σ^(3000*beta η)*σ^(-2000*beta η)=σ^(1000*beta η) := by
        rw [←rpow_add hσ]; congr 1; ring
      calc
        _ = c*D*(σ^(3000*beta η)*σ^(-2000*beta η)) := by field_simp
        _ = _ := by rw [hr]
    rwa [he] at hh
  have hna : c*σ^(1+η/2-2000*beta η)≤n*a := by
    have hh:=mul_le_mul_of_nonneg_right hn ha.le
    have he : (c*q*σ^(1+η/2))*a=c*σ^(1+η/2-2000*beta η) := by
      dsimp [a]
      have hr : σ^(1+η/2)*σ^(-2000*beta η)=σ^(1+η/2-2000*beta η) := by
        rw [←rpow_add hσ]; congr 1; ring
      calc
        _ = c*(σ^(1+η/2)*σ^(-2000*beta η)) := by field_simp
        _ = _ := by rw [hr]
    rwa [he] at hh
  have hb0 : 0≤C*N*D*σ^(-beta η) := by positivity
  have hd0 : 0<D*σ^beta η := by positivity
  have hk0 : 0<c*D*σ^(1000*beta η) := by positivity
  have hn0 : 0<c*σ^(1+η/2-2000*beta η) := by positivity
  have hbnd1 : budget/(D*σ^beta η)≤N*(C*σ^(-2*beta η)) := by
    calc
      _ ≤ (C*N*D*σ^(-beta η))/(D*σ^beta η) := div_le_div_of_nonneg_right hbudget hd0.le
      _ = C*N*(σ^(-beta η)/σ^beta η) := by field_simp
      _ = _ := by
        rw [rpow_ratio σ hσ, show -beta η-beta η = -2*beta η by ring]
        ring
  have hbnd2 : 2*budget/(k*a)≤N*((2*C/c)*σ^(-1001*beta η)) := by
    calc
      _ ≤ (2*(C*N*D*σ^(-beta η)))/(k*a) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbudget (by norm_num)) (hk0.le.trans hka)
      _ ≤ (2*(C*N*D*σ^(-beta η)))/(c*D*σ^(1000*beta η)) :=
        div_le_div_of_nonneg_left (by positivity) hk0 hka
      _ = N*(2*C/c)*(σ^(-beta η)/σ^(1000*beta η)) := by field_simp
      _ = _ := by
        rw [rpow_ratio σ hσ, show -beta η-1000*beta η = -1001*beta η by ring]
        ring
  have hbnd3 : 4*N*M/(n*a)≤N*((4*C/c)*σ^(2000*beta η-η/2)) := by
    calc
      _ ≤ (4*N*(C*σ))/(n*a) := by
        apply div_le_div_of_nonneg_right _ (hn0.le.trans hna)
        gcongr
      _ ≤ (4*N*(C*σ))/(c*σ^(1+η/2-2000*beta η)) :=
        div_le_div_of_nonneg_left (by positivity) hn0 hna
      _ = N*(4*C/c)*(σ^(1:ℝ)/σ^(1+η/2-2000*beta η)) := by rw [rpow_one]; field_simp
      _ = _ := by
        rw [rpow_ratio σ hσ, show (1:ℝ)-(1+η/2-2000*beta η) = 2000*beta η-η/2 by ring]
        ring
  calc
    _ ≤ N*(C*σ^(-2*beta η))+N*((2*C/c)*σ^(-1001*beta η))+
        N*((4*C/c)*σ^(2000*beta η-η/2)) := add_le_add (add_le_add hbnd1 hbnd2) hbnd3
    _ = N*(C*σ^(-2*beta η)+(2*C/c)*σ^(-1001*beta η)+(4*C/c)*σ^(2000*beta η-η/2)) := by ring
    _ ≤ N*ε := mul_le_mul_of_nonneg_left hsmall.le hN
end
end SharpLogRamsey.SourceScales

end

end OAI
