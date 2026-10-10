import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.IntegerScales

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

lemma Kstar_lower {σ η D : ℝ} (hσ : 0<σ) (hDl : σ^beta η≤D) :
    σ^(7*beta η)≤ scaleKstar σ η D := by
  calc
    _ = σ^beta η*σ^(6*beta η) := by rw [←rpow_add hσ]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hDl (by positivity)

lemma K_ratio {σ η D : ℝ} (hσ : 0<σ) :
    scaleK σ η D=σ^(-3*beta η)*scaleKstar σ η D := by
  unfold scaleK scaleKstar
  rw [mul_left_comm,←rpow_add hσ]
  congr 2
  ring

lemma Kstar_inv_bound {σ η D : ℝ} (hσ : 0<σ) (hDl : σ^beta η≤D) :
    1≤σ^(-7*beta η)*scaleKstar σ η D := by
  have hh:=mul_le_mul_of_nonneg_left (Kstar_lower hσ hDl)
    (rpow_pos_of_pos hσ (-7*beta η)).le
  rw [←rpow_add hσ] at hh
  simpa only [show -7*beta η+7*beta η=0 by ring,rpow_zero] using hh

theorem eventually_open_regime (η : ℝ) (d : ℕ) (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop, ∀ D q : ℝ, σ^beta η≤D → 0<q →
      log 1024+3*scaleK σ η D<scaleKstar σ η D ∧
      (4*exp 1)^2*(20000*((d:ℝ)+3)^2*(σ^(-2000*beta η)/q))≤1/(4*q) := by
  have hb:=beta_pos hη
  have ht : Tendsto (fun σ : ℝ=>log 1024*σ^(-7*beta η)+3*σ^(-3*beta η)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun σ : ℝ=>σ^(-7*beta η)) atTop (𝓝 0) := by
      simpa only [neg_mul] using tendsto_rpow_neg_atTop (show 0<7*beta η by positivity)
    have h2 : Tendsto (fun σ : ℝ=>σ^(-3*beta η)) atTop (𝓝 0) := by
      simpa only [neg_mul] using tendsto_rpow_neg_atTop (show 0<3*beta η by positivity)
    simpa only [mul_zero,add_zero] using (h1.const_mul (log 1024)).add (h2.const_mul 3)
  have hs : Tendsto (fun σ : ℝ=>(4*exp 1)^2*(20000*((d:ℝ)+3)^2)*σ^(-2000*beta η)) atTop (𝓝 0) := by
    have he : Tendsto (fun σ : ℝ=>σ^(-2000*beta η)) atTop (𝓝 0) := by
      simpa only [neg_mul] using tendsto_rpow_neg_atTop (show 0<2000*beta η by positivity)
    simpa only [mul_zero] using he.const_mul ((4*exp 1)^2*(20000*((d:ℝ)+3)^2))
  filter_upwards [eventually_gt_atTop (0:ℝ),ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    hs.eventually (gt_mem_nhds (show (0:ℝ)<1/4 by norm_num))] with σ hσ ht hs D q hDl hq
  have hD : 0<D := (rpow_pos_of_pos hσ _).trans_le hDl
  have hg : 0<scaleKstar σ η D := by unfold scaleKstar; positivity
  constructor
  · have hl : log 1024≤log 1024*(σ^(-7*beta η)*scaleKstar σ η D) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (Kstar_inv_bound hσ hDl)
        (log_nonneg (show (1:ℝ)≤1024 by norm_num))
    rw [K_ratio hσ]
    have hh:=mul_lt_mul_of_pos_right ht hg
    nlinarith
  · have hh:=div_le_div_of_nonneg_right hs.le hq.le
    convert hh using 1 <;> first | rfl | ring

theorem eventually_open_deletion_small (η c ε : ℝ) (hη : 0<η) (hc : 0<c) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop, ∀ D w : ℝ,σ^beta η≤D → 0≤w →
      c*σ^(1+η/2)≤w*D →
      σ+(2*scaleK σ η D+log 64)*w≤ε*w*scaleKstar σ η D := by
  have hb:=beta_pos hη
  have he1 : Tendsto (fun σ : ℝ=>σ^(-η/2-6*beta η)) atTop (𝓝 0) := by
    simpa only [neg_add, neg_div, sub_eq_add_neg] using
      tendsto_rpow_neg_atTop (show 0<η/2+6*beta η by positivity)
  have he2 : Tendsto (fun σ : ℝ=>σ^(-3*beta η)) atTop (𝓝 0) := by
    simpa only [neg_mul] using tendsto_rpow_neg_atTop (show 0<3*beta η by positivity)
  have he3 : Tendsto (fun σ : ℝ=>σ^(-7*beta η)) atTop (𝓝 0) := by
    simpa only [neg_mul] using tendsto_rpow_neg_atTop (show 0<7*beta η by positivity)
  have ht : Tendsto (fun σ : ℝ=>c⁻¹*σ^(-η/2-6*beta η)+2*σ^(-3*beta η)+log 64*σ^(-7*beta η)) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using ((he1.const_mul c⁻¹).add (he2.const_mul 2)).add (he3.const_mul (log 64))
  filter_upwards [eventually_gt_atTop (0:ℝ),ht.eventually (gt_mem_nhds hε)] with σ hσ ht D w hDl hw hwD
  have hD : 0<D := (rpow_pos_of_pos hσ _).trans_le hDl
  have hg : 0≤ scaleKstar σ η D := by unfold scaleKstar; positivity
  have hfirst : σ≤c⁻¹*σ^(-η/2-6*beta η)*w*scaleKstar σ η D := by
    have hh:=mul_le_mul_of_nonneg_left hwD (show 0≤c⁻¹*σ^(-η/2) by positivity)
    have heq : c⁻¹*σ^(-η/2)*(c*σ^(1+η/2))=σ := by
      rw [mul_mul_mul_comm,inv_mul_cancel₀ (ne_of_gt hc),one_mul,←rpow_add hσ]
      simp only [show -η/2+(1+η/2)=1 by ring,rpow_one]
    rw [heq] at hh
    have heq2 : c⁻¹*σ^(-η/2)*(w*D)=c⁻¹*σ^(-η/2-6*beta η)*w*scaleKstar σ η D := by
      unfold scaleKstar
      have hrpow : σ^(-η/2-6*beta η)*σ^(6*beta η)=σ^(-η/2) := by
        rw [←rpow_add hσ]; congr 1; ring
      calc
        _ = c⁻¹*(σ^(-η/2-6*beta η)*σ^(6*beta η))*(w*D) := by rw [hrpow]
        _ = _ := by ring
    rwa [heq2] at hh
  have hlog : log 64*w≤log 64*σ^(-7*beta η)*w*scaleKstar σ η D := by
    have hh:=mul_le_mul_of_nonneg_left (Kstar_inv_bound hσ hDl)
      (show 0≤log 64*w from mul_nonneg (log_nonneg (show (1:ℝ)≤64 by norm_num)) hw)
    nlinarith
  have hh:=mul_le_mul_of_nonneg_right ht.le (mul_nonneg hw hg)
  rw [K_ratio hσ]
  nlinarith
end
end SharpLogRamsey.SourceScales

end

end OAI
