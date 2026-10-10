import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.HighRankEndpoints
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalMarginals

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real Filter
open scoped Classical BigOperators Topology
noncomputable section

lemma high_upper_error_scale {x b κ δ H L₀ T N C : ℝ}
    (hx : 1≤x) (hb : 0≤b) (hC : 0≤C) (hκ : x^(4*b)≤κ)
    (hδ : δ≤κ*x^(-2*b)) (hnum : L₀+log T-H+N*exp (-L₀)≤δ+C) :
    (L₀+log T-H+N*exp (-L₀))/κ≤(1+C)*x^(-2*b) := by
  have hx0 : 0<x := by linarith
  have hp : 0<x^(2*b) := rpow_pos_of_pos hx0 _
  have hk : x^(2*b)≤κ := (rpow_le_rpow_of_exponent_le hx (by linarith)).trans hκ
  have hk0 : 0<κ := hp.trans_le hk
  have hi : 1/κ≤x^(-2*b) := by
    have hh:=one_div_le_one_div_of_le hp hk
    simpa only [neg_mul,rpow_neg hx0.le,one_div] using hh
  have hd : δ/κ≤x^(-2*b) := (div_le_iff₀ hk0).mpr (by simpa only [mul_comm κ] using hδ)
  calc
    _ ≤ (δ+C)/κ := div_le_div_of_nonneg_right hnum hk0.le
    _ = δ/κ+C*(1/κ) := by ring
    _ ≤ x^(-2*b)+C*x^(-2*b) := add_le_add hd (mul_le_mul_of_nonneg_left hi hC)
    _ = _ := by ring

variable {A B : Type*} [Fintype A] [Fintype B]

theorem actual_high_endpoint_errors (p : Law (A×B)) (S : Finset (A×B))
    (σ β D d r r' : ℝ) (hσ : 1≤σ) (hβ : 0≤β) (hD : σ^β≤D)
    (hs : ∀ z,z∉S→p.mass z=0)
    (hA : ((S.image Prod.fst).card:ℝ)≤1024*exp (r'*σ))
    (hB : ((S.image Prod.snd).card:ℝ)≤1024*exp (r*σ))
    (hS : (S.card:ℝ)≤64*exp (d*σ))
    (hfA : ∀ a,((univ.filter (fun b=>(a,b)∈S)).card:ℝ)≤2*exp ((d-r')*σ))
    (hfB : ∀ b,((univ.filter (fun a=>(a,b)∈S)).card:ℝ)≤2*exp ((d-r)*σ))
    (hdef : d*σ-entropy p≤D*σ^β) :
    let κ:=D*σ^(3*β)
    p.fst.event (univ.filter (fun a=>¬highGoodFirst p (1024*exp (r'*σ)) (d*σ) κ (exp (κ-r'*σ)) a))≤4300*σ^(-2*β) ∧
    p.snd.event (univ.filter (fun b=>¬highGoodSecond p (1024*exp (r*σ)) (d*σ) κ (exp (κ-r*σ)) b))≤4300*σ^(-2*β) ∧
    p.event (univ.filter (fun z=>exp (κ-d*σ)<p.mass z))≤65*σ^(-2*β) := by
  dsimp only
  have hσ0 : 0<σ := by linarith
  have hsc:=reciprocal_source_scales hσ0 hD
  have hk : 0<D*σ^(3*β) := (rpow_pos_of_pos hσ0 _).trans_le hsc.1
  have ha:=p.map_image_support S Prod.fst hs
  have hb:=p.map_image_support S Prod.snd hs
  rw [Law.map_fst] at ha
  rw [Law.map_snd] at hb
  have cap {N L : ℝ} (h : N≤64*exp L) : N*exp (-L)≤64 := by
    calc
      _ ≤ (64*exp L)*exp (-L) := mul_le_mul_of_nonneg_right h (exp_nonneg _)
      _ = _ := by rw [mul_assoc,←exp_add,add_neg_cancel,exp_zero,mul_one]
  have cap' {N L : ℝ} (h : N≤1024*exp L) : N*exp (-L)≤1024 := by
    calc
      _ ≤ (1024*exp L)*exp (-L) := mul_le_mul_of_nonneg_right h (exp_nonneg _)
      _ = _ := by rw [mul_assoc,←exp_add,add_neg_cancel,exp_zero,mul_one]
  have hcS:=cap hS
  have he:=endpoint_error_scale hσ hβ (by norm_num : (0:ℝ)≤64) hsc.1 hsc.2 hdef hcS
  have up (v : ℝ) (N : ℝ) (hN : N≤1024*exp (v*σ)) :
      (v*σ+log (2*exp ((d-v)*σ))-entropy p+N*exp (-(v*σ)))/(D*σ^(3*β))≤1027*σ^(-2*β) := by
    have hn : v*σ+log (2*exp ((d-v)*σ))-entropy p+N*exp (-(v*σ))≤D*σ^β+1026 := by
      rw [log_mul (by norm_num) (exp_ne_zero _),log_exp]
      have hl : log (2:ℝ)≤2 := (log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
      linarith [cap' hN]
    convert high_upper_error_scale hσ hβ (by norm_num : (0:ℝ)≤1026) hsc.1 hsc.2 hn using 1
    norm_num
  have heA:=high_first_bad p S (S.image Prod.fst) hs ha (1024*exp (r'*σ)) (d*σ) (r'*σ)
    (D*σ^(3*β)) (2*exp ((d-r')*σ)) (by positivity) hk (by positivity) hA hfA
  have heB:=high_second_bad p S (S.image Prod.snd) hs hb (1024*exp (r*σ)) (d*σ) (r*σ)
    (D*σ^(3*β)) (2*exp ((d-r)*σ)) (by positivity) hk (by positivity) hB hfB
  have hx : 0≤σ^(-2*β) := rpow_nonneg hσ0.le _
  refine ⟨?_,?_,?_⟩
  · linarith [up r' (S.image Prod.fst).card hA]
  · linarith [up r (S.image Prod.snd).card hB]
  · have hh:=p.heavy_atoms S hs (d*σ) hk
    have hm:=high_upper_error_scale (T:=1) (L₀:=d*σ) hσ hβ (by norm_num : (0:ℝ)≤64)
      hsc.1 hsc.2 (show d*σ+log 1-entropy p+S.card*exp (-(d*σ))≤D*σ^β+64 by simp only [log_one,add_zero]; linarith)
    simp only [log_one,add_zero] at hm
    norm_num only at hm
    exact hh.trans hm
end
end SharpLogRamsey.Selection

end

end OAI
