import Mathlib
import OAI.Combinatorics.KMedian.Process.StateInvariants
import OAI.Combinatorics.KMedian.Process.AveragedCount

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch Analytic
variable {F J X : Type*} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J]
variable [PseudoMetricSpace X] {Δ : ℕ}

theorem exists_round_with_count (s : State F J Δ) (S₀ : J → Finset (Copy (F := F) Δ))
    (location : F → X) (client : J → X) (R : J → ℝ) (b : ℝ) {x g h φ : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) (hunit : g*(Δ:ℝ)=1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hh : 0 < h) (hφ : 0 < φ) (hb : 0 < b) (hcount : 8*(2*h*g)*(Δ:ℝ) ≤ φ*g) (hp1 : (1+φ)*(2*h*g) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g)
    (hsurv : (2*h*g)*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1)
    (hR : ∀ j, 0 ≤ R j) (hm : ∀ j, mass g (S₀ j)=1)
    (hd : ∀ j i, i ∈ S₀ j → dist (client j) (location i.1) ≤ R j)
    (hmax : ∀ j, ∃ i ∈ S₀ j, R j=dist (client j) (location i.1))
    (hv : Valid g location client R S₀ s) :
    ∃ ν : FiniteLaw (State F J Δ),
      (∀ t, 0 < ν.weight t → Valid g location client R S₀ t) ∧
      (∀ j, ν.expect (fun t => mass g (t.2 j)) ≤ (1-h/2)*mass g (s.2 j)) ∧
      (ν.prob (fun t => mass g s.1+4/(g*b) < mass g t.1) ≤ 96*(Δ:ℝ)^2*b/((2*h*g)*φ^2*g)) ∧
      ∀ j, ν.expect (fun t => statePotential R (fun j f => dist (client j) (location f))
        (x*Real.exp (-h)) g t j) ≤
        statePotential R (fun j f => dist (client j) (location f)) x g s j+
        h*g*PhysicalPotential.cost g (fun i => dist (client j) (location i.1)) (s.2 j)+
        batchConstant Δ*h*(φ+h)*R j := by
  classical
  have htotal : 1 ≤ ∑ _i : s.1, g := by
    simpa only [mass,sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,mul_comm g] using hv.1
  obtain ⟨D,μ,hgood,hfirst,hpair⟩ := Taper.exists_graph Δ
    (fun i : s.1 => location i.val.1) (own Δ s.1) hg hunit (P_pos hx0) (P_le_half hx0)
    htotal (fun i a ha => by rw [(mem_own Δ s.1 i a).mp ha,dist_self]) (own_card_le Δ s.1)
  let m := fun (G : s.1 → Finset s.1) a => mass g ((graphActions G).erase a)
  let H := fun G => univ.filter (fun a => max 1 (b*SourceBalance.amount (m G)) < m G a)
  let q := fun (G : s.1 → Finset s.1) (e : HeavyAction (graphActions G) (H G)) =>
    SourceBalance.bias (m G) (2*h*g) φ (heavyParent (graphActions G) (H G) e)
  have hp0 : 0 ≤ 2*h*g := by positivity
  have hq : ∀ G e, 2*h*g ≤ q G e ∧ q G e ≤ (1+φ)*(2*h*g) :=
    fun G e => ⟨SourceBalance.bias_lower (m G) hp0 hφ0 _, SourceBalance.bias_upper (m G) hp0 hφ0 _⟩
  have hq0 : ∀ G e, 0 ≤ q G e := fun G e => hp0.trans (hq G e).1
  have hq1 : ∀ G e, q G e ≤ 1 := fun G e => (hq G e).2.trans hp1
  have hpp1 : 2*h*g ≤ 1 := (le_mul_of_one_le_left hp0 (by linarith only [hφ0])).trans hp1
  let ν := roundLaw s μ H q x g h (fun j f => dist (client j) (location f)) hp0 hpp1 hq0 hq1
  refine ⟨ν,?_,?_,?_,?_⟩
  · exact roundLaw_valid s S₀ location client R D μ H q x h hp0 hpp1 hq0 hq1 hg.le hunit
      (P_pos hx0) (P_le_half hx0) hR hm hd hgood hv
  · intro j
    apply roundLaw_survival s μ H q x g h _ hg.le hunit hh0 hpp1 hq0 hq1 _ hsurv
      (fun G hG => (hgood G hG).1) hv.2.1 j
    intro G e
    exact ⟨(hq G e).1,(hq G e).2.trans (mul_le_mul_of_nonneg_right (by linarith only [hφ1]) hp0)⟩
  · exact roundLaw_count_tail s μ _ x hg hg1 hh hφ hφ1 hb hunit hp1 hcount
      (fun G hG => (hgood G hG).1)
  · intro j
    have hh := roundLaw_drift s S₀ R location client D μ H q hg hg1 hunit hx0 hx1 hh0 hh1
      hpp1 hφ0 hφ1 hq0 hq1 hq hsmall (P_nonneg x) (P_le_half hx0)
      (show 0 ≤ (0:ℝ) by norm_num) (show (0:ℝ) < 1/4 by norm_num)
      (by rw [sub_self,abs_zero]) hgood hfirst hpair hv.2.1 hv.2.2.1 hm hR hd hmax j
    simpa only [mul_zero,add_zero] using hh

end MetricKMedian.CopyState
end
end

end OAI
