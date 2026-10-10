import Mathlib
import OAI.Combinatorics.KMedian.Probability.Conditioning
import OAI.Combinatorics.KMedian.Process.PhysicalProcess

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch Analytic
variable {F J X : Type*} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J]
variable [PseudoMetricSpace X] {Δ : ℕ}

omit [Fintype J] [DecidableEq J] in
 theorem statePotential_nonneg (s : State F J Δ) (S₀ : J → Finset (Copy (F := F) Δ))
    (location : F → X) (client : J → X) (R : J → ℝ) (x : ℝ) {g : ℝ}
    (hg : 0 ≤ g) (hR : ∀ j, 0 ≤ R j) (hm : ∀ j, mass g (S₀ j)=1)
    (hv : Valid g location client R S₀ s) (j : J) :
    0 ≤ statePotential R (fun j f => dist (client j) (location f)) x g s j := by
  have hy := (mass_mono hg (hv.2.2.1 j)).trans_eq (hm j)
  rw [statePotential,potential,← coefficient_eq]
  apply add_nonneg
  · exact mul_nonneg (le_trans (by norm_num) (coefficient_ge_one (mass_nonneg hg _)))
      (cost_nonneg hg (fun _ _ => dist_nonneg))
  · exact mul_nonneg (sub_nonneg.mpr hy) (GroupCap.cap_nonneg _ _ (hR j) (fun _ => dist_nonneg))

theorem exists_completed (A : Finset (Copy (F := F) Δ))
    (S₀ : J → Finset (Copy (F := F) Δ))
    (location : F → X) (client : J → X) (R : J → ℝ) {b g h φ : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) (hunit : g*(Δ:ℝ)=1)
    (hh : 0 < h) (hh1 : h ≤ 1) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hb : 0 < b)
    (hp1 : (1+φ)*(2*h*g) ≤ 1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g)
    (hsurv : (2*h*g)*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1)
    (hcount : 8*(2*h*g)*(Δ:ℝ) ≤ φ*g)
    (hR : ∀ j, 0 ≤ R j) (hm : ∀ j, mass g (S₀ j)=1)
    (hd : ∀ j i, i ∈ S₀ j → dist (client j) (location i.1) ≤ R j)
    (hmax : ∀ j, ∃ i ∈ S₀ j, R j=dist (client j) (location i.1))
    (hA : 1 ≤ mass g A) (hS : ∀ j, S₀ j ⊆ A) (T : ℕ)
    (hfail : (T:ℝ)*(96*(Δ:ℝ)^2*b/((2*h*g)*φ^2*g)) < 1) :
    ∃ O : Finset F, ∃ a : J → F,
      (∀ j, a j ∈ O) ∧ (O.card:ℝ) ≤ mass g A+(T:ℝ)*(4/(g*b)) ∧
      (∑ j, dist (client j) (location (a j))) ≤
      (∑ j, ((1+2/Real.exp 1)*PhysicalPotential.cost g (fun i => dist (client j) (location i.1)) (S₀ j)+
        (T:ℝ)*(h*g*PhysicalPotential.cost g (fun i => dist (client j) (location i.1)) (S₀ j)+
          batchConstant Δ*h*(φ+h)*R j)+5*R j*Real.exp (-(T:ℝ)*h/2))) /
        (1-(T:ℝ)*(96*(Δ:ℝ)^2*b/((2*h*g)*φ^2*g))) := by
  classical
  obtain ⟨ν,hvalid,hcnt,hsurvival,hpotential⟩ := exists_final_law A S₀ location client R hg hg1 hunit
    hh hh1 hφ hφ1 hb hp1 hsmall hsurv hcount hR hm hd hmax hA hS T
  let d := fun j f => dist (client j) (location f)
  let corr := fun (s : State F J Δ) j => statePotential R d (Real.exp (-(T:ℝ)*h)) g s j+5*R j*mass g (s.2 j)
  let score := fun s => ∑ j, max 0 (corr s j)
  have hc0 : ∀ s, 0 < ν.weight s → ∀ j, 0 ≤ corr s j := by
    intro s hs j
    apply add_nonneg
    · exact statePotential_nonneg s S₀ location client R _ hg.le hR hm (hvalid s hs) j
    · exact mul_nonneg (mul_nonneg (by norm_num) (hR j)) (mass_nonneg hg.le _)
  let bound := ∑ j, ((1+2/Real.exp 1)*PhysicalPotential.cost g (fun i => d j i.1) (S₀ j)+
    (T:ℝ)*(h*g*PhysicalPotential.cost g (fun i => d j i.1) (S₀ j)+batchConstant Δ*h*(φ+h)*R j)+
      5*R j*Real.exp (-(T:ℝ)*h/2))
  have hE : ν.expect score ≤ bound := by
    calc
      _ = ν.expect (fun s => ∑ j, corr s j) := by
        apply ν.expect_congr_support
        intro s hs
        apply sum_congr rfl
        exact fun j _ => max_eq_right (hc0 s hs j)
      _ = ∑ j, ν.expect (fun s => corr s j) := FiniteLaw.expect_sum _ _ _
      _ ≤ bound := by
        apply sum_le_sum
        intro j _
        dsimp only [corr]
        rw [FiniteLaw.expect_add,FiniteLaw.expect_mul]
        exact add_le_add (hpotential j) (mul_le_mul_of_nonneg_left (hsurvival j) (mul_nonneg (by norm_num) (hR j)))
  let good := fun s : State F J Δ => mass g s.1 ≤ mass g A+(T:ℝ)*(4/(g*b))
  have hgood : 1-(T:ℝ)*(96*(Δ:ℝ)^2*b/((2*h*g)*φ^2*g)) ≤ ν.prob good := by
    have hc := ν.prob_compl good
    have he : ν.prob (fun s => ¬good s) ≤ (T:ℝ)*(96*(Δ:ℝ)^2*b/((2*h*g)*φ^2*g)) := by
      simpa only [good,not_le] using hcnt
    linarith only [hc,he]
  obtain ⟨s,hs,hgood_s,hscore⟩ := ν.select_success_bound good score (sub_pos.mpr hfail) hgood
    (fun _ => sum_nonneg (fun _ _ => le_max_left _ _)) hE
  obtain ⟨O,_hO,hOs,hservice⟩ := complete_potential s S₀ location client R hg.le hunit hR hm hd (hvalid s hs)
    (x := Real.exp (-(T:ℝ)*h))
  choose a ha hcost using hservice
  refine ⟨O,a,ha,hOs.trans hgood_s,?_⟩
  apply le_trans _ hscore
  apply sum_le_sum
  intro j _
  exact (hcost j).trans (le_max_right 0 (corr s j))

end MetricKMedian.CopyState
end
end

end OAI
