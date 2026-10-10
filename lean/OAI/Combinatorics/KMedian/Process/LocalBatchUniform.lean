import Mathlib
import OAI.Combinatorics.KMedian.Process.BatchUniform
import OAI.Combinatorics.KMedian.Process.ForcedLocal

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I : Type*} [DecidableEq I] [Fintype I]

theorem actual_local_bound (G : I → Finset I) (H S F : Finset I) (Δ : ℕ)
    (q : HeavyAction (graphActions G) H → ℝ) {x g h φ R b b' : ℝ} (d : I → ℝ)
    (hG : ∀ i, (G i).card=Δ) (hg : 0 < g) (hg1 : g ≤ 1) (hunit : g*(Δ:ℝ)=1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hp1 : 2*h*g ≤ 1)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hq : ∀ e, 2*h*g ≤ q e ∧ q e ≤ (1+φ)*(2*h*g))
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction g)
    (hy : mass g S ≤ 1) (hF : F ⊆ S) (hHS : H ∩ S ⊆ F)
    (hd0 : ∀ i, 0 ≤ d i) (hR0 : 0 ≤ R) (hdR : ∀ i ∈ S, d i ≤ R)
    (hbQ : b ≤ 5*((PhysicalPotential.cost g d S+(1-mass g S)*b)/g))
    (hb0 : 0 ≤ b) (hbR : b ≤ 5*R) (hb'0 : 0 ≤ b') (hb' : b' ≤ b)
    (hbF : ∀ i ∈ F, b' ≤ d i) (hbH : ∀ i ∈ H, b' ≤ d i) :
    let D := heavyActions (graphActions G) H
    let μ := PhysicalBatchLaw.law (balancedActions D Δ) (balancedConflicts D Δ)
      (2*h*g) q (by positivity) hp1 hq0 hq1
    μ.expect (fun A => potential (x*Real.exp (-h)) g d
      (nextAliveAt D (coefficient x (mass g S)) d (S \ F) A)
      (nextCap D d b' A)-potential x g d S b) ≤
      h*(timeRate x (mass g S)*PhysicalPotential.cost g d S+
        g*(∑ e ∈ relevant (graphActions G) S, charge (graphActions G) x g b d S e))+
      batchConstant Δ*h*(φ+h)*R := by
  intro D μ
  have hcard : S.card ≤ Δ := card_le_grid hg hunit S hy
  have hin : ∀ i, (FiniteGraph.incoming D.erase i).card ≤ Δ :=
    fun i => le_of_eq ((heavy_incoming_card G H i).trans (hG i))
  have hD := heavy_relevant_bound G H S hcard hG
  have hFull := full_relevant_bound G S hcard hG
  have hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ 2*h*g := by
    intro e _
    have hpQ : 2*h*g ≤ 4*h*g := by nlinarith only [mul_nonneg hh0 hg.le]
    have hqQ : ∀ e, q e ≤ 4*h*g := by
      intro e
      have he := mul_le_mul_of_nonneg_right hφ1 (show 0 ≤ 2*h*g by positivity)
      linarith only [he,(hq e).2]
    have he := PhysicalBatchLaw.marginal_le (balancedActions D Δ) (balancedConflicts D Δ)
      (2*h*g) q (by positivity) hp1 hq0 hq1 (balancedConflicts_self D Δ) hpQ hqQ e
    change μ.prob _ ≤ _ at he
    linarith only [he]
  by_cases hFn : F.Nonempty
  · have hδ : g ≤ mass g F := by
      unfold mass
      have hf : (1:ℝ) ≤ F.card := by exact_mod_cast hFn.card_pos
      nlinarith only [mul_le_mul_of_nonneg_left hf hg.le]
    have hh := forced_step_local_bound D (graphActions G) μ d S F hx0 hx1 hg hg1 hh0 hh1
      hsmall hy hF hδ hd0 hb0 hbQ hb'0 hb' hbF hD hFull hmarg
    exact hh.trans (le_add_of_nonneg_right (by positivity [batchConstant_nonneg Δ]))
  · have hFe : F=∅ := not_nonempty_iff_eq_empty.mp hFn
    have hdis : Disjoint H S := by
      apply disjoint_left.mpr
      intro i hi hs
      have he := hHS (mem_inter.mpr ⟨hi,hs⟩)
      simp [hFe] at he
    have hheavy : ∀ e, e ∉ D.ordinary → b' ≤ d (D.source e) :=
      fun e he => hbH _ (nonordinary_parent_heavy G H e he)
    have hb := expected_step_bound D (balancedActions D Δ) (balancedConflicts D Δ) q
      hh0 hg.le hp1 hq0 hq1 hφ0 hφ1 hq (balancedConflicts_bound D Δ hin)
      (balancedConflicts_self D Δ) d S hx0 hx1 hR0 hd0 hdR
      hy hb0 hbR hb'0 hb' hheavy
    have hc := heavy_charge_le G H S hdis x g b d hg.le (fun i _ => hd0 i)
    have hcm := mul_le_mul_of_nonneg_left hc (mul_nonneg hh0 hg.le)
    have ho : (univ : Finset (relevant D S)).offDiag.card ≤ (relevant D S).card^2 := by
      rw [offDiag_card]
      simp only [card_univ,Fintype.card_coe]
      exact (Nat.sub_le _ _).trans_eq (pow_two _).symm
    have hr := uniform_remainder Δ (relevant D S).card
      (univ : Finset (relevant D S)).offDiag.card hD ho hh0 hg.le hg1 hφ0 hR0
    simp only [hFe,sdiff_empty]
    change μ.expect (fun A => potential (x*Real.exp (-h)) g d (nextAlive D x g d S A)
      (nextCap D d b' A)-potential x g d S b) ≤ _
    change μ.expect _ ≤ _ at hb
    nlinarith only [hb,hcm,hr]

end MetricKMedian.FixedBatch
end
end

end OAI
