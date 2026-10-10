import Mathlib
import OAI.Combinatorics.KMedian.Probability.ProbabilitySupport
import OAI.Combinatorics.KMedian.Process.PhysicalRound
import OAI.Combinatorics.KMedian.Process.SurvivalProbability

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset PhysicalPotential
variable {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]

theorem expected_mass_subset (μ : FiniteLaw Ω) (T : Ω → Finset I) (S : Finset I)
    {g ρ : ℝ} (hg : 0 ≤ g) (hsub : ∀ ω, T ω ⊆ S)
    (hp : ∀ i ∈ S, μ.prob (fun ω => i ∈ T ω) ≤ ρ) :
    μ.expect (fun ω => mass g (T ω)) ≤ ρ*mass g S := by
  have he : μ.expect (fun ω => mass g (T ω))=
      ∑ i, μ.prob (fun ω => i ∈ T ω)*g := by
    have hh := BatchRemainder.expect_selected_sum μ T (fun _ => g)
    simpa only [sum_const,nsmul_eq_mul,mass,mul_comm g] using hh
  rw [he]
  have hzero : ∀ i, i ∉ S → μ.prob (fun ω => i ∈ T ω)=0 := by
    intro i hi
    unfold prob
    have hp : (fun ω => if i ∈ T ω then (1:ℝ) else 0)=fun _ => 0 := by
      funext ω
      rw [ite_eq_right (fun hm => hi (hsub ω hm))]
    rw [hp,expect_const]
  have hsum := sum_le_sum (s := univ) (f := fun i => μ.prob (fun ω => i ∈ T ω)*g)
    (g := fun i => if i ∈ S then ρ*g else 0) (fun i _ => ?_)
  · have he' : (∑ i, if i ∈ S then ρ*g else 0)=ρ*mass g S := by
      rw [← sum_filter]
      simp only [filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul,mass]
      ring
    exact hsum.trans_eq he'
  · by_cases hi : i ∈ S
    · rw [ite_eq_left hi]
      exact mul_le_mul_of_nonneg_right (hp i hi) hg
    · rw [ite_eq_right hi,hzero i hi,zero_mul]

end MetricKMedian.FiniteLaw

namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F : Type*} [DecidableEq F] {Δ : ℕ}

theorem conditional_round_survival (A S : Finset (Copy (F := F) Δ))
    (G : A → Finset A) (H : Finset A) (q : HeavyAction (graphActions G) H → ℝ)
    {x g h : ℝ} (d : F → ℝ) (hG : ∀ i, (G i).card=Δ)
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (hh0 : 0 ≤ h)
    (hp1 : 2*h*g ≤ 1) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hq : ∀ e, 2*h*g ≤ q e ∧ q e ≤ 2*(2*h*g))
    (hsmall : (2*h*g)*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1) (hSA : S ⊆ A) :
    let D := heavyActions (graphActions G) H
    let μ := PhysicalBatchLaw.law (balancedActions D Δ) (balancedConflicts D Δ)
      (2*h*g) q (by positivity) hp1 hq0 hq1
    μ.expect (fun Z => mass g (roundAlive A S G H Z x g d)) ≤ (1-h/2)*mass g S := by
  intro D μ
  let T := fun Z => nextAliveAt D (Analytic.coefficient x (mass g S))
    (fun i => d i.val.1) (localSet A S \ forcedAlive A S H) Z
  have hin : ∀ i, (FiniteGraph.incoming D.erase i).card=Δ := fun i =>
    (heavy_incoming_card G H i).trans (hG i)
  have hp : ∀ i ∈ localSet A S, μ.prob (fun Z => i ∈ T Z) ≤ 1-h/2 := by
    intro i _
    let R := FiniteGraph.incoming D.erase i
    have herase := PhysicalBatchLaw.erasure_at_least_quarter (balancedActions D Δ) R
      (balancedConflicts D Δ) (2*h*g) q (by positivity) hp1 hq0 hq1 hq
      (balancedConflicts_bound D Δ (fun i => le_of_eq (hin i)))
      (balancedConflicts_self D Δ) (by simpa only [R,hin i] using hsmall)
    change (R.card:ℝ)*(2*h*g)/4 ≤ μ.prob _ at herase
    have he : μ.prob (fun Z => i ∈ T Z) ≤ μ.prob (fun Z => ¬∃ e ∈ R, e ∈ Z) := by
      apply μ.prob_mono
      intro Z hi ⟨e,he,heZ⟩
      have hh := (mem_sdiff.mp (nextAliveAt_subset_physical _ _ _ _ _ hi)).2
      exact hh (mem_biUnion.mpr ⟨e,heZ,(mem_filter.mp he).2⟩)
    rw [μ.prob_compl] at he
    have hc : (R.card:ℝ)*(2*h*g)/4=h/2 := by
      rw [show R.card=Δ from hin i]
      calc
        _ = (g*(Δ:ℝ))*h/2 := by ring
        _ = h/2 := by rw [hunit,one_mul]
    rw [hc] at herase
    linarith only [herase,he]
  have hh := μ.expected_mass_subset T (localSet A S) hg
    (fun Z => (nextAliveAt_subset _ _ _ _ _).trans sdiff_subset) hp
  simpa only [roundAlive,image_mass,localSet_mass A S hSA,T] using hh

end MetricKMedian.CopyState
end
end

end OAI
