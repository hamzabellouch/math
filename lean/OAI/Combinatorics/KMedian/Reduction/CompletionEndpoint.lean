import Mathlib
import OAI.Combinatorics.KMedian.Process.StateInvariants
import OAI.Combinatorics.KMedian.Geometry.GreedyCompletion

namespace OAI

section
section
namespace MetricKMedian.GroupCap
open Finset
variable {F : Type*}

theorem completed_distance (R : ℝ) (d : F → ℝ) (Q O : Finset F)
    (hQ : Q ⊆ O) (hbackup : ∃ f ∈ O, d f ≤ 5*R) :
    ∃ f ∈ O, d f ≤ cap R d Q := by
  have hh := (fold_min_le (s := Q) (b := 5*R) (f := d) (c := cap R d Q)).mp (le_refl _)
  rcases hh with hh | ⟨f,hf,hd⟩
  · obtain ⟨f,hf,hd⟩ := hbackup
    exact ⟨f,hf,hd.trans hh⟩
  · exact ⟨f,hQ hf,hd⟩

end MetricKMedian.GroupCap

namespace MetricKMedian.CopyState
open Finset PhysicalPotential Analytic
variable {F J X : Type*} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J]
variable [PseudoMetricSpace X] {Δ : ℕ}

theorem complete_potential (s : State F J Δ) (S₀ : J → Finset (Copy (F := F) Δ))
    (location : F → X) (client : J → X) (R : J → ℝ) {x g : ℝ}
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1)
    (hR : ∀ j, 0 ≤ R j) (hm : ∀ j, mass g (S₀ j)=1)
    (hd : ∀ j i, i ∈ S₀ j → dist (client j) (location i.1) ≤ R j)
    (hv : Valid g location client R S₀ s) :
    ∃ O : Finset F, integral Δ s.1 ⊆ O ∧ (O.card:ℝ) ≤ mass g s.1 ∧
      ∀ j, ∃ f ∈ O, dist (client j) (location f) ≤
        statePotential R (fun j f => dist (client j) (location f)) x g s j+
        5*R j*mass g (s.2 j) := by
  obtain ⟨O,hO,hcount,hnear⟩ := Completion.complete Δ hg hunit location client R hR s.1 S₀ hm hd hv.2.2.2
  refine ⟨O,hO,hcount,?_⟩
  intro j
  obtain ⟨f,hf,hfbound⟩ := GroupCap.completed_distance (R j) (fun f => dist (client j) (location f))
    (integral Δ s.1) O hO (hnear j)
  refine ⟨f,hf,hfbound.trans ?_⟩
  have hb := GroupCap.cap_le_radius (R j) (fun f => dist (client j) (location f)) (integral Δ s.1)
  have hy := mass_nonneg hg (s.2 j)
  have hv0 := cost_nonneg hg (d := fun i : Copy (F := F) Δ => dist (client j) (location i.1)) (S := s.2 j) (fun _ _ => dist_nonneg)
  have ha := coefficient_ge_one (x := x) hy
  have hm := mul_nonneg (show 0 ≤ coefficient x (mass g (s.2 j)) by linarith only [ha]) hv0
  have hby := mul_le_mul_of_nonneg_right hb hy
  rw [statePotential,potential,← coefficient_eq]
  nlinarith only [hm,hby]

omit [Fintype J] [DecidableEq J] [PseudoMetricSpace X] in
 theorem initial_potential (A : Finset (Copy (F := F) Δ)) (S₀ : J → Finset (Copy (F := F) Δ))
    (R : J → ℝ) (d : J → F → ℝ) {g : ℝ} (hm : ∀ j, mass g (S₀ j)=1) (j : J) :
    statePotential R d 1 g (A,S₀) j=(1+2/Real.exp 1)*PhysicalPotential.cost g (fun i => d j i.1) (S₀ j) := by
  rw [statePotential,potential]
  dsimp only
  rw [hm j,sub_self,zero_mul,add_zero,← coefficient_eq]
  rw [coefficient,sub_self,mul_zero,add_zero,A_one]

end MetricKMedian.CopyState
end
end

end OAI
