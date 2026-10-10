import Mathlib
import OAI.Combinatorics.KMedian.Process.ErasureDecay
import OAI.Combinatorics.KMedian.Sparse.SparseEnumeratedSurvival

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F : Type} [DecidableEq F] {Δ n : ℕ}

theorem enumerated_conditional_round_survival (A S : Finset (Copy (F := F) Δ))
    (G : A → Finset A) (H : Finset A)
    (enum : Fin n ≃ HeavyAction (graphActions G) H)
    (p : ℚ) (q : HeavyAction (graphActions G) H → ℚ)
    {x g h : ℝ} (d : F → ℝ) (hG : ∀ i, (G i).card=Δ)
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (_hh0 : 0 ≤ h)
    (hprob : (p:ℝ)=2*h*g) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ 2*(p:ℝ))
    (hsmall : (2*h*g)*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1) (hSA : S ⊆ A) :
    let D := heavyActions (graphActions G) H
    let μ := (SparseEnumeratedBatch.law enum (balancedActions D Δ) (balancedConflicts D Δ)
      p q hp hq0).real
    μ.expect (fun Z => mass g (roundAlive A S G H Z x g d)) ≤ (1-h/2)*mass g S := by
  intro D μ
  let T := fun Z => nextAliveAt D (Analytic.coefficient x (mass g S))
    (fun i => d i.val.1) (localSet A S \ forcedAlive A S H) Z
  have hin : ∀ i, (FiniteGraph.incoming D.erase i).card=Δ := fun i =>
    (heavy_incoming_card G H i).trans (hG i)
  have hp : ∀ i ∈ localSet A S, μ.prob (fun Z => i ∈ T Z) ≤ 1-h/2 := by
    intro i _
    let R := FiniteGraph.incoming D.erase i
    have herase := SparseEnumeratedBatch.erasure_at_least_quarter enum (balancedActions D Δ) R
      (balancedConflicts D Δ) p q hp hq0 hq
      (balancedConflicts_bound D Δ (fun i => le_of_eq (hin i)))
      (balancedConflicts_self D Δ) (by simpa only [R,hin i,hprob] using hsmall)
    rw [hprob] at herase
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
