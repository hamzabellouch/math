import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalCountLaw
import OAI.Combinatorics.KMedian.Sparse.SparseEnumeratedMixture
import OAI.Combinatorics.KMedian.Sparse.SparseCountInstantiation

namespace OAI

section
section
namespace MetricKMedian.SparseCopyState
open Finset FixedBatch PhysicalPotential SourceBalance CountStatistic CopyState
variable {F : Type} [DecidableEq F] {Δ n : ℕ}

theorem physical_count_tail (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    {g p : ℚ} {φ b : ℝ} (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hb : 0 < b) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hG : ∀ i, (G i).card=Δ) (hpp : 0 ≤ p ∧ p ≤ 1)
    (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ φ*(g:ℝ)) :
    let m := fun h => mass (g:ℝ) ((graphActions G).erase h)
    let H := univ.filter (fun h => max 1 (b*amount m) < m h)
    let D := heavyActions (graphActions G) H
    ∀ (enum : Fin n ≃ HeavyAction (graphActions G) H)
      (q : HeavyAction (graphActions G) H → ℚ) (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1),
    (∀ e, (q e:ℝ)=bias m (p:ℝ) φ (heavyParent (graphActions G) H e)) →
    (SparseEnumeratedBatch.law enum (balancedActions D Δ) (balancedConflicts D Δ) p q hpp hq).real.prob
      (fun Z => mass (g:ℝ) A+4/((g:ℝ)*b) < mass (g:ℝ) (next Δ A (roundErased A G H Z) (roundOpened A G H Z))) ≤
        96*(Δ:ℝ)^2*b/((p:ℝ)*φ^2*(g:ℝ)) := by
  classical
  dsimp only
  intro enum q hq hqcast
  let m := fun h => mass (g:ℝ) ((graphActions G).erase h)
  let H := univ.filter (fun h => max 1 (b*amount m) < m h)
  let D := heavyActions (graphActions G) H
  let bad := fun Z => mass (g:ℝ) A+4/((g:ℝ)*b) <
    mass (g:ℝ) (next Δ A (roundErased A G H Z) (roundOpened A G H Z))
  have hm := graph_mass_sum G hG hunit
  have hH : (H.card:ℝ) ≤ 2/((g:ℝ)*b) := heavy_card m hg hb (fun h => mass_nonneg hg.le _) hm
    (fun h hh => grid_imbalance Δ _ hg hunit hh)
  have hc : 2/((g:ℝ)*b) ≤ 4/((g:ℝ)*b) := div_le_div_of_nonneg_right (by norm_num) (mul_pos hg hb).le
  have hbalance : (SparseEnumeratedBernoulli.law enum (fun _ => p) (fun _ => hpp)).real.prob
      (fun ω => bad (PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω))=0 := by
    have he : (fun ω => bad (PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω))=
        (fun _ => False) := by
      funext ω
      apply propext
      constructor
      · intro hh
        have hbnd := balanced_count_change A G H ω hg.le hunit
        dsimp only [bad] at hh
        linarith only [hbnd,hH,hc,hh]
      · exact False.elim
    have hz := (SparseEnumeratedBernoulli.law enum (fun _ => p) (fun _ => hpp)).real.prob_congr
      (F := fun _ => False) (fun ω => (congrFun he ω).to_iff)
    exact hz.trans (FiniteLaw.prob_false _)
  have hunbalanced : (SparseEnumeratedBernoulli.law enum q hq).real.prob
      (fun ω => bad (PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω)) ≤
        96*(Δ:ℝ)^2*b/((p:ℝ)*φ^2*(g:ℝ)) := by
    by_cases hlarge : 1 < b*amount m
    · apply le_trans _ (SparseFixedCount.actual_count_tail G hg hg1 hp hφ hφ1 hb hunit hG hsmall hlarge enum q hq hqcast)
      apply FiniteLaw.prob_mono
      intro ω hh
      have hbnd := unbalanced_count_change A G H ω hg.le hunit
      dsimp only [bad] at hh
      linarith only [hh,hbnd,hH,hc]
    · have he : (fun ω => bad (PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω))=(fun _ => False) := by
        funext ω
        apply propext
        constructor
        · intro hh
          have hbnd := unbalanced_small_change A G hg hb hunit hG (le_of_not_gt hlarge) ω
          dsimp only [bad] at hh
          linarith only [hh,hbnd]
        · exact False.elim
      have hz := (SparseEnumeratedBernoulli.law enum q hq).real.prob_congr
        (F := fun _ => False) (fun ω => (congrFun he ω).to_iff)
      rw [hz,FiniteLaw.prob_false]
      positivity
  rw [SparseEnumeratedBatch.prob_eq]
  change (1/2)*(SparseEnumeratedBernoulli.law enum (fun _ => p) (fun _ => hpp)).real.prob (fun ω => bad (PhysicalBatchLaw.balanced _ _ ω))+
    (1/2)*(SparseEnumeratedBernoulli.law enum q hq).real.prob (fun ω => bad (PhysicalBatchLaw.unbalanced _ ω)) ≤ _
  rw [hbalance, mul_zero, zero_add]
  have hnonneg : 0 ≤ 96*(Δ:ℝ)^2*b/((p:ℝ)*φ^2*(g:ℝ)) := by positivity
  linarith only [hunbalanced,hnonneg]

end MetricKMedian.SparseCopyState
end
end

end OAI
