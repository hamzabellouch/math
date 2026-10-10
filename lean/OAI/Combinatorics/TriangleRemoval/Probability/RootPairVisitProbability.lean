import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.PairRequired

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave
section RootForkVisitation
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem rootPairVisitProbability_fork (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 0 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (hkd : k ≤ d+1) (hkN : k ≤ N)
    (focus : Finset ι) (parent : Option τ)
    (a b' : gridCandidates H focus parent) (hab : a ≠ b')
    (as bs : List (ι × τ)) (ha : LegalQueryPath H ((H a.val.2).erase a.val.1) (some a.val.2) as)
    (hb' : LegalQueryPath H ((H b'.val.2).erase b'.val.1) (some b'.val.2) bs)
    (halen : as.length ≤ d) (hblen : bs.length ≤ d) :
    pairVisitProbability H N (d+1) k focus parent (a.val :: as) (b'.val :: bs) ≤
      C^2 * orderedWeight (fun t => (2/(N : ℝ))*b t) (as.length+1) k *
        orderedWeight (fun t => (2/(N : ℝ))*b t) (bs.length+1) k := by
  let A := fun t => orderedWeight (fun t => (2/(N : ℝ))*b t) as.length t
  let B := fun t => orderedWeight (fun t => (2/(N : ℝ))*b t) bs.length t
  have hA : ∀ t, 0 ≤ A t := fun t => orderedWeight_nonneg (fun t => mul_nonneg (by positivity) (hb t)) _ t
  have hB : ∀ t, 0 ≤ B t := fun t => orderedWeight_nonneg (fun t => mul_nonneg (by positivity) (hb t)) _ t
  have hstep := markedQuery_two_paths H N (pairRequired (a.val :: as) (b'.val :: bs)) d k hkd hkN []
    focus parent a b' hab (pair_required_candidates H _ _ a b' as bs) (fun _ => 1)
    (fun t ht => hq.1 t (by omega))
    (fun t _ => (gridAnswerProbability_mem_unit H N N t focus parent).2.trans (by norm_num))
  have hac := (Finset.mem_filter.mp a.property).2.1
  have hbc := (Finset.mem_filter.mp b'.property).2.1
  calc
    _ ≤ (1/(N : ℝ))*∑ u : Fin N, (1/(N : ℝ))*∑ v : Fin N,
        if u.val < k ∧ v.val < k then
          (markedGood (markedChildKernel H N (pairRequired (a.val :: as) (b'.val :: bs)) d []
            focus parent a u)*
          markedGood (markedChildKernel H N (pairRequired (a.val :: as) (b'.val :: bs)) d []
            focus parent b' v))*(2*1) else 0 := hstep
    _ ≤ (1/(N : ℝ))*∑ u : Fin N, (1/(N : ℝ))*∑ v : Fin N,
        C^2*((if u.val < k then A u.val*(2*b u.val) else 0)*
          (if v.val < k then B v.val*(2*b v.val) else 0)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro u _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro v _
      by_cases hu : u.val < k <;> by_cases hv : v.val < k
      · simp only [hu,hv,and_self,↓reduceIte]
        rw [marked_pair_child_left H N d _ _ a b' hab as bs u,
          marked_pair_child_right H N d _ _ a b' hab as bs v]
        have hau := pathVisitProbability_ordered H N b hb hq as d u.val (by omega) u.isLt.le
          halen a.val.1 a.val.2 hac ha
        have hbv := pathVisitProbability_ordered H N b hb hq bs d v.val (by omega) v.isLt.le
          hblen b'.val.1 b'.val.2 hbc hb'
        have hp := mul_le_mul hau hbv (markedGood_nonneg _) (hA _)
        dsimp only [pathVisitProbability] at hp
        have hm : 1 ≤ C^2*(b u.val*b v.val) := by
          have hh := mul_le_mul (hlower u.val u.isLt.le) (hlower v.val v.isLt.le)
            (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg hC (hb _))
          nlinarith
        have hw := mul_le_mul_of_nonneg_left hm (mul_nonneg (hA u.val) (hB v.val))
        have hab0 := mul_nonneg (hA u.val) (hB v.val)
        nlinarith
      · simp only [hu,hv,and_false,↓reduceIte,mul_zero,le_refl]
      · simp only [hu,hv,false_and,↓reduceIte,zero_mul,mul_zero,le_refl]
      · simp only [hu,hv,false_and,↓reduceIte,mul_zero,le_refl]
    _ = C^2*((1/(N : ℝ))*∑ u : Fin N, if u.val < k then A u.val*(2*b u.val) else 0)*
        ((1/(N : ℝ))*∑ v : Fin N, if v.val < k then B v.val*(2*b v.val) else 0) := by
      simp only [← Finset.mul_sum,← Finset.sum_mul]
      ring
    _ = _ := by
      rw [discrete_ordered_step N k hkN b as.length,discrete_ordered_step N k hkN b bs.length]

end RootForkVisitation
end SharpTerminalLeave

end

end OAI
