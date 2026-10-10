import Mathlib
import OAI.Combinatorics.TriangleRemoval.Probability.PathVisitProbability
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
section RootPathVisitation
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem rootPathVisitProbability_ordered (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 1 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (path : List (ι × τ)) (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N)
    (hlen : path.length ≤ d) (focus : Finset ι) (parent : Option τ)
    (hpath : LegalQueryPath H focus parent path) :
    pathVisitProbability H N d k focus parent path ≤
      C*orderedWeight (fun t => (2/(N : ℝ))*b t) path.length k := by
  cases path with
  | nil =>
    simpa only [List.length_nil,orderedWeight,mul_one,pathVisitProbability] using
      (markedGood_le_one (ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
        (markedGridQueryDepth H N (pathRequired []) d k [] focus parent))).trans hC
  | cons a as =>
    cases d with
    | zero => simp only [List.length_cons] at hlen; omega
    | succ d =>
      obtain ⟨ha,htail⟩ := hpath
      let aa : gridCandidates H focus parent := ⟨a,ha⟩
      have haT : a.1 ∈ H a.2 := (Finset.mem_filter.mp ha).2.1
      have hstep := markedQuery_single_path H N (pathRequired (a :: as)) d k hkd hkN []
        focus parent aa (path_required_candidates H _ _ aa as) (fun _ => 1)
        (fun t ht => hq.1 t (by omega))
        (fun t _ => (gridAnswerProbability_mem_unit H N N t focus parent).2.trans (by norm_num))
      change pathVisitProbability H N (d+1) k focus parent (a :: as) ≤ _ at hstep
      calc
        _ ≤ (1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            markedGood (markedChildKernel H N (pathRequired (a :: as)) d []
              focus parent aa u)*(2*1) else 0 := hstep
        _ ≤ C*((1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            orderedWeight (fun t => (2/(N : ℝ))*b t) as.length u.val*(2*b u.val)
            else 0) := by
          rw [mul_left_comm C (1/(N : ℝ))]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro u _
          by_cases hu : u.val < k
          · simp only [hu,↓reduceIte]
            rw [marked_path_child H N d focus parent aa as u]
            have hi := pathVisitProbability_ordered H N b hb hq as d u.val (by omega)
              u.isLt.le (by simp only [List.length_cons] at hlen; omega) a.1 a.2 haT htail
            have ho := orderedWeight_nonneg (fun t => mul_nonneg (by positivity : (0 : ℝ) ≤ 2/(N : ℝ)) (hb t)) as.length u.val
            have hl := hlower u.val u.isLt.le
            change pathVisitProbability H N d u.val ((H a.2).erase a.1) (some a.2) as * (2*1) ≤ _
            nlinarith [mul_nonneg ho (sub_nonneg.mpr hl)]
          · simp only [hu,↓reduceIte,mul_zero,le_refl]
        _ = _ := by
          rw [discrete_ordered_step N k hkN b as.length]
          rfl

theorem actualRootPathVisitProbability_factorial (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 1 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (path : List (ι × τ)) (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N)
    (hlen : path.length ≤ d) (focus : Finset ι) (parent : Option τ)
    (hpath : LegalQueryPath H focus parent path) :
    actualPathVisitProbability H N d k focus parent path ≤
      C*(prefixWeight (fun t => (2/(N : ℝ))*b t) k ^ path.length /
        (path.length.factorial : ℝ)) := by
  apply (actualPathVisitProbability_le_marked H N d k focus parent path).trans
  apply (rootPathVisitProbability_ordered H N b hb hq C hC hlower path d k hkd hkN hlen
    focus parent hpath).trans
  exact mul_le_mul_of_nonneg_left
    (orderedWeight_le (fun t => mul_nonneg (by positivity) (hb t)) _ _) (by linarith)

end RootPathVisitation
end SharpTerminalLeave

end

end OAI
