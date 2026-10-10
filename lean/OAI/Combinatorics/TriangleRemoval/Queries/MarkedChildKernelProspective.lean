import Mathlib
import OAI.Combinatorics.TriangleRemoval.Coupling.GridUniformError
import OAI.Combinatorics.TriangleRemoval.Probability.MarkedSuccessTrueProbability
import OAI.Combinatorics.TriangleRemoval.Coupling.SelectedClockLawPair

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
section ActualMarkedRows
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

omit [Fintype ι] in

lemma markedChildKernel_prospective (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (required : List (ι × τ) → Bool) (d t : ℕ) (htd : t ≤ d+1) (htN : t ≤ N)
    (address : List (ι × τ)) (focus : Finset ι) (parent : Option τ)
    (a : gridCandidates H focus parent) :
    prospectiveFailure N t (fun u => markedSuccess
      (markedChildKernel H N required d address focus parent a u)) =
        gridCandidateFailure H N t a.val.1 a.val.2 := by
  have hsum : (∑ u : Fin N, if u.val < t then markedSuccess
      (markedChildKernel H N required d address focus parent a u) else 0) =
      ∑ j ∈ Finset.range t, ∏ f ∈ (H a.val.2).erase a.val.1,
        gridMessage H N N j f (some a.val.2) := by
    calc
      _ = ∑ u : Fin N, if u.val < t then
          ∏ f ∈ (H a.val.2).erase a.val.1, gridMessage H N N u.val f (some a.val.2)
          else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases hu : u.val < t
        · simp only [hu,↓reduceIte]
          exact markedChildKernel_success_complete H N required d address focus parent a u (by omega)
        · simp only [hu,↓reduceIte]
      _ = _ := by
        simpa only [Finset.sum_filter] using sum_fin_filter_lt_eq_range N t htN
          (fun j => ∏ f ∈ (H a.val.2).erase a.val.1, gridMessage H N N j f (some a.val.2))
  unfold prospectiveFailure gridCandidateFailure
  rw [hsum]
  ring

omit [Fintype ι] in

theorem markedQuery_single_path (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (required : List (ι × τ) → Bool) (d k : ℕ) (hkd : k ≤ d+1) (hkN : k ≤ N)
    (address : List (ι × τ)) (focus : Finset ι) (parent : Option τ)
    (a : gridCandidates H focus parent)
    (hreq : requiredCandidates H required address focus parent = {a}) (b : ℕ → ℝ)
    (hfactor : ∀ t < k, ∀ (e : ι) (T : τ), e ∈ H T →
      (7/8 : ℝ) ≤ gridCandidateFailure H N t e T)
    (hfull : ∀ t < k, gridAnswerProbability H N N t focus parent ≤ (9/8 : ℝ)*b t) :
    markedGood (ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
      (markedGridQueryDepth H N required (d+1) k address focus parent)) ≤
      (1/(N : ℝ))*∑ u : Fin N, if u.val < k then
        markedGood (markedChildKernel H N required d address focus parent a u)*(2*b u.val)
        else 0 := by
  rw [markedGridQueryDepth_candidate_kernel,hreq]
  apply marked_row_single_path N _ (finsetCandidateOrder_perm _) a _
    (fun a u => markedSuccess (markedChildKernel H N required d address focus parent a u))
    k b (by intros; rfl)
  · intro t ht a
    rw [markedChildKernel_prospective H N required d t (by omega) (by omega)]
    exact hfactor t ht a.val.1 a.val.2 (by
      have ha := a.property
      simp only [gridCandidates,Finset.mem_filter] at ha
      exact ha.2.1)
  · intro t ht
    simp_rw [markedChildKernel_prospective H N required d t (by omega) (by omega)]
    rw [gridCandidateFailure_product H N t (by omega)]
    exact hfull t ht

omit [Fintype ι] in

theorem markedQuery_two_paths (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (required : List (ι × τ) → Bool) (d k : ℕ) (hkd : k ≤ d+1) (hkN : k ≤ N)
    (address : List (ι × τ)) (focus : Finset ι) (parent : Option τ)
    (a b : gridCandidates H focus parent) (hab : a ≠ b)
    (hreq : requiredCandidates H required address focus parent = {a,b}) (w : ℕ → ℝ)
    (hfactor : ∀ t < k, ∀ (e : ι) (T : τ), e ∈ H T →
      (7/8 : ℝ) ≤ gridCandidateFailure H N t e T)
    (hfull : ∀ t < k, gridAnswerProbability H N N t focus parent ≤ (9/8 : ℝ)*w t) :
    markedGood (ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
      (markedGridQueryDepth H N required (d+1) k address focus parent)) ≤
      (1/(N : ℝ))*∑ u : Fin N, (1/(N : ℝ))*∑ v : Fin N,
        if u.val < k ∧ v.val < k then
          (markedGood (markedChildKernel H N required d address focus parent a u)*
            markedGood (markedChildKernel H N required d address focus parent b v))*
              (2*w (max u.val v.val)) else 0 := by
  rw [markedGridQueryDepth_candidate_kernel,hreq]
  apply marked_row_two_paths N _ (finsetCandidateOrder_perm _) a b hab _
    (fun a u => markedSuccess (markedChildKernel H N required d address focus parent a u))
    k w (by intros; rfl)
  · intro t ht a
    rw [markedChildKernel_prospective H N required d t (by omega) (by omega)]
    exact hfactor t ht a.val.1 a.val.2 (by
      have ha := a.property
      simp only [gridCandidates,Finset.mem_filter] at ha
      exact ha.2.1)
  · intro t ht
    simp_rw [markedChildKernel_prospective H N required d t (by omega) (by omega)]
    rw [gridCandidateFailure_product H N t (by omega)]
    exact hfull t ht

end ActualMarkedRows
end SharpTerminalLeave

open scoped BigOperators

end

end OAI
