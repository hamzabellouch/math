import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.MarkedChildKernelProspective
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixWeight

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

def pathRequired {A : Type*} [DecidableEq A] (path address : List A) : Bool :=
  decide (address.reverse <+: path)

lemma pathRequired_singleton {A : Type*} [DecidableEq A] (a b : A) (as : List A) :
    pathRequired (a :: as) [b] = decide (b = a) := by
  simp [pathRequired,List.cons_prefix_cons]

lemma pathRequired_shift {A : Type*} [DecidableEq A] (a : A) (as address : List A) :
    pathRequired (a :: as) (address ++ [a]) = pathRequired as address := by
  simp [pathRequired,List.reverse_append]

section PathVisitation
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

def LegalQueryPath (H : τ → Finset ι) : Finset ι → Option τ → List (ι × τ) → Prop
  | _, _, [] => True
  | focus, parent, a :: as => a ∈ gridCandidates H focus parent ∧
      LegalQueryPath H ((H a.2).erase a.1) (some a.2) as

omit [Fintype ι] in
lemma path_required_candidates (H : τ → Finset ι) (focus : Finset ι) (parent : Option τ)
    (a : gridCandidates H focus parent) (as : List (ι × τ)) :
    requiredCandidates H (pathRequired (a.val :: as)) [] focus parent = {a} := by
  ext b
  simp only [requiredCandidates,Finset.mem_filter,Finset.mem_univ,true_and,
    pathRequired_singleton,decide_eq_true_eq,Finset.mem_singleton]
  exact Subtype.val_injective.eq_iff

omit [Fintype ι] in

lemma markedGridQueryDepth_readdress (H : τ → Finset ι) (N : ℕ)
    (required : List (ι × τ) → Bool) (d k : ℕ)
    (address base : List (ι × τ)) (focus : Finset ι) (parent : Option τ) :
    markedGridQueryDepth H N required d k (address ++ base) focus parent =
      markedGridQueryDepth H N (fun l => required (l ++ base)) d k address focus parent := by
  induction d generalizing k address focus parent with
  | zero => rfl
  | succ d ih =>
    simp only [markedGridQueryDepth]
    congr 1
    funext values
    congr 1
    apply List.map_congr_left
    intro p _
    congr 1
    split
    · simpa only [List.cons_append] using
        ih p.2.val (p.1 :: address) ((H p.1.2).erase p.1.1) (some p.1.2)
    · rfl

omit [Fintype ι] in
lemma marked_path_child (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d : ℕ) (focus : Finset ι) (parent : Option τ)
    (a : gridCandidates H focus parent) (as : List (ι × τ)) (u : Fin N) :
    markedChildKernel H N (pathRequired (a.val :: as)) d [] focus parent a u =
      ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
        (markedGridQueryDepth H N (pathRequired as) d u.val []
          ((H a.val.2).erase a.val.1) (some a.val.2)) := by
  unfold markedChildKernel
  change ExposureTree.fresh _ (markedGridQueryDepth H N _ d u.val ([] ++ [a.val]) _ _) = _
  rw [markedGridQueryDepth_readdress]
  have he : (fun l => pathRequired (a.val :: as) (l ++ [a.val])) = pathRequired as := by
    funext l
    exact pathRequired_shift _ _ _
  rw [he]

noncomputable def pathVisitProbability (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (path : List (ι × τ)) : ℝ :=
  markedGood (ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
    (markedGridQueryDepth H N (pathRequired path) d k [] focus parent))

def GridRowQuality (H : τ → Finset ι) (N : ℕ) [NeZero N] (b : ℕ → ℝ) : Prop :=
  (∀ t ≤ N, ∀ (e : ι) (T : τ), e ∈ H T →
    (7/8 : ℝ) ≤ gridCandidateFailure H N t e T) ∧
  (∀ t ≤ N, ∀ (e : ι) (T : τ), e ∈ H T →
    gridAnswerProbability H N N t ((H T).erase e) (some T) ≤ (9/8 : ℝ)*b t)

omit [Fintype ι] in

theorem pathVisitProbability_ordered (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (path : List (ι × τ)) (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N)
    (hlen : path.length ≤ d) (e : ι) (T : τ) (he : e ∈ H T)
    (hpath : LegalQueryPath H ((H T).erase e) (some T) path) :
    pathVisitProbability H N d k ((H T).erase e) (some T) path ≤
      orderedWeight (fun t => (2/(N : ℝ))*b t) path.length k := by
  induction path generalizing d k e T with
  | nil =>
    simpa only [List.length_nil,orderedWeight,pathVisitProbability] using markedGood_le_one _
  | cons a as ih =>
    cases d with
    | zero => simp only [List.length_cons] at hlen; omega
    | succ d =>
      obtain ⟨ha,htail⟩ := hpath
      let a' : gridCandidates H ((H T).erase e) (some T) := ⟨a,ha⟩
      have haT : a.1 ∈ H a.2 := (Finset.mem_filter.mp ha).2.1
      have hstep := markedQuery_single_path H N (pathRequired (a :: as)) d k hkd hkN []
        ((H T).erase e) (some T) a' (path_required_candidates H _ _ a' as) b
        (fun t ht => hq.1 t (by omega))
        (fun t ht => hq.2 t (by omega) e T he)
      change pathVisitProbability H N (d+1) k ((H T).erase e) (some T) (a :: as) ≤ _ at hstep
      calc
        _ ≤ (1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            markedGood (markedChildKernel H N (pathRequired (a :: as)) d []
              ((H T).erase e) (some T) a' u)*(2*b u.val) else 0 := hstep
        _ ≤ (1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            orderedWeight (fun t => (2/(N : ℝ))*b t) as.length u.val*(2*b u.val) else 0 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro u _
          by_cases hu : u.val < k
          · simp only [hu,↓reduceIte]
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by norm_num) (hb _))
            rw [marked_path_child H N d ((H T).erase e) (some T) a' as u]
            apply ih d u.val (by omega) u.isLt.le (by simpa only [List.length_cons] using Nat.le_of_succ_le_succ hlen)
              a.1 a.2 haT htail
          · simp only [hu,↓reduceIte,le_refl]
        _ = _ := by
          rw [Finset.mul_sum]
          simp only [List.length_cons,orderedWeight]
          have hsum := sum_fin_filter_lt_eq_range N k hkN
            (fun j => (2/(N : ℝ))*b j*orderedWeight (fun t => (2/(N : ℝ))*b t) as.length j)
          rw [Finset.sum_filter] at hsum
          rw [← hsum]
          apply Finset.sum_congr rfl
          intro u _
          by_cases hu : u.val < k <;> simp only [hu,↓reduceIte] <;> ring

omit [Fintype ι] in

theorem pathVisitProbability_factorial (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (path : List (ι × τ)) (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N)
    (hlen : path.length ≤ d) (e : ι) (T : τ) (he : e ∈ H T)
    (hpath : LegalQueryPath H ((H T).erase e) (some T) path) :
    pathVisitProbability H N d k ((H T).erase e) (some T) path ≤
      prefixWeight (fun t => (2/(N : ℝ))*b t) k ^ path.length /
        (path.length.factorial : ℝ) :=
  (pathVisitProbability_ordered H N b hb hq path d k hkd hkN hlen e T he hpath).trans
    (orderedWeight_le (fun t => mul_nonneg (by positivity) (hb t)) _ _)

end PathVisitation
end SharpTerminalLeave

end

end OAI
