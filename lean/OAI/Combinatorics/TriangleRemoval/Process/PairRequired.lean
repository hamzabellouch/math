import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.PathRequired

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

def pairRequired {A : Type*} [DecidableEq A] (p q address : List A) : Bool :=
  pathRequired p address || pathRequired q address

lemma pairRequired_shift_left {A : Type*} [DecidableEq A] (a b : A)
    (as bs address : List A) (hab : a ≠ b) :
    pairRequired (a :: as) (b :: bs) (address ++ [a]) = pathRequired as address := by
  simp [pairRequired,pathRequired,List.reverse_append,List.cons_prefix_cons,hab]

lemma pairRequired_shift_right {A : Type*} [DecidableEq A] (a b : A)
    (as bs address : List A) (hab : a ≠ b) :
    pairRequired (a :: as) (b :: bs) (address ++ [b]) = pathRequired bs address := by
  simp [pairRequired,pathRequired,List.reverse_append,List.cons_prefix_cons,hab.symm]

section ForkVisitation
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

omit [Fintype ι] in
lemma pair_required_candidates (H : τ → Finset ι) (focus : Finset ι) (parent : Option τ)
    (a b : gridCandidates H focus parent) (as bs : List (ι × τ)) :
    requiredCandidates H (pairRequired (a.val :: as) (b.val :: bs)) [] focus parent =
      {a,b} := by
  ext c
  simp only [requiredCandidates,Finset.mem_filter,Finset.mem_univ,true_and,pairRequired,
    pathRequired_singleton,Bool.or_eq_true,decide_eq_true_eq,Finset.mem_insert,
    Finset.mem_singleton,Subtype.val_injective.eq_iff]

omit [Fintype ι] in
lemma marked_pair_child_left (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d : ℕ) (focus : Finset ι) (parent : Option τ)
    (a b : gridCandidates H focus parent) (hab : a ≠ b)
    (as bs : List (ι × τ)) (u : Fin N) :
    markedChildKernel H N (pairRequired (a.val :: as) (b.val :: bs)) d [] focus parent a u =
      ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
        (markedGridQueryDepth H N (pathRequired as) d u.val []
          ((H a.val.2).erase a.val.1) (some a.val.2)) := by
  unfold markedChildKernel
  change ExposureTree.fresh _ (markedGridQueryDepth H N _ d u.val ([] ++ [a.val]) _ _) = _
  rw [markedGridQueryDepth_readdress]
  have he : (fun l => pairRequired (a.val :: as) (b.val :: bs) (l ++ [a.val])) =
      pathRequired as := by
    funext l
    exact pairRequired_shift_left _ _ _ _ _ (fun h => hab (Subtype.ext h))
  rw [he]

omit [Fintype ι] in
lemma marked_pair_child_right (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d : ℕ) (focus : Finset ι) (parent : Option τ)
    (a b : gridCandidates H focus parent) (hab : a ≠ b)
    (as bs : List (ι × τ)) (u : Fin N) :
    markedChildKernel H N (pairRequired (a.val :: as) (b.val :: bs)) d [] focus parent b u =
      ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
        (markedGridQueryDepth H N (pathRequired bs) d u.val []
          ((H b.val.2).erase b.val.1) (some b.val.2)) := by
  unfold markedChildKernel
  change ExposureTree.fresh _ (markedGridQueryDepth H N _ d u.val ([] ++ [b.val]) _ _) = _
  rw [markedGridQueryDepth_readdress]
  have he : (fun l => pairRequired (a.val :: as) (b.val :: bs) (l ++ [b.val])) =
      pathRequired bs := by
    funext l
    exact pairRequired_shift_right _ _ _ _ _ (fun h => hab (Subtype.ext h))
  rw [he]

noncomputable def pairVisitProbability (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d k : ℕ) (focus : Finset ι) (parent : Option τ) (p q : List (ι × τ)) : ℝ :=
  markedGood (ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
    (markedGridQueryDepth H N (pairRequired p q) d k [] focus parent))

lemma discrete_ordered_step (N k : ℕ) (hk : k ≤ N) (b : ℕ → ℝ) (j : ℕ) :
    (1/(N : ℝ))*(∑ u : Fin N, if u.val < k then
      orderedWeight (fun t => (2/(N : ℝ))*b t) j u.val*(2*b u.val) else 0) =
      orderedWeight (fun t => (2/(N : ℝ))*b t) (j+1) k := by
  rw [Finset.mul_sum,orderedWeight]
  have hs := sum_fin_filter_lt_eq_range N k hk
    (fun t => (2/(N : ℝ))*b t*orderedWeight (fun t => (2/(N : ℝ))*b t) j t)
  rw [Finset.sum_filter] at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u.val < k <;> simp only [hu,↓reduceIte] <;> ring

omit [Fintype ι] in

theorem pairVisitProbability_fork (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 0 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (d k : ℕ) (hkd : k ≤ d+1) (hkN : k ≤ N)
    (e : ι) (T : τ) (he : e ∈ H T)
    (a b' : gridCandidates H ((H T).erase e) (some T)) (hab : a ≠ b')
    (as bs : List (ι × τ)) (ha : LegalQueryPath H ((H a.val.2).erase a.val.1) (some a.val.2) as)
    (hb' : LegalQueryPath H ((H b'.val.2).erase b'.val.1) (some b'.val.2) bs)
    (halen : as.length ≤ d) (hblen : bs.length ≤ d) :
    pairVisitProbability H N (d+1) k ((H T).erase e) (some T) (a.val :: as) (b'.val :: bs) ≤
      C * orderedWeight (fun t => (2/(N : ℝ))*b t) (as.length+1) k *
        orderedWeight (fun t => (2/(N : ℝ))*b t) (bs.length+1) k := by
  let A := fun t => orderedWeight (fun t => (2/(N : ℝ))*b t) as.length t
  let B := fun t => orderedWeight (fun t => (2/(N : ℝ))*b t) bs.length t
  have hA : ∀ t, 0 ≤ A t := fun t => orderedWeight_nonneg (fun t => mul_nonneg (by positivity) (hb t)) _ t
  have hB : ∀ t, 0 ≤ B t := fun t => orderedWeight_nonneg (fun t => mul_nonneg (by positivity) (hb t)) _ t
  have hstep := markedQuery_two_paths H N (pairRequired (a.val :: as) (b'.val :: bs)) d k hkd hkN []
    ((H T).erase e) (some T) a b' hab (pair_required_candidates H _ _ a b' as bs) b
    (fun t ht => hq.1 t (by omega)) (fun t ht => hq.2 t (by omega) e T he)
  have hac := (Finset.mem_filter.mp a.property).2.1
  have hbc := (Finset.mem_filter.mp b'.property).2.1
  calc
    _ ≤ (1/(N : ℝ))*∑ u : Fin N, (1/(N : ℝ))*∑ v : Fin N,
        if u.val < k ∧ v.val < k then
          (markedGood (markedChildKernel H N (pairRequired (a.val :: as) (b'.val :: bs)) d []
            ((H T).erase e) (some T) a u)*
          markedGood (markedChildKernel H N (pairRequired (a.val :: as) (b'.val :: bs)) d []
            ((H T).erase e) (some T) b' v))*(2*b (max u.val v.val)) else 0 := hstep
    _ ≤ (1/(N : ℝ))*∑ u : Fin N, (1/(N : ℝ))*∑ v : Fin N,
        C*((if u.val < k then A u.val*(2*b u.val) else 0)*
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
        have hm : b (max u.val v.val) ≤ C*(b u.val*b v.val) := by
          rcases le_total u.val v.val with h | h
          · rw [max_eq_right h]
            simpa only [one_mul,mul_assoc] using
              mul_le_mul_of_nonneg_right (hlower u.val u.isLt.le) (hb v.val)
          · rw [max_eq_left h]
            have hh := mul_le_mul_of_nonneg_right (hlower v.val v.isLt.le) (hb u.val)
            nlinarith
        have hp := mul_le_mul hau hbv (markedGood_nonneg _) (hA _)
        have hprod := mul_le_mul_of_nonneg_right hp
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hb (max u.val v.val)))
        have hwm := mul_le_mul_of_nonneg_left hm (mul_nonneg (hA u.val) (hB v.val))
        dsimp only [pathVisitProbability] at hprod
        calc
          _ ≤ A u.val*B v.val*(2*b (max u.val v.val)) := hprod
          _ ≤ _ := by
            have hn := mul_nonneg (mul_nonneg (hA u.val) (hB v.val))
              (mul_nonneg hC (mul_nonneg (hb u.val) (hb v.val)))
            nlinarith
      · simp only [hu,hv,and_false,↓reduceIte,mul_zero,le_refl]
      · simp only [hu,hv,false_and,↓reduceIte,zero_mul,mul_zero,le_refl]
      · simp only [hu,hv,false_and,↓reduceIte,mul_zero,le_refl]
    _ = C*((1/(N : ℝ))*∑ u : Fin N, if u.val < k then A u.val*(2*b u.val) else 0)*
        ((1/(N : ℝ))*∑ v : Fin N, if v.val < k then B v.val*(2*b v.val) else 0) := by
      simp only [← Finset.mul_sum,← Finset.sum_mul]
      ring
    _ = _ := by
      rw [discrete_ordered_step N k hkN b as.length,discrete_ordered_step N k hkN b bs.length]

end ForkVisitation
end SharpTerminalLeave

end

end OAI
