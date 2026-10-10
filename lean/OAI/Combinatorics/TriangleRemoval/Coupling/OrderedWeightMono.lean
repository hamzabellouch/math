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

lemma orderedWeight_mono {w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t) (j : ℕ) :
    Monotone (orderedWeight w j) := by
  cases j with
  | zero => intro a b _; rfl
  | succ j =>
    intro a b hab
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
      (fun t _ _ => mul_nonneg (hw t) (orderedWeight_nonneg hw _ _))

lemma pairRequired_common_shift {A : Type*} [DecidableEq A] (a : A)
    (p q address : List A) :
    pairRequired (a :: p) (a :: q) (address ++ [a]) = pairRequired p q address := by
  simp only [pairRequired,pathRequired_shift]

section SpineVisitation
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

lemma pair_common_required_candidates (H : τ → Finset ι) (focus : Finset ι)
    (parent : Option τ) (a : gridCandidates H focus parent) (p q : List (ι × τ)) :
    requiredCandidates H (pairRequired (a.val :: p) (a.val :: q)) [] focus parent = {a} := by
  rw [pair_required_candidates]
  exact Finset.pair_eq_singleton a

lemma marked_pair_common_child (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (d : ℕ) (focus : Finset ι) (parent : Option τ)
    (a : gridCandidates H focus parent) (p q : List (ι × τ)) (u : Fin N) :
    markedChildKernel H N (pairRequired (a.val :: p) (a.val :: q)) d [] focus parent a u =
      ExposureTree.fresh (fun _ : τ => PMF.uniformOfFintype (Fin N))
        (markedGridQueryDepth H N (pairRequired p q) d u.val []
          ((H a.val.2).erase a.val.1) (some a.val.2)) := by
  unfold markedChildKernel
  change ExposureTree.fresh _ (markedGridQueryDepth H N _ d u.val ([] ++ [a.val]) _ _) = _
  rw [markedGridQueryDepth_readdress]
  have he : (fun l => pairRequired (a.val :: p) (a.val :: q) (l ++ [a.val])) =
      pairRequired p q := by
    funext l
    exact pairRequired_common_shift _ _ _ _
  rw [he]

theorem pairVisitProbability_spine (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 0 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (spine : List (ι × τ)) (a b' : ι × τ) (hab : a ≠ b') (as bs : List (ι × τ))
    (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N)
    (e : ι) (T : τ) (he : e ∈ H T)
    (ha : LegalQueryPath H ((H T).erase e) (some T) (spine ++ a :: as))
    (hb' : LegalQueryPath H ((H T).erase e) (some T) (spine ++ b' :: bs))
    (halen : spine.length + (as.length+1) ≤ d) (hblen : spine.length + (bs.length+1) ≤ d) :
    pairVisitProbability H N d k ((H T).erase e) (some T)
      (spine ++ a :: as) (spine ++ b' :: bs) ≤
      C * orderedWeight (fun t => (2/(N : ℝ))*b t) spine.length k *
        orderedWeight (fun t => (2/(N : ℝ))*b t) (as.length+1) k *
        orderedWeight (fun t => (2/(N : ℝ))*b t) (bs.length+1) k := by
  have hw : ∀ t, 0 ≤ (2/(N : ℝ))*b t := fun t => mul_nonneg (by positivity) (hb t)
  induction spine generalizing d k e T with
  | nil =>
    cases d with
    | zero => simp only [List.length_nil] at halen; omega
    | succ d =>
      obtain ⟨ha,hat⟩ := ha
      obtain ⟨hb',hbt⟩ := hb'
      let aa : gridCandidates H ((H T).erase e) (some T) := ⟨a,ha⟩
      let bb : gridCandidates H ((H T).erase e) (some T) := ⟨b',hb'⟩
      have hne : aa ≠ bb := fun h => hab (congrArg Subtype.val h)
      simpa only [List.nil_append,List.length_nil,orderedWeight,mul_one] using
        pairVisitProbability_fork H N b hb hq C hC hlower d k hkd hkN e T he aa bb hne as bs
          hat hbt (by simp only [List.length_nil] at halen; omega)
          (by simp only [List.length_nil] at hblen; omega)
  | cons z zs ih =>
    cases d with
    | zero => simp only [List.length_cons] at halen; omega
    | succ d =>
      obtain ⟨hz,haz⟩ := ha
      obtain ⟨_,hbz⟩ := hb'
      let zz : gridCandidates H ((H T).erase e) (some T) := ⟨z,hz⟩
      have hzc := (Finset.mem_filter.mp hz).2.1
      have hs := markedQuery_single_path H N
        (pairRequired (z :: (zs ++ a :: as)) (z :: (zs ++ b' :: bs))) d k hkd hkN []
        ((H T).erase e) (some T) zz (pair_common_required_candidates H _ _ zz _ _) b
        (fun t ht => hq.1 t (by omega)) (fun t ht => hq.2 t (by omega) e T he)
      let A := orderedWeight (fun t => (2/(N : ℝ))*b t) (as.length+1) k
      let B := orderedWeight (fun t => (2/(N : ℝ))*b t) (bs.length+1) k
      have hA : 0 ≤ A := orderedWeight_nonneg hw _ _
      have hB : 0 ≤ B := orderedWeight_nonneg hw _ _
      calc
        _ ≤ (1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            markedGood (markedChildKernel H N
              (pairRequired (z :: (zs ++ a :: as)) (z :: (zs ++ b' :: bs))) d []
              ((H T).erase e) (some T) zz u)*(2*b u.val) else 0 := hs
        _ ≤ (1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            (C*orderedWeight (fun t => (2/(N : ℝ))*b t) zs.length u.val*A*B)*(2*b u.val)
            else 0 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro u _
          by_cases hu : u.val < k
          · simp only [hu,↓reduceIte]
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by norm_num) (hb _))
            rw [marked_pair_common_child H N d _ _ zz _ _ u]
            have hi := ih d u.val (by omega) u.isLt.le z.1 z.2 hzc haz hbz
              (by simp only [List.length_cons] at halen; omega)
              (by simp only [List.length_cons] at hblen; omega)
            apply hi.trans
            apply mul_le_mul
            · apply mul_le_mul_of_nonneg_left
              · exact orderedWeight_mono hw _ hu.le
              · exact mul_nonneg hC (orderedWeight_nonneg hw _ _)
            · exact orderedWeight_mono hw _ hu.le
            · exact orderedWeight_nonneg hw _ _
            · exact mul_nonneg (mul_nonneg hC (orderedWeight_nonneg hw _ _)) hA
          · simp only [hu,↓reduceIte,le_refl]
        _ = C*((1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            orderedWeight (fun t => (2/(N : ℝ))*b t) zs.length u.val*(2*b u.val) else 0)*A*B := by
          simp only [Finset.mul_sum,Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro u _
          by_cases hu : u.val < k <;> simp only [hu,↓reduceIte] <;> ring
        _ = _ := by
          rw [discrete_ordered_step N k hkN b zs.length]
          rfl

end SpineVisitation
end SharpTerminalLeave

end

end OAI
