import Mathlib
import OAI.Combinatorics.TriangleRemoval.Coupling.OrderedWeightMono
import OAI.Combinatorics.TriangleRemoval.Probability.RootPairVisitProbability

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
section RootSpineVisitation
variable {ι τ : Type*} [Fintype τ] [DecidableEq ι] [DecidableEq τ]

theorem rootPairVisitProbability_spine (H : τ → Finset ι) (N : ℕ) [NeZero N]
    (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t) (hq : GridRowQuality H N b)
    (C : ℝ) (hC : 0 ≤ C) (hlower : ∀ t ≤ N, 1 ≤ C*b t)
    (spine : List (ι × τ)) (a b' : ι × τ) (hab : a ≠ b') (as bs : List (ι × τ))
    (d k : ℕ) (hkd : k ≤ d) (hkN : k ≤ N)
    (focus : Finset ι) (parent : Option τ)
    (ha : LegalQueryPath H focus parent (spine ++ a :: as))
    (hb' : LegalQueryPath H focus parent (spine ++ b' :: bs))
    (halen : spine.length + (as.length+1) ≤ d) (hblen : spine.length + (bs.length+1) ≤ d) :
    pairVisitProbability H N d k focus parent
      (spine ++ a :: as) (spine ++ b' :: bs) ≤
      C^2 * orderedWeight (fun t => (2/(N : ℝ))*b t) spine.length k *
        orderedWeight (fun t => (2/(N : ℝ))*b t) (as.length+1) k *
        orderedWeight (fun t => (2/(N : ℝ))*b t) (bs.length+1) k := by
  have hw : ∀ t, 0 ≤ (2/(N : ℝ))*b t := fun t => mul_nonneg (by positivity) (hb t)
  cases spine with
  | nil =>
    cases d with
    | zero => simp only [List.length_nil] at halen; omega
    | succ d =>
      obtain ⟨ha,hat⟩ := ha
      obtain ⟨hb',hbt⟩ := hb'
      let aa : gridCandidates H focus parent := ⟨a,ha⟩
      let bb : gridCandidates H focus parent := ⟨b',hb'⟩
      have hne : aa ≠ bb := fun h => hab (congrArg Subtype.val h)
      simpa only [List.nil_append,List.length_nil,orderedWeight,mul_one] using
        rootPairVisitProbability_fork H N b hb hq C hC hlower d k hkd hkN focus parent aa bb hne as bs
          hat hbt (by simp only [List.length_nil] at halen; omega)
          (by simp only [List.length_nil] at hblen; omega)
  | cons z zs =>
    cases d with
    | zero => simp only [List.length_cons] at halen; omega
    | succ d =>
      obtain ⟨hz,haz⟩ := ha
      obtain ⟨_,hbz⟩ := hb'
      let zz : gridCandidates H focus parent := ⟨z,hz⟩
      have hzc := (Finset.mem_filter.mp hz).2.1
      have hs := markedQuery_single_path H N
        (pairRequired (z :: (zs ++ a :: as)) (z :: (zs ++ b' :: bs))) d k hkd hkN []
        focus parent zz (pair_common_required_candidates H _ _ zz _ _) (fun _ => 1)
        (fun t ht => hq.1 t (by omega))
        (fun t _ => (gridAnswerProbability_mem_unit H N N t focus parent).2.trans (by norm_num))
      let A := orderedWeight (fun t => (2/(N : ℝ))*b t) (as.length+1) k
      let B := orderedWeight (fun t => (2/(N : ℝ))*b t) (bs.length+1) k
      have hA : 0 ≤ A := orderedWeight_nonneg hw _ _
      have hB : 0 ≤ B := orderedWeight_nonneg hw _ _
      calc
        _ ≤ (1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            markedGood (markedChildKernel H N
              (pairRequired (z :: (zs ++ a :: as)) (z :: (zs ++ b' :: bs))) d []
              focus parent zz u)*(2*1) else 0 := hs
        _ ≤ (1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            (C^2*orderedWeight (fun t => (2/(N : ℝ))*b t) zs.length u.val*A*B)*(2*b u.val)
            else 0 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro u _
          by_cases hu : u.val < k
          · simp only [hu,↓reduceIte]
            rw [marked_pair_common_child H N d _ _ zz _ _ u]
            have hi := pairVisitProbability_spine H N b hb hq C hC hlower zs a b' hab as bs
              d u.val (by omega) u.isLt.le z.1 z.2 hzc haz hbz
              (by simp only [List.length_cons] at halen; omega)
              (by simp only [List.length_cons] at hblen; omega)
            have hj : pairVisitProbability H N d u.val ((H z.2).erase z.1) (some z.2)
                (zs ++ a :: as) (zs ++ b' :: bs) ≤
                C*orderedWeight (fun t => (2/(N : ℝ))*b t) zs.length u.val*A*B := by
              apply hi.trans
              apply mul_le_mul
              · apply mul_le_mul_of_nonneg_left
                · exact orderedWeight_mono hw _ hu.le
                · exact mul_nonneg hC (orderedWeight_nonneg hw _ _)
              · exact orderedWeight_mono hw _ hu.le
              · exact orderedWeight_nonneg hw _ _
              · exact mul_nonneg (mul_nonneg hC (orderedWeight_nonneg hw _ _)) hA
            have hz0 := orderedWeight_nonneg hw zs.length u.val
            have hcharge := mul_le_mul_of_nonneg_left (hlower u.val u.isLt.le)
              (mul_nonneg (mul_nonneg (mul_nonneg hC hz0) hA) hB)
            dsimp only [pairVisitProbability] at hj
            nlinarith
          · simp only [hu,↓reduceIte,le_refl]
        _ = C^2*((1/(N : ℝ))*∑ u : Fin N, if u.val < k then
            orderedWeight (fun t => (2/(N : ℝ))*b t) zs.length u.val*(2*b u.val) else 0)*A*B := by
          simp only [Finset.mul_sum,Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro u _
          by_cases hu : u.val < k <;> simp only [hu,↓reduceIte] <;> ring
        _ = _ := by
          rw [discrete_ordered_step N k hkN b zs.length]
          rfl

end RootSpineVisitation
end SharpTerminalLeave

end

end OAI
