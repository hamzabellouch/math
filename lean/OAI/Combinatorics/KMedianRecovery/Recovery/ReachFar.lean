import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.CloseSandwich
import OAI.Combinatorics.KMedianRecovery.Algorithms.BudgetBound
import OAI.Combinatorics.KMedianRecovery.Strictness.ClippedMap

namespace OAI

namespace MetricKMedianRecovery.PhaseLengthInterpolation
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion FreshCopyEndpoints
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

theorem reach_far (loc : D → X) (F B Q : Finset X) (root : X) (H : List X)
    (v lam M : ℝ) (q n c N : ℕ) (s : ℚ) (hF : F.Nonempty)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (hM : 0 < M)
    (hN : 3 ≤ N) (hlamUpper : lam ≤ 8*N*M) (hs : 20*N*M ≤ (s:ℝ))
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) (Q ∪ H.toFinset) i ≤ lam)
    (hc : Attains loc F B (Q ∪ H.toFinset) v lam q n c) :
    Reach loc F B Q root H v lam q n s c := by
  classical
  let : PseudoMetricSpace (X ⊕ ℝ) := familyMetric root
  have hm := hc.map incl (original_dist root)
  apply UniformRowDisabling.attains_insert hm (hF.image incl) M (Sum.inr (s:ℝ))
    hv hvsmall hlam hM.le (fresh F B _) _ _ _
  · intro x hx j
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    simpa only [original_dist root] using hdiam i hi j
  · intro j
    obtain ⟨h₁,h₂⟩ := DisablingCopy.numerical_bound v M N hv hvsmall hM hN
    have h₀ : (1+v^2)*(M+lam) ≤ (1+v^2)*(M+8*N*M) :=
      mul_le_mul_of_nonneg_left (by linarith only [hlamUpper]) (by positivity)
    have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
    have hs' : 20*N*M ≤ dist (incl (loc j)) (Sum.inr (s:ℝ)) := by
      rw [leaf_dist]
      exact hs.trans ((le_max_left _ _).trans (le_add_of_nonneg_left dist_nonneg))
    exact (h₀.trans_lt (h₁.trans h₂)).trans_le (mul_le_mul_of_nonneg_left hs' ht)
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    simpa only [HistoryIsometry.row_map incl (original_dist root)] using hrow i hi

theorem reach_zero_free (loc : D → X) (F B Q : Finset X) (i f : X) (H : List X)
    (v lam eta : ℝ) (q n c : ℕ) (hdis : Disjoint F B) (hf : f ∈ B)
    (hd : ∀ j, dist (loc j) i = dist (loc j) f) (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (hphase : Valid loc F B Q v ((1+v^2)^(q-1)) lam eta (H++[f]))
    (hc : Attains loc F B (Q ∪ (H++[f]).toFinset) v lam q n c) :
    Reach loc F B Q i H v lam q n 0 c := by
  classical
  let : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
  have hfF : f ∉ F := fun he => Finset.disjoint_left.mp hdis he hf
  have hfQ : f ∉ Q ∪ H.toFinset := by
    have he := PhaseMergeRefinement.entry_fresh (C := H) (T := []) hphase.1
    simpa only [List.append_nil] using he
  have hco : ∀ j, dist (incl (loc j)) (incl f) = dist (incl (loc j)) (Sum.inr (0:ℝ)) := by
    intro j
    simp only [original_dist i,leaf_dist,max_self,add_zero]
    exact (hd j).symm
  have hm := hc.map incl (original_dist i)
  have hs := hm.swap_free (incl f) (Sum.inr (0:ℝ))
    (by simpa only [incl.injective.mem_finset_image] using hfF) (fresh F B 0) hco ht hlam
  have hfix : ∀ x ∈ (Q ∪ H.toFinset).image (incl : X ↪ X ⊕ ℝ),
      Equiv.swap (incl f) (Sum.inr (0:ℝ)) x = x := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    apply Equiv.swap_apply_of_ne_of_ne
    · intro he
      exact hfQ ((incl.injective he) ▸ hy)
    · simp [incl]
  have him : ((Q ∪ H.toFinset).image (incl : X ↪ X ⊕ ℝ)).image
      (Equiv.swap (incl f) (Sum.inr (0:ℝ))) = (Q ∪ H.toFinset).image incl := by
    calc
      _ = ((Q ∪ H.toFinset).image (incl : X ↪ X ⊕ ℝ)).image id := Finset.image_congr hfix
      _ = _ := Finset.image_id
  have hb : Q ∪ (H++[f]).toFinset = insert f (Q ∪ H.toFinset) := by
    simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
      Finset.union_insert,Finset.union_empty]
  simpa only [Reach,Rat.cast_zero,hb,Finset.image_insert,Equiv.swap_apply_left,him] using hs

theorem reach_zero_paid (loc : D → X) (F B Q : Finset X) (i : X) (C T : List X)
    (v lam eta : ℝ) (q n c : ℕ) (hi : i ∈ F) (hdis : Disjoint F B)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (hphase : Valid loc F B Q v ((1+v^2)^(q-1)) lam eta (C++i::T))
    (hc : Attains loc F B (Q ∪ (C++i::T).toFinset) v lam q n c) :
    ∃ c', Reach loc F B Q i (C++T) v lam q n 0 c' ∧ c = c'+1 := by
  classical
  let : PseudoMetricSpace (X ⊕ ℝ) := familyMetric i
  have hiQ := PhaseMergeRefinement.entry_fresh hphase.1
  have hco : ∀ j, dist (incl (loc j)) (incl i) = dist (incl (loc j)) (Sum.inr (0:ℝ)) := by
    intro j
    simp only [original_dist i,leaf_dist,max_self,add_zero]
  have hm := (hc.map incl (original_dist i)).mono_free
    (Finset.subset_insert (Sum.inr (0:ℝ)) (B.image incl))
  have hd' : Disjoint (F.image (incl : X ↪ X ⊕ ℝ)) (insert (Sum.inr (0:ℝ)) (B.image incl)) := by
    rw [Finset.disjoint_insert_right]
    refine ⟨by simp [incl],?_⟩
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hy
    exact Finset.disjoint_left.mp hdis ha (incl.injective he ▸ hb)
  have hb : (Q ∪ (C++i::T).toFinset).image (incl : X ↪ X ⊕ ℝ) =
      insert (incl i) ((Q ∪ (C++T).toFinset).image incl) := by
    simp only [List.toFinset_append,List.toFinset_cons,Finset.union_insert,Finset.image_insert]
  obtain ⟨c',hc',hcorr⟩ := attains_twin (incl i) (Sum.inr (0:ℝ))
    ((Q ∪ (C++T).toFinset).image incl) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    (Finset.mem_insert_self _ _) hd'
    (by simpa only [incl.injective.mem_finset_image] using hiQ)
    (by simp [incl]) hb rfl hco ht hlam hm
  exact ⟨c',by simpa only [Reach,Rat.cast_zero] using hc',hcorr⟩

end MetricKMedianRecovery.PhaseLengthInterpolation

end OAI
