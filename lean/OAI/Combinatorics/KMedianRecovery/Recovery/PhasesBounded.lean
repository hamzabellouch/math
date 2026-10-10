import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ActiveInsert
import OAI.Combinatorics.KMedianRecovery.Recovery.Live

namespace OAI

namespace MetricKMedianRecovery.UniformDisablingEndpoint
open PhaseHistoryTransfer HistoryPhaseBound
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

theorem phases_bounded (loc : D → X) (F B Q : Finset X) (hF : F.Nonempty)
    (v lam M eta : ℝ) (q : ℕ) (T : List (List X))
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hM : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (hh : History loc F B v lam eta q Q T) (hlive : Live loc v q Q T) :
    ∀ r, r < T.length → (1+v^2)^(q+r) ≤ M+lam := by
  induction hh with
  | nil => simp
  | @cons q Q H T hhead htail ih =>
    intro r hr
    cases r with
    | zero =>
      simpa only [Nat.add_zero] using
        active_bound loc F Q hF v lam M ((1+v^2)^q)
          (by linarith only [hvsmall]) hrow hM hlive.1
    | succ r =>
      have hrow' := advance_rows loc F B Q v lam eta q H hv hvsmall hlam hrow hhead
      have hr' : r < T.length := by simpa using hr
      have hh := ih hrow' hlive.2 r hr'
      simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh

theorem uniform_far (loc : D → X) (F B : Finset X) (hF : F.Nonempty)
    (v lam M eta : ℝ) (N : ℕ) (T : List (List X)) (f : X)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hMpos : 0 < M) (hN : 3 ≤ N) (hprice : lam ≤ 8*N*M)
    (hM : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M)
    (hsep : ∀ j i, i ∈ F → 1 ≤ dist i (loc j))
    (hf : ∀ j, 20*N*M ≤ dist (loc j) f)
    (hh : History loc F B v lam eta 0 ∅ T) (hlive : Live loc v 0 ∅ T) :
    ∀ r, r < T.length → ∀ j, (1+v^2)*(1+v^2)^(0+r) < (1-3*v)*dist (loc j) f := by
  have hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^0) ∅ i ≤ lam := by
    intro i hi
    have he : bidRow loc (1-3*v) ((1+v^2)^0) ∅ i = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp only [clippedAt,Finset.not_nonempty_empty,↓reduceIte,pow_zero]
      exact max_eq_right (by linarith only [hsep j i hi])
    rw [he]
    exact hlam.le
  have hphase := phases_bounded loc F B ∅ hF v lam M eta 0 T hv hvsmall hlam hM hrow hh hlive
  have hnum := DisablingCopy.numerical_bound v M N hv hvsmall hMpos hN
  intro r hr j
  calc
    (1+v^2)*(1+v^2)^(0+r) ≤ (1+v^2)*(M+8*N*M) := by
      gcongr
      exact (hphase r hr).trans (by linarith only [hprice])
    _ < (1-3*v)*(20*N*M) := hnum.1.trans hnum.2
    _ ≤ (1-3*v)*dist (loc j) f :=
      mul_le_mul_of_nonneg_left (hf j) (by linarith only [hvsmall])

theorem endpoint (loc : D → X) (F B : Finset X) (hF : F.Nonempty)
    (v lam M eta : ℝ) (N : ℕ) (H : List X) (T : List (List X)) (f : X)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hMpos : 0 < M) (hN : 3 ≤ N) (hprice : lam ≤ 8*N*M)
    (hM : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M)
    (hsep : ∀ j i, i ∈ F → 1 ≤ dist i (loc j))
    (hfresh : f ∉ F ∪ B) (hf : ∀ j, 20*N*M ≤ dist (loc j) f)
    (hh : History loc F B v lam eta 0 ∅ (H::T)) (hlive : Live loc v 0 ∅ (H::T))
    (hterm : ∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^(H::T).length) (after ∅ (H::T)) j) :
    History loc F (insert f B) v lam eta 0 ∅ ((f::H)::T) ∧
    (∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^((f::H)::T).length) (after ∅ ((f::H)::T)) j) ∧
    (after ∅ ((f::H)::T) ∩ F).card = (after ∅ (H::T) ∩ F).card ∧
    (after ∅ ((f::H)::T) \ F).card = (after ∅ (H::T) \ F).card+1 := by
  have hfar := uniform_far loc F B hF v lam M eta N (H::T) f hv hvsmall hlam
    hMpos hN hprice hM hsep hf hh hlive
  obtain ⟨hvalid,hcount⟩ := DisablingHistory.prepend_disabled_copy loc F B ∅ v lam eta f
    0 H T hvsmall hfresh (Finset.empty_subset _) hfar hh
  have he : after ∅ ((f::H)::T) = insert f (after ∅ (H::T)) := by
    simp only [after,List.toFinset_cons,Finset.union_insert,DisablingHistory.after_insert]
  have hsub := hh.after_subset (Finset.empty_subset _)
  have hfnot : f ∉ after ∅ (H::T) := fun h => hfresh (hsub h)
  have hfF : f ∉ F := fun h => hfresh (Finset.mem_union_left _ h)
  refine ⟨hvalid,?_,hcount,?_⟩
  · intro j hj
    apply hterm j
    intro i hi
    apply hj i
    rw [he]
    exact Finset.mem_insert_of_mem hi
  · rw [he]
    have hs : insert f (after ∅ (H::T)) \ F = insert f (after ∅ (H::T) \ F) := by
      ext i
      by_cases hi : i = f
      · subst i; simp [hfF]
      · simp [hi]
    rw [hs,Finset.card_insert_of_notMem]
    exact fun hi => hfnot (Finset.mem_sdiff.mp hi).1

end MetricKMedianRecovery.UniformDisablingEndpoint

namespace MetricKMedianRecovery.LeafMetric
variable {V C : Type*} [PseudoMetricSpace V]

def parent (root : C → V) : V ⊕ C → V := Sum.elim id root

def height (u : C → ℝ) : V ⊕ C → ℝ := Sum.elim (fun _ => 0) u

noncomputable def leafDist (root : C → V) (u : C → ℝ) (x y : V ⊕ C) : ℝ := by
  classical
  exact if x = y then 0 else height u x+dist (parent root x) (parent root y)+height u y

omit [PseudoMetricSpace V] in
lemma height_nonneg (u : C → ℝ) (hu : ∀ c, 0 ≤ u c) (x : V ⊕ C) : 0 ≤ height u x := by
  cases x with
  | inl => exact le_rfl
  | inr c => exact hu c

lemma leafDist_self (root : C → V) (u : C → ℝ) (x : V ⊕ C) : leafDist root u x x = 0 := by
  simp [leafDist]
lemma leafDist_nonneg (root : C → V) (u : C → ℝ) (hu : ∀ c, 0 ≤ u c) (x y : V ⊕ C) :
    0 ≤ leafDist root u x y := by
  unfold leafDist
  split_ifs
  · exact le_rfl
  · exact add_nonneg (add_nonneg (height_nonneg u hu x) dist_nonneg) (height_nonneg u hu y)
lemma leafDist_comm (root : C → V) (u : C → ℝ) (x y : V ⊕ C) :
    leafDist root u x y = leafDist root u y x := by
  by_cases h : x = y
  · subst y; rfl
  · simp only [leafDist,ite_eq_right h,ite_eq_right (Ne.symm h)]
    rw [dist_comm]
    ring
lemma leafDist_triangle (root : C → V) (u : C → ℝ) (hu : ∀ c, 0 ≤ u c) (x y z : V ⊕ C) :
    leafDist root u x z ≤ leafDist root u x y + leafDist root u y z := by
  by_cases hxz : x = z
  · subst z
    rw [leafDist_self]
    exact add_nonneg (leafDist_nonneg root u hu _ _) (leafDist_nonneg root u hu _ _)
  by_cases hxy : x = y
  · subst y
    rw [leafDist_self,zero_add]
  by_cases hyz : y = z
  · subst z
    rw [leafDist_self,add_zero]
  simp only [leafDist,ite_eq_right hxz,ite_eq_right hxy,ite_eq_right hyz]
  have h := dist_triangle (parent root x) (parent root y) (parent root z)
  have hh := height_nonneg u hu y
  linarith

@[instance_reducible]
noncomputable def attachedMetric (root : C → V) (u : C → ℝ) (hu : ∀ c, 0 ≤ u c) :
    PseudoMetricSpace (V ⊕ C) where
  dist := leafDist root u
  dist_self := leafDist_self root u
  dist_comm := leafDist_comm root u
  dist_triangle := leafDist_triangle root u hu

lemma original_distance (root : C → V) (u : C → ℝ) (x y : V) :
    leafDist root u (.inl x) (.inl y) = dist x y := by
  by_cases h : x = y
  · subst y; simp [leafDist_self]
  · simp [leafDist,h,height,parent]
lemma copy_distance (root : C → V) (u : C → ℝ) (x : V) (c : C) :
    leafDist root u (.inl x) (.inr c) = dist x (root c)+u c := by
  simp [leafDist,height,parent]
lemma copies_distance (root : C → V) (u : C → ℝ) (c d : C) (h : c ≠ d) :
    leafDist root u (.inr c) (.inr d) = u c+dist (root c) (root d)+u d := by
  simp [leafDist,h,height,parent]

lemma parent_nonexpansive (root : C → V) (u : C → ℝ) (hu : ∀ c, 0 ≤ u c) (x y : V ⊕ C) :
    dist (parent root x) (parent root y) ≤ leafDist root u x y := by
  by_cases h : x = y
  · subst y; simp [leafDist_self]
  · simp only [leafDist,ite_eq_right h]
    linarith only [height_nonneg u hu x,height_nonneg u hu y]

lemma shorten_distance (root : C → V) (u u' : C → ℝ) (hu' : ∀ c, u' c ≤ u c)
    (p : V) (x : V ⊕ C) : leafDist root u' (.inl p) x ≤ leafDist root u (.inl p) x := by
  cases x with
  | inl x => rw [original_distance,original_distance]
  | inr c => simp only [copy_distance]; linarith only [hu' c]

lemma shorten_distance_loss (root : C → V) (u u' : C → ℝ) (eps : ℝ) (heps : 0 ≤ eps)
    (hu' : ∀ c, u c ≤ u' c+eps) (p : V) (x : V ⊕ C) :
    leafDist root u (.inl p) x ≤ leafDist root u' (.inl p) x+eps := by
  cases x with
  | inl x => rw [original_distance,original_distance]; linarith only [heps]
  | inr c => simp only [copy_distance]; linarith only [hu' c]

end MetricKMedianRecovery.LeafMetric

end OAI
