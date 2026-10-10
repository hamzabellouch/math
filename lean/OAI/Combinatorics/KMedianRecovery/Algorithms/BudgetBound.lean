import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ImagePhaseUnion
import OAI.Combinatorics.KMedianRecovery.Recovery.ActiveInsert

namespace OAI

namespace MetricKMedianRecovery.UniformRowDisabling
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [DecidableEq X] in

lemma budget_bound (loc : D → X) (F Q : Finset X) (hF : F.Nonempty)
    (t z lam M : ℝ) (hrow : ∀ i ∈ F, bidRow loc t z Q i ≤ lam)
    (hM : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (j : D) :
    clippedAt loc t z Q j ≤ M+lam := by
  obtain ⟨i,hi⟩ := hF
  have hsum : max (clippedAt loc t z Q j-dist i (loc j)) 0 ≤ bidRow loc t z Q i :=
    Finset.single_le_sum (fun a _ => le_max_right (clippedAt loc t z Q a-dist i (loc a)) 0)
      (Finset.mem_univ j)
  have hh := (le_max_left (clippedAt loc t z Q j-dist i (loc j)) 0).trans (hsum.trans (hrow i hi))
  linarith only [hh,hM i hi j]

omit [Fintype D] in
lemma active_insert (loc : D → X) (Q : Finset X) (t z K W : ℝ) (f : X)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hW : 0 ≤ W)
    (hbound : ∀ j, clippedAt loc t z Q j ≤ W)
    (hfar : ∀ j, K*W < t*dist (loc j) f) (j : D) :
    activeAt loc t z (insert f Q) j ↔ activeAt loc t z Q j := by
  constructor
  · intro h i hi
    exact h i (Finset.mem_insert_of_mem hi)
  · intro h i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have hz : z ≤ W := by simpa only [clippedAt_of_active loc t z Q j ht h] using hbound j
      exact (hz.trans (by nlinarith only [hK,hW] : W ≤ K*W)).trans_lt (hfar j)
    · exact h i hi

omit [Fintype D] in
lemma inactive_distance (loc : D → X) (Q : Finset X) (t z K W : ℝ) (f : X)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hW : 0 ≤ W)
    (hbound : ∀ j, clippedAt loc t z Q j ≤ W)
    (hfar : ∀ j, K*W < t*dist (loc j) f) (j : D) (hj : ¬activeAt loc t z Q j) :
    t*nearestDistance (loc j) (insert f Q) = t*nearestDistance (loc j) Q := by
  have hQ := inactive_nonempty loc t z Q j hj
  have hb : t*nearestDistance (loc j) Q ≤ W := by
    simpa only [clippedAt_of_inactive loc t z Q j ht hj] using hbound j
  apply le_antisymm
  · exact mul_le_mul_of_nonneg_left
      (nearestDistance_antitone _ _ _ hQ (Finset.subset_insert _ _)) ht
  · obtain ⟨g,hg,he⟩ := nearestDistance_attained (loc j) (insert f Q) (Finset.insert_nonempty _ _)
    rw [he]
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact (hb.trans (by nlinarith only [hK,hW] : W ≤ K*W)).trans (hfar j).le
    · exact mul_le_mul_of_nonneg_left (nearestDistance_le_mem _ _ _ hg) ht

omit [Fintype D] in
lemma admissible_insert (loc : D → X) (Q : Finset X) (t z K W v : ℝ) (f i : X)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hW : 0 ≤ W)
    (hbound : ∀ j, clippedAt loc t z Q j ≤ W)
    (hfar : ∀ j, K*W < t*dist (loc j) f) (tau : D → ℝ) :
    admissibleBids loc t K v z (insert f Q) i tau ↔ admissibleBids loc t K v z Q i tau := by
  constructor
  · intro h j hj
    have hh := h j ((active_insert loc Q t z K W f ht hK hW hbound hfar j).mpr hj)
    exact ⟨hh.1,hh.2.1,(fun g hg => hh.2.2.1 g (Finset.mem_insert_of_mem hg)),hh.2.2.2⟩
  · intro h j hj
    have hj' := (active_insert loc Q t z K W f ht hK hW hbound hfar j).mp hj
    have hh := h j hj'
    refine ⟨hh.1,hh.2.1,?_,hh.2.2.2⟩
    intro g hg
    rcases Finset.mem_insert.mp hg with rfl | hg
    · have hz : z ≤ W := by simpa only [clippedAt_of_active loc t z Q j ht hj'] using hbound j
      exact hh.2.1.trans ((mul_le_mul_of_nonneg_left hz (by linarith only [hK])).trans (hfar j).le)
    · exact hh.2.2.1 g hg

lemma payment_insert (loc : D → X) (Q : Finset X) (t z K W : ℝ) (f i : X)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hW : 0 ≤ W)
    (hbound : ∀ j, clippedAt loc t z Q j ≤ W)
    (hfar : ∀ j, K*W < t*dist (loc j) f) (tau : D → ℝ) :
    openingPayment loc t z (insert f Q) i tau = openingPayment loc t z Q i tau := by
  classical
  unfold openingPayment
  apply Finset.sum_congr rfl
  intro j _
  rw [active_insert loc Q t z K W f ht hK hW hbound hfar j]
  by_cases hj : activeAt loc t z Q j
  · simp only [ite_eq_left hj]
  · simp only [ite_eq_right hj,inactive_distance loc Q t z K W f ht hK hW hbound hfar j hj]

lemma dual_insert (loc : D → X) (Q : Finset X) (t z K W : ℝ) (f i : X)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hW : 0 ≤ W)
    (hbound : ∀ j, clippedAt loc t z Q j ≤ W)
    (hfar : ∀ j, K*W < t*dist (loc j) f) (tau : D → ℝ) (a : D) :
    openingDual loc t z (insert f Q) i tau a = openingDual loc t z Q i tau a := by
  classical
  simp only [openingDual,active_insert loc Q t z K W f ht hK hW hbound hfar]

theorem openable_insert (loc : D → X) (F Q : Finset X) (t z K W v lam eta : ℝ) (f i : X)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hW : 0 ≤ W)
    (hbound : ∀ j, clippedAt loc t z Q j ≤ W)
    (hfar : ∀ j, K*W < t*dist (loc j) f) :
    etaOpenable loc F (insert f Q) t K v z lam eta i ↔ etaOpenable loc F Q t K v z lam eta i := by
  simp only [etaOpenable,admissible_insert loc Q t z K W v f i ht hK hW hbound hfar,
    payment_insert loc Q t z K W f i ht hK hW hbound hfar,
    dual_insert loc Q t z K W f _ ht hK hW hbound hfar,
    active_insert loc Q t z K W f ht hK hW hbound hfar]

lemma entry_insert (loc : D → X) (F B Q : Finset X) (v z lam eta W : ℝ) (f i : X)
    (hv : v < 1/6) (hW : 0 ≤ W) (hf : f ∉ F ∪ B)
    (hbound : ∀ j, clippedAt loc (1-3*v) z Q j ≤ W)
    (hfar : ∀ j, (1+v^2)*W < (1-3*v)*dist (loc j) f)
    (h : Entry loc F B Q v z lam eta i) :
    Entry loc F (insert f B) (insert f Q) v z lam eta i := by
  have ht : 0 ≤ 1-3*v := by linarith only [hv]
  have hif := DisablingHistory.member_ne F B f i hf h.mem
  refine ⟨by simpa only [Finset.mem_insert,not_or] using And.intro hif h.1,?_⟩
  rcases h.2 with hi | ⟨hi,S,hQ,hS,hop⟩
  · exact Or.inl (Finset.mem_insert_of_mem hi)
  · right
    refine ⟨hi,insert f S,Finset.insert_subset_insert f hQ,?_,?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      · exact (Finset.union_subset_union_right (Finset.subset_insert _ _)) (hS hx)
    · exact (openable_insert loc F S (1-3*v) z (1+v^2) W v lam eta f i ht
        (by nlinarith only [sq_nonneg v]) hW
        (fun j => (clippedAt_antitone_open loc (1-3*v) z Q S j ht hQ).trans (hbound j)) hfar).mpr hop

lemma prefix_insert (loc : D → X) (F B Q : Finset X) (v z lam eta W : ℝ) (f : X)
    (H : List X) (hv : v < 1/6) (hW : 0 ≤ W) (hf : f ∉ F ∪ B)
    (hbound : ∀ j, clippedAt loc (1-3*v) z Q j ≤ W)
    (hfar : ∀ j, (1+v^2)*W < (1-3*v)*dist (loc j) f)
    (h : Prefix loc F B v z lam eta Q H) :
    Prefix loc F (insert f B) v z lam eta (insert f Q) H := by
  induction h with
  | nil Q => exact Prefix.nil _
  | @cons Q i H hi htail ih =>
    apply Prefix.cons (entry_insert loc F B Q v z lam eta W f i hv hW hf hbound hfar hi)
    rw [Finset.insert_comm]
    apply ih
    intro j
    exact (clippedAt_antitone_open loc (1-3*v) z Q (insert i Q) j
      (by linarith only [hv]) (Finset.subset_insert _ _)).trans (hbound j)

lemma valid_insert (loc : D → X) (F B Q : Finset X) (v z lam eta W : ℝ) (f : X)
    (H : List X) (hv : v < 1/6) (hW : 0 ≤ W) (hf : f ∉ F ∪ B)
    (hbound : ∀ j, clippedAt loc (1-3*v) z Q j ≤ W)
    (hfar : ∀ j, (1+v^2)*W < (1-3*v)*dist (loc j) f)
    (h : Valid loc F B Q v z lam eta H) :
    Valid loc F (insert f B) (insert f Q) v z lam eta H := by
  refine ⟨prefix_insert loc F B Q v z lam eta W f H hv hW hf hbound hfar h.1,?_⟩
  intro i hi hnot hop
  have hiQ : i ∉ Q ∪ H.toFinset := by
    intro hh
    apply hnot
    simpa only [Finset.insert_union] using Finset.mem_insert_of_mem hh
  apply h.2 i hi hiQ
  apply (openable_insert loc F (Q ∪ H.toFinset) (1-3*v) z (1+v^2) W v lam 0 f i
    (by linarith only [hv]) (by nlinarith only [sq_nonneg v]) hW
    (fun j => (clippedAt_antitone_open loc (1-3*v) z Q (Q ∪ H.toFinset) j
      (by linarith only [hv]) Finset.subset_union_left).trans (hbound j)) hfar).mp
  simpa only [Finset.insert_union] using hop

theorem history_insert (loc : D → X) (F B Q : Finset X) (hF : F.Nonempty)
    (v lam eta M : ℝ) (f : X) (q : ℕ) (T : List (List X))
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (hM : 0 ≤ M)
    (hf : f ∉ F ∪ B) (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M)
    (hfar : ∀ j, (1+v^2)*(M+lam) < (1-3*v)*dist (loc j) f)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (h : History loc F B v lam eta q Q T) :
    History loc F (insert f B) v lam eta q (insert f Q) T := by
  induction h with
  | nil q Q => exact History.nil _ _
  | @cons q Q H T hhead htail ih =>
    apply History.cons (valid_insert loc F B Q v ((1+v^2)^q) lam eta (M+lam) f H
      hvsmall (add_nonneg hM hlam.le) hf (budget_bound loc F Q hF (1-3*v)
        ((1+v^2)^q) lam M hrow hdiam) hfar hhead)
    rw [Finset.insert_union]
    exact ih (advance_rows loc F B Q v lam eta q H hv hvsmall hlam hrow hhead)

lemma attains_insert {loc : D → X} {F B Q : Finset X} {v lam : ℝ} {q n c : ℕ}
    (h : Attains loc F B Q v lam q n c) (hF : F.Nonempty) (M : ℝ) (f : X)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (hM : 0 ≤ M)
    (hf : f ∉ F ∪ B) (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M)
    (hfar : ∀ j, (1+v^2)*(M+lam) < (1-3*v)*dist (loc j) f)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam) :
    Attains loc F (insert f B) (insert f Q) v lam q n c := by
  obtain ⟨T,hT,hh,hr,hc⟩ := h
  refine ⟨T,hT,history_insert loc F B Q hF v lam 0 M f q T hv hvsmall hlam hM hf hdiam hfar hrow hh,hr,?_⟩
  rw [DisablingHistory.after_insert,Finset.insert_inter_of_notMem
    (fun he => hf (Finset.mem_union_left _ he))]
  exact hc

end MetricKMedianRecovery.UniformRowDisabling

end OAI
