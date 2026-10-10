import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Entry

namespace OAI

namespace MetricKMedianRecovery.DisablingCopy
variable {D X : Type*} [PseudoMetricSpace X] [DecidableEq X]

lemma active_insert (loc : D → X) (t z : ℝ) (Q : Finset X) (f : X)
    (hfar : ∀ j, z < t * dist (loc j) f) (j : D) :
    activeAt loc t z (insert f Q) j ↔ activeAt loc t z Q j := by
  simp only [activeAt, Finset.mem_insert, forall_eq_or_imp]
  exact and_iff_right (hfar j)

lemma inactive_distance (loc : D → X) (t z : ℝ) (Q : Finset X) (f : X)
    (ht : 0 ≤ t) (hfar : ∀ j, z < t * dist (loc j) f)
    (j : D) (hj : ¬activeAt loc t z Q j) :
    t * nearestDistance (loc j) (insert f Q) = t * nearestDistance (loc j) Q := by
  have hQ := inactive_nonempty loc t z Q j hj
  have hz : t * nearestDistance (loc j) Q ≤ z :=
    not_lt.mp (fun h => hj ((activeAt_iff loc t z Q j ht hQ).mpr h))
  apply le_antisymm
  · exact mul_le_mul_of_nonneg_left
      (nearestDistance_antitone (loc j) Q (insert f Q) hQ (Finset.subset_insert _ _)) ht
  · obtain ⟨g,hg,he⟩ := nearestDistance_attained (loc j) (insert f Q) (Finset.insert_nonempty _ _)
    rw [he]
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact hz.trans (hfar j).le
    · exact mul_le_mul_of_nonneg_left (nearestDistance_le_mem _ _ _ hg) ht

lemma budgets_insert (loc : D → X) (t z : ℝ) (Q : Finset X) (f : X)
    (ht : 0 ≤ t) (hfar : ∀ j, z < t * dist (loc j) f) (j : D) :
    clippedAt loc t z (insert f Q) j = clippedAt loc t z Q j := by
  by_cases hj : activeAt loc t z Q j
  · rw [clippedAt_of_active loc t z Q j ht hj,
      clippedAt_of_active loc t z (insert f Q) j ht ((active_insert loc t z Q f hfar j).mpr hj)]
  · have hj' := fun h => hj ((active_insert loc t z Q f hfar j).mp h)
    rw [clippedAt_of_inactive loc t z Q j ht hj,
      clippedAt_of_inactive loc t z (insert f Q) j ht hj']
    exact inactive_distance loc t z Q f ht hfar j hj

lemma admissible_insert (loc : D → X) (t K v z : ℝ) (Q : Finset X)
    (f i : X) (tau : D → ℝ) (hz : 0 ≤ z) (hK : 1 ≤ K)
    (hfar : ∀ j, K*z < t * dist (loc j) f) :
    admissibleBids loc t K v z (insert f Q) i tau ↔
      admissibleBids loc t K v z Q i tau := by
  have hf : ∀ j, z < t*dist (loc j) f := fun j =>
    (by nlinarith only [hz,hK] : z ≤ K*z).trans_lt (hfar j)
  constructor
  · intro hb j hj
    have hh := hb j ((active_insert loc t z Q f hf j).mpr hj)
    exact ⟨hh.1,hh.2.1,(fun g hg => hh.2.2.1 g (Finset.mem_insert_of_mem hg)),hh.2.2.2⟩
  · intro hb j hj
    have hh := hb j ((active_insert loc t z Q f hf j).mp hj)
    refine ⟨hh.1,hh.2.1,?_,hh.2.2.2⟩
    intro g hg
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact hh.2.1.trans (hfar j).le
    · exact hh.2.2.1 g hg

variable [Fintype D]

lemma payment_insert (loc : D → X) (t z : ℝ) (Q : Finset X)
    (f i : X) (tau : D → ℝ) (ht : 0 ≤ t)
    (hfar : ∀ j, z < t * dist (loc j) f) :
    openingPayment loc t z (insert f Q) i tau = openingPayment loc t z Q i tau := by
  classical
  unfold openingPayment
  apply Finset.sum_congr rfl
  intro j _
  rw [active_insert loc t z Q f hfar j]
  by_cases hj : activeAt loc t z Q j
  · simp only [ite_eq_left hj]
  · simp only [ite_eq_right hj, inactive_distance loc t z Q f ht hfar j hj]

lemma dual_insert (loc : D → X) (t z : ℝ) (Q : Finset X)
    (f i : X) (tau : D → ℝ) (hfar : ∀ j, z < t * dist (loc j) f) (a : D) :
    openingDual loc t z (insert f Q) i tau a = openingDual loc t z Q i tau a := by
  classical
  simp only [openingDual,active_insert loc t z Q f hfar]

theorem openable_insert (loc : D → X) (F Q : Finset X) (t K v z lam eta : ℝ)
    (f i : X) (ht : 0 ≤ t) (hz : 0 ≤ z) (hK : 1 ≤ K)
    (hfar : ∀ j, K*z < t * dist (loc j) f) :
    etaOpenable loc F (insert f Q) t K v z lam eta i ↔
      etaOpenable loc F Q t K v z lam eta i := by
  have hf : ∀ j, z < t*dist (loc j) f := fun j =>
    (by nlinarith only [hz,hK] : z ≤ K*z).trans_lt (hfar j)
  simp only [etaOpenable,admissible_insert loc t K v z Q f _ _ hz hK hfar,
    payment_insert loc t z Q f _ _ ht hf,dual_insert loc t z Q f _ _ hf,
    active_insert loc t z Q f hf]

lemma numerical_bound (v M : ℝ) (N : ℕ) (hv : 0 < v) (hv' : v < 1/6)
    (hM : 0 < M) (hN : 3 ≤ N) :
    (1+v^2)*(M+8*N*M) < 10*N*M ∧ 10*N*M < (1-3*v)*(20*N*M) := by
  have hv2 : v^2 < 1/36 := by nlinarith
  have hn : (3:ℝ) ≤ N := by exact_mod_cast hN
  constructor
  · have hz : 0 < M+8*N*M := by positivity
    have hh := mul_lt_mul_of_pos_right hv2 hz
    have hnm : 3*M ≤ N*M := mul_le_mul_of_nonneg_right hn hM.le
    nlinarith
  · have hnm : 0 < (N:ℝ)*M := mul_pos (by linarith) hM
    nlinarith

end MetricKMedianRecovery.DisablingCopy

namespace MetricKMedianRecovery.DisablingHistory
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [PseudoMetricSpace X] in
lemma member_ne (F B : Finset X) (f i : X) (hf : f ∉ F ∪ B) (hi : i ∈ F ∪ B) : i ≠ f := by
  rintro rfl
  exact hf hi

theorem entry_insert (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (f i : X)
    (hv : v < 1/6) (hz : 0 ≤ z) (hf : f ∉ F ∪ B)
    (hfar : ∀ j, (1+v^2)*z < (1-3*v)*dist (loc j) f)
    (h : PhaseSequence.Entry loc F B Q v z lam eta i) :
    PhaseSequence.Entry loc F (insert f B) (insert f Q) v z lam eta i := by
  have hif : i ≠ f := member_ne F B f i hf (by
    rcases h.2 with hfree | hregular
    · exact Finset.mem_union_right _ hfree
    · exact Finset.mem_union_left _ hregular.1)
  refine ⟨by simpa only [Finset.mem_insert,not_or] using And.intro hif h.1,?_⟩
  rcases h.2 with hi | ⟨hi,W,hQ,hW,hcert⟩
  · exact Or.inl (Finset.mem_insert_of_mem hi)
  · right
    refine ⟨hi,insert f W,Finset.insert_subset_insert f hQ,?_,?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      · rcases Finset.mem_union.mp (hW hx) with hx | hx
        · exact Finset.mem_union_left _ hx
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hx)
    · exact (DisablingCopy.openable_insert loc F W (1-3*v) (1+v^2) v z lam eta f i
        (by linarith only [hv]) hz (by nlinarith only [sq_nonneg v]) hfar).mpr hcert

theorem prefix_insert (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (f : X)
    (H : List X) (hv : v < 1/6) (hz : 0 ≤ z) (hf : f ∉ F ∪ B)
    (hfar : ∀ j, (1+v^2)*z < (1-3*v)*dist (loc j) f)
    (h : PhaseSequence.Prefix loc F B v z lam eta Q H) :
    PhaseSequence.Prefix loc F (insert f B) v z lam eta (insert f Q) H := by
  induction h with
  | nil Q => exact PhaseSequence.Prefix.nil _
  | @cons Q i H hi htail ih =>
    apply PhaseSequence.Prefix.cons (entry_insert loc F B Q v z lam eta f i hv hz hf hfar hi)
    simpa only [Finset.insert_comm] using ih

theorem valid_insert (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (f : X)
    (H : List X) (hv : v < 1/6) (hz : 0 ≤ z) (hf : f ∉ F ∪ B)
    (hfar : ∀ j, (1+v^2)*z < (1-3*v)*dist (loc j) f)
    (h : PhaseSequence.Valid loc F B Q v z lam eta H) :
    PhaseSequence.Valid loc F (insert f B) (insert f Q) v z lam eta H := by
  refine ⟨prefix_insert loc F B Q v z lam eta f H hv hz hf hfar h.1,?_⟩
  intro i hi hnot hcoin
  have hnot' : i ∉ Q ∪ H.toFinset := by
    intro hh
    apply hnot
    simpa only [Finset.insert_union] using Finset.mem_insert_of_mem hh
  apply h.2 i hi hnot'
  apply (DisablingCopy.openable_insert loc F (Q ∪ H.toFinset) (1-3*v) (1+v^2) v z lam 0 f i
    (by linarith only [hv]) hz (by nlinarith only [sq_nonneg v]) hfar).mp
  simpa only [Finset.insert_union] using hcoin

theorem history_insert (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (f : X)
    (q : ℕ) (T : List (List X)) (hv : v < 1/6) (hf : f ∉ F ∪ B)
    (hfar : ∀ r, r < T.length → ∀ j, (1+v^2)*(1+v^2)^(q+r) < (1-3*v)*dist (loc j) f)
    (h : PhaseHistoryTransfer.History loc F B v lam eta q Q T) :
    PhaseHistoryTransfer.History loc F (insert f B) v lam eta q (insert f Q) T := by
  induction h with
  | nil q Q => exact PhaseHistoryTransfer.History.nil _ _
  | @cons q Q H T hhead htail ih =>
    apply PhaseHistoryTransfer.History.cons
    · exact valid_insert loc F B Q v ((1+v^2)^q) lam eta f H hv (by positivity) hf
        (by simpa only [Nat.add_zero] using hfar 0 (by simp)) hhead
    · rw [Finset.insert_union]
      apply ih
      intro r hr j
      have hh := hfar (r+1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hr) j
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh

omit [PseudoMetricSpace X] in
lemma after_insert (Q : Finset X) (T : List (List X)) (f : X) :
    PhaseHistoryTransfer.after (insert f Q) T = insert f (PhaseHistoryTransfer.after Q T) := by
  induction T generalizing Q with
  | nil => rfl
  | cons H T ih =>
    simp only [PhaseHistoryTransfer.after,Finset.insert_union]
    exact ih _

theorem prepend_disabled_copy (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (f : X)
    (q : ℕ) (H : List X) (T : List (List X)) (hv : v < 1/6) (hf : f ∉ F ∪ B)
    (hQ : Q ⊆ F ∪ B)
    (hfar : ∀ r, r < (H::T).length → ∀ j,
      (1+v^2)*(1+v^2)^(q+r) < (1-3*v)*dist (loc j) f)
    (h : PhaseHistoryTransfer.History loc F B v lam eta q Q (H::T)) :
    PhaseHistoryTransfer.History loc F (insert f B) v lam eta q Q ((f::H)::T) ∧
    (PhaseHistoryTransfer.after Q ((f::H)::T) ∩ F).card =
      (PhaseHistoryTransfer.after Q (H::T) ∩ F).card := by
  cases h with
  | cons hhead htail =>
    have hfQ : f ∉ Q := fun hh => hf (hQ hh)
    have hfar0 : ∀ j, (1+v^2)*(1+v^2)^q < (1-3*v)*dist (loc j) f := by
      simpa only [Nat.add_zero] using hfar 0 (by simp)
    have hvalid := valid_insert loc F B Q v ((1+v^2)^q) lam eta f H hv (by positivity) hf hfar0 hhead
    have htail' := history_insert loc F B (Q ∪ H.toFinset) v lam eta f (q+1) T hv hf
      (by
        intro r hr j
        have hh := hfar (r+1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hr) j
        simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh) htail
    constructor
    · apply PhaseHistoryTransfer.History.cons
      · constructor
        · exact PhaseSequence.Prefix.cons ⟨hfQ,Or.inl (Finset.mem_insert_self _ _)⟩ hvalid.1
        · simpa only [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using hvalid.2
      · simpa only [List.toFinset_cons,Finset.union_insert] using htail'
    · have hiF : f ∉ F := fun hh => hf (Finset.mem_union_left _ hh)
      have he (S : Finset X) : insert f S ∩ F = S ∩ F := by
        ext x
        by_cases hx : x = f
        · subst x; simp [hiF]
        · simp [hx]
      simp only [PhaseHistoryTransfer.after,List.toFinset_cons,Finset.union_insert,after_insert,he]

end MetricKMedianRecovery.DisablingHistory

end OAI
