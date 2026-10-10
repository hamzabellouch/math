import Mathlib
import OAI.Combinatorics.UniformKServer.Basic

namespace OAI

namespace UniformKServer
namespace Fallback

structure State (n k : ℕ) where
  position : Configuration n k
  marked : Finset (Fin k)

def pick {k : ℕ} (hk : 0 < k) (A : Finset (Fin k)) : Fin k :=
  if h : A.Nonempty then A.min' h else ⟨0,hk⟩

def coverers {n k : ℕ} (c : Configuration n k) (r : Fin n) : Finset (Fin k) :=
  Finset.univ.filter (fun j => c j = r)

def choose {n k : ℕ} (hk : 0 < k) (s : State n k) (r : Fin n) : Fin k :=
  if (coverers s.position r).Nonempty then pick hk (coverers s.position r)
  else pick hk (Finset.univ \ s.marked)

def step {n k : ℕ} (hk : 0 < k) (s : State n k) (r : Fin n) : State n k :=
  let j := choose hk s r
  ⟨serve s.position r j, insert j s.marked⟩

def trace {n k : ℕ} (hk : 0 < k) : State n k → List (Fin n) → History n k
  | _, [] => []
  | s, r :: w => (r,choose hk s r) :: trace hk (step hk s r) w

def run {n k : ℕ} (hk : 0 < k) : State n k → List (Fin n) → State n k
  | s, [] => s
  | s, r :: w => run hk (step hk s r) w

/-- A raw nonendpoint portion has at most k distinct requested points.
Marks are a subset of the points already seen in that same raw block. -/
def Valid {n k : ℕ} (s : State n k) (S : Finset (Fin n)) : Prop :=
  Function.Injective s.position ∧ s.marked.image s.position ⊆ S ∧ S.card ≤ k


theorem pick_mem {k : ℕ} (hk : 0 < k) (A : Finset (Fin k)) (hA : A.Nonempty) :
    pick hk A ∈ A := by
  simp only [pick, hA, ↓reduceDIte]
  exact A.min'_mem hA

@[simp] theorem mem_coverers {n k : ℕ} (c : Configuration n k) (r : Fin n)
    (j : Fin k) : j ∈ coverers c r ↔ c j = r := by simp [coverers]

theorem misses_card_lt {n k : ℕ} (s : State n k) (S : Finset (Fin n))
    (hv : Valid s S) (r : Fin n) (hr : r ∈ S)
    (hn : ¬(coverers s.position r).Nonempty) : s.marked.card < k := by
  have hs : r ∉ s.marked.image s.position := by
    intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    exact hn ⟨j, by simpa using hj⟩
  have hb : insert r (s.marked.image s.position) ⊆ S :=
    Finset.insert_subset hr hv.2.1
  have hc := Finset.card_le_card hb
  rw [Finset.card_insert_of_notMem hs,
    Finset.card_image_of_injective _ hv.1] at hc
  exact lt_of_lt_of_le (by omega) hv.2.2

theorem free_nonempty {k : ℕ} (m : Finset (Fin k)) (h : m.card < k) :
    (Finset.univ \ m).Nonempty := by
  apply Finset.nonempty_of_ne_empty
  intro he
  have hm : m = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    by_contra hj
    have : j ∈ Finset.univ \ m := by simp [hj]
    simp [he] at this
  simp [hm] at h

theorem choice_hit_or_free {n k : ℕ} (hk : 0 < k) (s : State n k)
    (S : Finset (Fin n)) (hv : Valid s S) (r : Fin n) (hr : r ∈ S) :
    s.position (choose hk s r) = r ∨ choose hk s r ∉ s.marked := by
  unfold choose
  split_ifs with hc
  · exact Or.inl ((mem_coverers _ _ _).1 (pick_mem hk _ hc))
  · right
    have hf := free_nonempty s.marked (misses_card_lt s S hv r hr hc)
    exact (Finset.mem_sdiff.mp (pick_mem hk _ hf)).2

theorem updated_injective {n k : ℕ} (hk : 0 < k) (s : State n k)
    (r : Fin n) (hs : Function.Injective s.position) :
    Function.Injective (step hk s r).position := by
  by_cases hc : (coverers s.position r).Nonempty
  · have hh : s.position (choose hk s r) = r := by
      simpa [choose, hc] using (mem_coverers _ _ _).1 (pick_mem hk _ hc)
    have he : (step hk s r).position = s.position := by
      dsimp [step, serve]
      conv_lhs => arg 3; rw [← hh]
      exact Function.update_eq_self _ _
    simpa [he] using hs
  · have hn : ∀ j, s.position j ≠ r := by
      intro j hj
      exact hc ⟨j, (mem_coverers _ _ _).2 hj⟩
    intro i j hij
    change Function.update s.position (choose hk s r) r i =
      Function.update s.position (choose hk s r) r j at hij
    by_cases hi : i = choose hk s r
    · subst i
      by_cases hj : j = choose hk s r
      · exact hj.symm
      · simp only [Function.update_self, Function.update_of_ne hj] at hij
        exact False.elim (hn j hij.symm)
    · by_cases hj : j = choose hk s r
      · subst j
        simp only [Function.update_self, Function.update_of_ne hi] at hij
        exact False.elim (hn i hij)
      · simp only [Function.update_of_ne hi, Function.update_of_ne hj] at hij
        exact hs hij

/-- Source Lemma fallback: the exact nonendpoint marking rule is feasible. -/
theorem step_guarantee {n k : ℕ} (hk : 0 < k) (s : State n k)
    (S : Finset (Fin n)) (hv : Valid s S) (r : Fin n) (hr : r ∈ S) :
    Valid (step hk s r) S ∧
    (∀ j ∈ s.marked, (step hk s r).position j = s.position j) := by
  have hh := choice_hit_or_free hk s S hv r hr
  have hp : ∀ j ∈ s.marked, (step hk s r).position j = s.position j := by
    intro j hj
    dsimp [step, serve]
    by_cases he : j = choose hk s r
    · subst j
      rw [Function.update_self]
      exact (hh.resolve_right (not_not.mpr hj)).symm
    · exact Function.update_of_ne he _ _
  refine ⟨⟨updated_injective hk s r hv.1, ?_, hv.2.2⟩, hp⟩
  intro p hp'
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp'
  change j ∈ insert (choose hk s r) s.marked at hj
  rcases Finset.mem_insert.mp hj with he | hj
  · subst j
    simpa [step, serve] using hr
  · rw [hp j hj]
    exact hv.2.1 (Finset.mem_image.mpr ⟨j,hj,rfl⟩)

theorem step_cost {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (D : ℝ) (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (s : State n k) (S : Finset (Fin n)) (hv : Valid s S)
    (r : Fin n) (hr : r ∈ S) :
    (d.distance (s.position (choose hk s r)) r : ℝ) + s.marked.card * D ≤
      (step hk s r).marked.card * D := by
  by_cases hm : choose hk s r ∈ s.marked
  · have hh := (choice_hit_or_free hk s S hv r hr).resolve_right (not_not.mpr hm)
    have hz : (d.distance r r : ℝ) = 0 := by exact_mod_cast (d.eq_zero r r).2 rfl
    simp [step, Finset.insert_eq_of_mem hm, hh, hz]
  · have hc : (step hk s r).marked.card = s.marked.card + 1 := by
      exact Finset.card_insert_of_notMem hm
    rw [hc, Nat.cast_add, Nat.cast_one]
    have hd := hdiam (s.position (choose hk s r)) r
    nlinarith

/-- Source Lemma fallback: first appearances cost at most kD, independently
of their number of repetitions. Empty and truncated portions are included. -/
theorem nonendpoint_cost {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (D : ℝ) (hD : 0 ≤ D) (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (s : State n k) (S : Finset (Fin n)) (hv : Valid s S)
    (w : List (Fin n)) (hw : ∀ r ∈ w, r ∈ S) :
    Valid (run hk s w) S ∧ (trace hk s w).map Prod.fst = w ∧
    costAlong d s.position (trace hk s w) ≤ ((k : ℝ) - s.marked.card) * D := by
  induction w generalizing s with
  | nil =>
    have hc : s.marked.card ≤ k := by
      simpa using Finset.card_le_card (Finset.subset_univ s.marked)
    have hc' : (s.marked.card : ℝ) ≤ k := by exact_mod_cast hc
    exact ⟨hv, rfl, by simpa [trace, costAlong] using mul_nonneg (sub_nonneg.mpr hc') hD⟩
  | cons r w ih =>
    have hr : r ∈ S := hw r (by simp)
    have hg := step_guarantee hk s S hv r hr
    have hi := ih (step hk s r) hg.1 (fun x hx => hw x (by simp [hx]))
    refine ⟨hi.1, ?_, ?_⟩
    · simpa [trace] using congrArg (List.cons r) hi.2.1
    · have hs := step_cost hk d D hdiam s S hv r hr
      change (d.distance (s.position (choose hk s r)) r : ℝ) +
        costAlong d (step hk s r).position (trace hk (step hk s r) w) ≤ _
      nlinarith [hi.2.2]

end Fallback

private theorem cost_nonneg {n k : ℕ} (d : RationalMetric n)
    (s : Configuration n k) (h : History n k) : 0 ≤ costAlong d s h := by
  induction h generalizing s with
  | nil => rfl
  | cons a h ih =>
    exact add_nonneg (by exact_mod_cast d.nonneg (s a.2) a.1) (ih _)

private theorem requests_of_small_cost {n k : ℕ} (d : RationalMetric n)
    (δ : ℝ) (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (s : Configuration n k) (h : History n k) (hc : costAlong d s h < δ) :
    ∀ r ∈ h.map Prod.fst, ∃ j, s j = r := by
  induction h generalizing s with
  | nil => simp
  | cons a h ih =>
    rcases a with ⟨r,j⟩
    have ht := cost_nonneg d (serve s r j) h
    have hh : s j = r := by
      by_contra hn
      have hd := hsep (s j) r hn
      simp only [costAlong] at hc
      linarith
    have hu : serve s r j = s := by
      unfold serve
      conv_lhs => arg 3; rw [← hh]
      exact Function.update_eq_self _ _
    have hz : (d.distance (s j) r : ℝ) = 0 := by
      exact_mod_cast (d.eq_zero (s j) r).2 hh
    have hc' : costAlong d s h < δ := by simpa [costAlong, hu, hz] using hc
    intro x hx
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨j, hh⟩
    · exact ih s hc' x hx

/-- Source Proposition suffix: every completed raw block forces at least
one positive move even from repeated initial positions. -/
theorem completed_block_cost {n k : ℕ} (d : RationalMetric n)
    (δ : ℝ) (_ : 0 < δ)
    (hsep : ∀ x y, x ≠ y → δ ≤ (d.distance x y : ℝ))
    (s : Configuration n k) (h : History n k)
    (hdistinct : k < (h.map Prod.fst).toFinset.card) :
    δ ≤ costAlong d s h := by
  by_contra hc
  have hs := requests_of_small_cost d δ hsep s h (lt_of_not_ge hc)
  have hsub : (h.map Prod.fst).toFinset ⊆ Finset.univ.image s := by
    intro r hr
    obtain ⟨j, hj⟩ := hs r (List.mem_toFinset.mp hr)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩
  have hl := Finset.card_le_card hsub
  have hu := Finset.card_image_le (s := Finset.univ) (f := s)
  simp only [Finset.card_univ, Fintype.card_fin] at hu
  omega


namespace Fallback

structure RawState (n k : ℕ) where
  marking : State n k
  seen : Finset (Fin n)
  completed : ℕ

def isEndpoint {n k : ℕ} (s : RawState n k) (r : Fin n) : Prop :=
  k < (insert r s.seen).card
instance {n k : ℕ} (s : RawState n k) (r : Fin n) : Decidable (isEndpoint s r) :=
  inferInstanceAs (Decidable (k < (insert r s.seen).card))

def rawChoice {n k : ℕ} (hk : 0 < k) (s : RawState n k) (r : Fin n) : Fin k :=
  if isEndpoint s r then pick hk (coverers s.marking.position r)
  else choose hk s.marking r

def rawStep {n k : ℕ} (hk : 0 < k) (s : RawState n k) (r : Fin n) : RawState n k :=
  if isEndpoint s r then
    ⟨⟨serve s.marking.position r (rawChoice hk s r), ∅⟩, ∅, s.completed + 1⟩
  else ⟨step hk s.marking r, insert r s.seen, s.completed⟩

def rawTrace {n k : ℕ} (hk : 0 < k) : RawState n k → List (Fin n) → History n k
  | _, [] => []
  | s, r :: w => (r,rawChoice hk s r) :: rawTrace hk (rawStep hk s r) w

def rawRun {n k : ℕ} (hk : 0 < k) : RawState n k → List (Fin n) → RawState n k
  | s, [] => s
  | s, r :: w => rawRun hk (rawStep hk s r) w

def portions {n k : ℕ} (s : RawState n k) : ℕ :=
  s.completed + if s.seen.Nonempty then 1 else 0


theorem endpoint_injective {n k : ℕ} (hk : 0 < k) (c : Configuration n k)
    (hc : Function.Injective c) (r : Fin n) :
    Function.Injective (serve c r (pick hk (coverers c r))) := by
  by_cases hcov : (coverers c r).Nonempty
  · have hh : c (pick hk (coverers c r)) = r :=
      (mem_coverers _ _ _).1 (pick_mem hk _ hcov)
    have he : serve c r (pick hk (coverers c r)) = c := by
      unfold serve
      conv_lhs => arg 3; rw [← hh]
      exact Function.update_eq_self _ _
    simpa [he] using hc
  · have hf : ∀ j, c j ≠ r := fun j hj => hcov ⟨j, by simpa using hj⟩
    intro i j hij
    change Function.update c (pick hk (coverers c r)) r i =
      Function.update c (pick hk (coverers c r)) r j at hij
    by_cases hi : i = pick hk (coverers c r)
    · subst i
      by_cases hj : j = pick hk (coverers c r)
      · exact hj.symm
      · simp only [Function.update_self, Function.update_of_ne hj] at hij
        exact (hf j hij.symm).elim
    · by_cases hj : j = pick hk (coverers c r)
      · subst j
        simp only [Function.update_self, Function.update_of_ne hi] at hij
        exact (hf i hij).elim
      · simp only [Function.update_of_ne hi, Function.update_of_ne hj] at hij
        exact hc hij

theorem raw_step_valid {n k : ℕ} (hk : 0 < k) (s : RawState n k)
    (hv : Valid s.marking s.seen) (r : Fin n) :
    Valid (rawStep hk s r).marking (rawStep hk s r).seen := by
  by_cases he : isEndpoint s r
  · simp only [rawStep, he, ↓reduceIte, rawChoice]
    exact ⟨endpoint_injective hk _ hv.1 r, by simp, by simp⟩
  · have hn : (insert r s.seen).card ≤ k := le_of_not_gt he
    have hv' : Valid s.marking (insert r s.seen) :=
      ⟨hv.1, hv.2.1.trans (Finset.subset_insert _ _), hn⟩
    simpa [rawStep, he] using
      (step_guarantee hk s.marking (insert r s.seen) hv' r (by simp)).1

theorem raw_step_position {n k : ℕ} (hk : 0 < k) (s : RawState n k) (r : Fin n) :
    (rawStep hk s r).marking.position = serve s.marking.position r (rawChoice hk s r) := by
  by_cases he : isEndpoint s r <;> simp [rawStep, rawChoice, step, he]

/-- Marked points pay the unfinished part of the current block; completed
blocks pay their endpoint as well. This potential prevents a charge per raw
request, even when an epoch is arbitrarily long. -/
def ledger {n k : ℕ} (D : ℝ) (s : RawState n k) : ℝ :=
  s.completed * (k+1) * D + s.marking.marked.card * D

theorem raw_step_cost {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (D : ℝ) (hD : 0 ≤ D) (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (s : RawState n k) (hv : Valid s.marking s.seen) (r : Fin n) :
    (d.distance (s.marking.position (rawChoice hk s r)) r : ℝ) + ledger D s ≤
      ledger D (rawStep hk s r) := by
  by_cases he : isEndpoint s r
  · have hcard : s.marking.marked.card ≤ k := by
      simpa using Finset.card_le_card (Finset.subset_univ s.marking.marked)
    have hcard' : (s.marking.marked.card : ℝ) ≤ k := by exact_mod_cast hcard
    have hh := hdiam (s.marking.position (rawChoice hk s r)) r
    simp only [ledger, rawStep, he, ↓reduceIte, Finset.card_empty, Nat.cast_zero,
      zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
    nlinarith [mul_le_mul_of_nonneg_right hcard' hD]
  · have hv' : Valid s.marking (insert r s.seen) :=
      ⟨hv.1, hv.2.1.trans (Finset.subset_insert _ _), le_of_not_gt he⟩
    have hb := step_cost hk d D hdiam s.marking (insert r s.seen) hv' r (by simp)
    simpa [rawChoice, rawStep, he, ledger, add_assoc, add_left_comm, add_comm] using
      add_le_add_left hb (s.completed * (k+1) * D)

theorem raw_run_ledger {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (D : ℝ) (hD : 0 ≤ D) (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (s : RawState n k) (hv : Valid s.marking s.seen) (w : List (Fin n)) :
    Valid (rawRun hk s w).marking (rawRun hk s w).seen ∧
    (rawTrace hk s w).map Prod.fst = w ∧
    costAlong d s.marking.position (rawTrace hk s w) + ledger D s ≤
      ledger D (rawRun hk s w) := by
  induction w generalizing s with
  | nil => exact ⟨hv, rfl, by simp [rawTrace, rawRun, costAlong]⟩
  | cons r w ih =>
    have hv' := raw_step_valid hk s hv r
    have hi := ih (rawStep hk s r) hv'
    have hs := raw_step_cost hk d D hD hdiam s hv r
    refine ⟨hi.1, ?_, ?_⟩
    · simpa [rawTrace] using congrArg (List.cons r) hi.2.1
    · simp only [rawTrace, costAlong, rawRun]
      rw [← raw_step_position]
      linarith [hi.2.2]

theorem ledger_le_portions {n k : ℕ} (D : ℝ) (hD : 0 ≤ D) (s : RawState n k)
    (hv : Valid s.marking s.seen) : ledger D s ≤ portions s * (k+1) * D := by
  by_cases he : s.seen.Nonempty
  · have hcard : s.marking.marked.card ≤ k := by
      simpa using Finset.card_le_card (Finset.subset_univ s.marking.marked)
    have hcard' : (s.marking.marked.card : ℝ) ≤ k+1 := by exact_mod_cast (by omega : s.marking.marked.card ≤ k+1)
    have hm := mul_le_mul_of_nonneg_right hcard' hD
    simp only [ledger, portions, he, ↓reduceIte, Nat.cast_add, Nat.cast_one]
    nlinarith
  · have hem : s.seen = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have hmarks : s.marking.marked = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have h := hv.2.1 (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
      simp [hem] at h
    simp [ledger, portions, he, hmarks]

/-- The literal marking fallback of Section 03, including raw block endpoints,
an inherited pre-switch raw block, and any finite truncation. -/
theorem raw_fallback_bound {n k : ℕ} (hk : 0 < k) (d : RationalMetric n)
    (D : ℝ) (hD : 0 ≤ D) (hdiam : ∀ x y, (d.distance x y : ℝ) ≤ D)
    (c : Configuration n k) (hc : Function.Injective c)
    (seen : Finset (Fin n)) (hs : seen.card ≤ k)
    (w : List (Fin n)) (R : ℕ)
    (hR : portions (rawRun hk ⟨⟨c,∅⟩,seen,0⟩ w) ≤ R) :
    Valid (rawRun hk ⟨⟨c,∅⟩,seen,0⟩ w).marking
      (rawRun hk ⟨⟨c,∅⟩,seen,0⟩ w).seen ∧
    (rawTrace hk ⟨⟨c,∅⟩,seen,0⟩ w).map Prod.fst = w ∧
    costAlong d c (rawTrace hk ⟨⟨c,∅⟩,seen,0⟩ w) ≤ R * (k+1) * D := by
  have hv : Valid (⟨c,∅⟩ : State n k) seen := ⟨hc, by simp, hs⟩
  have hr := raw_run_ledger hk d D hD hdiam ⟨⟨c,∅⟩,seen,0⟩ hv w
  have hb := ledger_le_portions D hD (rawRun hk ⟨⟨c,∅⟩,seen,0⟩ w) hr.1
  have hR' : ((portions (rawRun hk ⟨⟨c,∅⟩,seen,0⟩ w) : ℕ) : ℝ) ≤ R := by
    exact_mod_cast hR
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hR' (by positivity : (0:ℝ) ≤ k+1)) hD
  refine ⟨hr.1, hr.2.1, ?_⟩
  have hl : ledger D (⟨⟨c,∅⟩,seen,0⟩ : RawState n k) = 0 := by simp [ledger]
  rw [hl, add_zero] at hr
  exact hr.2.2.trans (hb.trans hm)

end Fallback
end UniformKServer


end OAI
