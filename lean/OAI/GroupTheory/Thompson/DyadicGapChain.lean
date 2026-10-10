import OAI.GroupTheory.Thompson.BasicInterval

namespace OAI

/-!
# Consecutive dyadic cells

A chain is an ordered list of actual basic intervals whose consecutive
endpoints agree. Its endpoints and coverage are proved from this data.
-/

namespace ThompsonNonamenability

noncomputable section

/-- A finite list of consecutive cells starts at `a` and ends at `b`.
The empty list represents a gap of length zero. -/
def GapChain : ℝ → ℝ → List BasicInterval → Prop
  | a, b, [] => a = b
  | a, b, I :: L => I.left = a ∧ GapChain I.right b L

namespace GapChain

@[simp] theorem nil_iff {a b : ℝ} : GapChain a b [] ↔ a = b := Iff.rfl

@[simp] theorem cons_iff {a b : ℝ} {I : BasicInterval} {L : List BasicInterval} :
    GapChain a b (I :: L) ↔ I.left = a ∧ GapChain I.right b L := Iff.rfl

theorem singleton (I : BasicInterval) : GapChain I.left I.right [I] :=
  ⟨rfl, rfl⟩

@[simp] theorem singleton_iff {a b : ℝ} {I : BasicInterval} :
    GapChain a b [I] ↔ I.left = a ∧ I.right = b := Iff.rfl

theorem append {a b c : ℝ} {L M : List BasicInterval}
    (hL : GapChain a b L) (hM : GapChain b c M) : GapChain a c (L ++ M) := by
  induction L generalizing a with
  | nil =>
      change a = b at hL
      subst a
      exact hM
  | cons I L ih =>
      exact ⟨hL.1, ih hL.2⟩

theorem le_endpoints {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) : a ≤ b := by
  induction L generalizing a with
  | nil => exact le_of_eq h
  | cons I L ih =>
      calc
        a = I.left := h.1.symm
        _ ≤ I.right := I.left_lt_right.le
        _ ≤ b := ih h.2

theorem lt_endpoints_of_ne_nil {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) (hL : L ≠ []) : a < b := by
  cases L with
  | nil => exact False.elim (hL rfl)
  | cons I L =>
      calc
        a = I.left := h.1.symm
        _ < I.right := I.left_lt_right
        _ ≤ b := h.2.le_endpoints

theorem ne_nil_of_lt_endpoints {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) (hab : a < b) : L ≠ [] := by
  intro hL
  subst L
  exact (ne_of_lt hab) h

theorem left_le_of_mem {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) {I : BasicInterval} (hI : I ∈ L) : a ≤ I.left := by
  induction L generalizing a with
  | nil => exact False.elim (List.not_mem_nil hI)
  | cons J L ih =>
      rcases List.mem_cons.mp hI with rfl | hI
      · exact le_of_eq h.1.symm
      · calc
          a = J.left := h.1.symm
          _ ≤ J.right := J.left_lt_right.le
          _ ≤ I.left := ih h.2 hI

theorem right_le_of_mem {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) {I : BasicInterval} (hI : I ∈ L) : I.right ≤ b := by
  induction L generalizing a with
  | nil => exact False.elim (List.not_mem_nil hI)
  | cons J L ih =>
      rcases List.mem_cons.mp hI with rfl | hI
      · exact h.2.le_endpoints
      · exact ih h.2 hI

theorem carrier_subset {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) {I : BasicInterval} (hI : I ∈ L) :
    I.carrier ⊆ Set.Icc a b := by
  intro x hx
  exact ⟨(h.left_le_of_mem hI).trans hx.1, hx.2.trans (h.right_le_of_mem hI)⟩

/-- Cells later in the chain start no earlier than the current cell ends. -/
theorem pairwise {a b : ℝ} {L : List BasicInterval} (h : GapChain a b L) :
    L.Pairwise (fun I J => I.right ≤ J.left) := by
  induction L generalizing a with
  | nil => exact List.Pairwise.nil
  | cons I L ih =>
      apply List.pairwise_cons.mpr
      exact ⟨fun J hJ => h.2.left_le_of_mem hJ, ih h.2⟩

/-- A nonempty chain covers exactly its closed endpoint interval. -/
theorem mem_carrier_iff {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) (hL : L ≠ []) (x : ℝ) :
    (∃ I ∈ L, x ∈ I.carrier) ↔ a ≤ x ∧ x ≤ b := by
  constructor
  · rintro ⟨I, hI, hx⟩
    exact h.carrier_subset hI hx
  · intro hx
    induction L generalizing a with
    | nil => exact False.elim (hL rfl)
    | cons I L ih =>
        by_cases hxr : x ≤ I.right
        · refine ⟨I, List.mem_cons_self, ?_⟩
          exact ⟨by simpa only [h.1] using hx.1, hxr⟩
        · have htail : L ≠ [] := by
            intro he
            subst L
            have hr : I.right = b := h.2
            exact hxr (by simpa only [hr] using hx.2)
          obtain ⟨J, hJ, hxJ⟩ := ih h.2 htail ⟨(lt_of_not_ge hxr).le, hx.2⟩
          exact ⟨J, List.mem_cons_of_mem I hJ, hxJ⟩

end GapChain

/-- A nonempty ordered partition of an actual interval by basic dyadic cells. -/
structure DyadicGapPartition (a b : ℝ) where
  cells : List BasicInterval
  chain : GapChain a b cells
  nonempty : cells ≠ []

namespace DyadicGapPartition

theorem left_lt_right {a b : ℝ} (P : DyadicGapPartition a b) : a < b :=
  P.chain.lt_endpoints_of_ne_nil P.nonempty

theorem mem_covered_iff {a b : ℝ} (P : DyadicGapPartition a b) (x : ℝ) :
    (∃ I ∈ P.cells, x ∈ I.carrier) ↔ a ≤ x ∧ x ≤ b :=
  P.chain.mem_carrier_iff P.nonempty x

theorem cell_bounds {a b : ℝ} (P : DyadicGapPartition a b)
    {I : BasicInterval} (hI : I ∈ P.cells) : a ≤ I.left ∧ I.right ≤ b :=
  ⟨P.chain.left_le_of_mem hI, P.chain.right_le_of_mem hI⟩

end DyadicGapPartition

end

end ThompsonNonamenability

end OAI
