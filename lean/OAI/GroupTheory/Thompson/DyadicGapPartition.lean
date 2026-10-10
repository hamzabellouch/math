import OAI.GroupTheory.Thompson.DyadicArithmetic
import OAI.GroupTheory.Thompson.DyadicGapChain
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# Partitions of positive dyadic gaps

The initial partition consists of consecutive cells of a common dyadic grid.
Splitting one cell gives exactly one additional cell. Thus each pair of gaps
can be partitioned into the same number of cells independently.
-/

namespace ThompsonNonamenability

noncomputable section

/-- Consecutive cells with indices `A, ..., A+c-1` on grid level `n`. -/
def uniformGapCells (n A c : ℕ) (h : A + c ≤ 2 ^ n) : List BasicInterval :=
  match c with
  | 0 => []
  | c + 1 =>
      (⟨n, ⟨A, by omega⟩⟩ : BasicInterval) ::
        uniformGapCells n (A + 1) c (by omega)
termination_by c

@[simp] theorem uniformGapCells_length (n A c : ℕ) (h : A + c ≤ 2 ^ n) :
    (uniformGapCells n A c h).length = c := by
  induction c generalizing A with
  | zero => simp [uniformGapCells]
  | succ c ih => simp [uniformGapCells, ih]

theorem uniformGapCells_chain (n A c : ℕ) (h : A + c ≤ 2 ^ n) :
    GapChain ((A : ℝ) / (2 : ℝ) ^ n)
      (((A + c : ℕ) : ℝ) / (2 : ℝ) ^ n) (uniformGapCells n A c h) := by
  induction c generalizing A with
  | zero => simp [uniformGapCells]
  | succ c ih =>
      simp only [uniformGapCells]
      refine ⟨rfl, ?_⟩
      simpa [BasicInterval.right, Nat.cast_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ih (A + 1) (by omega)

/-- An actual basic-cell partition of any positive dyadic subinterval. -/
theorem exists_dyadicGapPartition {a b : ℝ}
    (ha : IsDyadic a) (hb : IsDyadic b)
    (h0 : 0 ≤ a) (hab : a < b) (h1 : b ≤ 1) :
    Nonempty (DyadicGapPartition a b) := by
  obtain ⟨ka, na, hka⟩ := ha
  obtain ⟨kb, nb, hkb⟩ := hb
  obtain ⟨ka', hka'⟩ := dyadic_raise_denominator ⟨ka, hka⟩ nb
  obtain ⟨kb', hkb'⟩ := dyadic_raise_denominator ⟨kb, hkb⟩ na
  have hkb'' : b = (kb' : ℝ) / (2 : ℝ) ^ (na + nb) := by
    simpa only [Nat.add_comm nb na] using hkb'
  obtain ⟨A, hAmax, hA⟩ := dyadic_nat_numerator hka' h0 (hab.le.trans h1)
  obtain ⟨B, hBmax, hB⟩ := dyadic_nat_numerator hkb'' (h0.trans hab.le) h1
  have hABr : (A : ℝ) < (B : ℝ) := by
    apply (div_lt_div_iff_of_pos_right (pow_pos (by norm_num : (0 : ℝ) < 2)
      (na + nb))).1
    rw [← hA, ← hB]
    exact hab
  have hAB : A < B := by exact_mod_cast hABr
  have hsum : A + (B - A) = B := by omega
  let cells := uniformGapCells (na + nb) A (B - A) (by omega)
  have hc : GapChain a b cells := by
    simpa only [cells, hsum, ← hA, ← hB] using
      uniformGapCells_chain (na + nb) A (B - A) (by omega)
  refine ⟨⟨cells, hc, ?_⟩⟩
  intro he
  have hlen := congrArg List.length he
  simp only [cells, uniformGapCells_length, List.length_nil] at hlen
  omega

namespace BasicInterval

/-- The left half of an actual basic interval. -/
def splitLeft (I : BasicInterval) : BasicInterval :=
  I.comp ⟨1, ⟨0, by decide⟩⟩

/-- The right half of an actual basic interval. -/
def splitRight (I : BasicInterval) : BasicInterval :=
  I.comp ⟨1, ⟨1, by decide⟩⟩

@[simp] theorem splitLeft_left (I : BasicInterval) : I.splitLeft.left = I.left := by
  rw [splitLeft, left_comp]
  have h : (⟨1, ⟨0, by decide⟩⟩ : BasicInterval).left = 0 := by
    norm_num [left]
  rw [h, chart_zero]

@[simp] theorem splitRight_right (I : BasicInterval) : I.splitRight.right = I.right := by
  rw [splitRight, right_comp]
  have h : (⟨1, ⟨1, by decide⟩⟩ : BasicInterval).right = 1 := by
    norm_num [right]
  rw [h, chart_one]

theorem split_adjacent (I : BasicInterval) : I.splitLeft.right = I.splitRight.left := by
  rw [splitLeft, splitRight, right_comp, left_comp]
  congr 1
  norm_num [right, left]

theorem splitLeft_contained (I : BasicInterval) : I.splitLeft.Contained I :=
  I.comp_contained _

theorem splitRight_contained (I : BasicInterval) : I.splitRight.Contained I :=
  I.comp_contained _

end BasicInterval

/-- Every cell in the refined list lies in an original cell. -/
def GapRefines (newCells oldCells : List BasicInterval) : Prop :=
  ∀ J ∈ newCells, ∃ I ∈ oldCells, J.Contained I

namespace GapRefines

theorem refl (L : List BasicInterval) : GapRefines L L := by
  intro I hI
  exact ⟨I, hI, I.contained_refl⟩

theorem trans {L M N : List BasicInterval} (hLM : GapRefines L M)
    (hMN : GapRefines M N) : GapRefines L N := by
  intro I hI
  obtain ⟨J, hJ, hIJ⟩ := hLM I hI
  obtain ⟨K, hK, hJK⟩ := hMN J hJ
  exact ⟨K, hK, hIJ.trans hJK⟩

end GapRefines

namespace GapChain

theorem split_head {a b : ℝ} {I : BasicInterval} {L : List BasicInterval}
    (h : GapChain a b (I :: L)) :
    GapChain a b (I.splitLeft :: I.splitRight :: L) := by
  rcases h with ⟨hleft, htail⟩
  refine ⟨I.splitLeft_left.trans hleft, I.split_adjacent.symm, ?_⟩
  simpa only [BasicInterval.splitRight_right] using htail

theorem split_head_refines (I : BasicInterval) (L : List BasicInterval) :
    GapRefines (I.splitLeft :: I.splitRight :: L) (I :: L) := by
  intro J hJ
  simp only [List.mem_cons] at hJ
  rcases hJ with rfl | rfl | hJ
  · exact ⟨I, List.mem_cons_self, I.splitLeft_contained⟩
  · exact ⟨I, List.mem_cons_self, I.splitRight_contained⟩
  · exact ⟨J, List.mem_cons_of_mem I hJ, J.contained_refl⟩

/-- Bisection increases a nonempty chain's cardinality by exactly one. -/
theorem exists_succ_length {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) (hne : L ≠ []) :
    ∃ M : List BasicInterval, GapChain a b M ∧
      M.length = L.length + 1 ∧ GapRefines M L := by
  cases L with
  | nil => exact False.elim (hne rfl)
  | cons I L =>
      exact ⟨I.splitLeft :: I.splitRight :: L, h.split_head,
        by simp [Nat.add_comm, Nat.add_left_comm], split_head_refines I L⟩

/-- Any prescribed nonnegative number of extra cells can be obtained by bisection. -/
theorem exists_length_add {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) (hne : L ≠ []) (k : ℕ) :
    ∃ M : List BasicInterval, GapChain a b M ∧
      M.length = L.length + k ∧ GapRefines M L := by
  induction k with
  | zero => exact ⟨L, h, by simp, GapRefines.refl L⟩
  | succ k ih =>
      obtain ⟨M, hM, hlen, href⟩ := ih
      have hMne : M ≠ [] := by
        intro hempty
        have hL : L.length = 0 := by simp only [hempty, List.length_nil] at hlen; omega
        exact hne (List.length_eq_zero_iff.mp hL)
      obtain ⟨N, hN, hNlen, hNref⟩ := hM.exists_succ_length hMne
      refine ⟨N, hN, ?_, hNref.trans href⟩
      omega

theorem exists_length_ge {a b : ℝ} {L : List BasicInterval}
    (h : GapChain a b L) (hne : L ≠ []) {n : ℕ} (hn : L.length ≤ n) :
    ∃ M : List BasicInterval, GapChain a b M ∧ M.length = n ∧ GapRefines M L := by
  obtain ⟨M, hM, hlen, href⟩ := h.exists_length_add hne (n - L.length)
  exact ⟨M, hM, by omega, href⟩

end GapChain

namespace DyadicGapPartition

theorem exists_refinement_card {a b : ℝ} (P : DyadicGapPartition a b)
    {n : ℕ} (hn : P.cells.length ≤ n) :
    ∃ Q : DyadicGapPartition a b, Q.cells.length = n ∧ GapRefines Q.cells P.cells := by
  obtain ⟨M, hM, hlen, href⟩ := P.chain.exists_length_ge P.nonempty hn
  have hMne : M ≠ [] := by
    intro hempty
    have hnzero : n = 0 := by simpa only [hempty, List.length_nil] using hlen.symm
    have hpzero : P.cells.length = 0 := by omega
    exact P.nonempty (List.length_eq_zero_iff.mp hpzero)
  exact ⟨⟨M, hM, hMne⟩, hlen, href⟩

/-- Equalization is performed for this pair of gaps, with both refinements retained. -/
theorem equalize {a b c d : ℝ} (P : DyadicGapPartition a b) (Q : DyadicGapPartition c d) :
    ∃ (P' : DyadicGapPartition a b) (Q' : DyadicGapPartition c d),
      P'.cells.length = Q'.cells.length ∧
      GapRefines P'.cells P.cells ∧ GapRefines Q'.cells Q.cells := by
  obtain ⟨P', hP', hrefP⟩ := P.exists_refinement_card (Nat.le_max_left P.cells.length Q.cells.length)
  obtain ⟨Q', hQ', hrefQ⟩ := Q.exists_refinement_card (Nat.le_max_right P.cells.length Q.cells.length)
  exact ⟨P', Q', hP'.trans hQ'.symm, hrefP, hrefQ⟩

end DyadicGapPartition

/-- Any two positive dyadic gaps admit ordered basic-cell chains of equal length. -/
theorem equalize_dyadic_gaps {a b c d : ℝ}
    (ha : IsDyadic a) (hb : IsDyadic b) (h0 : 0 ≤ a) (hab : a < b) (h1 : b ≤ 1)
    (hc : IsDyadic c) (hd : IsDyadic d) (h0' : 0 ≤ c) (hcd : c < d) (h1' : d ≤ 1) :
    ∃ A B : List BasicInterval, GapChain a b A ∧ GapChain c d B ∧
      A ≠ [] ∧ B ≠ [] ∧ A.length = B.length := by
  obtain ⟨P⟩ := exists_dyadicGapPartition ha hb h0 hab h1
  obtain ⟨Q⟩ := exists_dyadicGapPartition hc hd h0' hcd h1'
  obtain ⟨P', Q', hlen, _, _⟩ := P.equalize Q
  exact ⟨P'.cells, Q'.cells, P'.chain, Q'.chain, P'.nonempty, Q'.nonempty, hlen⟩

theorem exists_equal_length_partitions {a b c d : ℝ}
    (ha : IsDyadic a) (hb : IsDyadic b) (hc : IsDyadic c) (hd : IsDyadic d)
    (ha0 : 0 ≤ a) (hb1 : b ≤ 1) (hc0 : 0 ≤ c) (hd1 : d ≤ 1)
    (hab : a < b) (hcd : c < d) :
    ∃ P : DyadicGapPartition a b, ∃ Q : DyadicGapPartition c d,
      P.cells.length = Q.cells.length := by
  obtain ⟨P⟩ := exists_dyadicGapPartition ha hb ha0 hab hb1
  obtain ⟨Q⟩ := exists_dyadicGapPartition hc hd hc0 hcd hd1
  obtain ⟨P', Q', hlen, _, _⟩ := P.equalize Q
  exact ⟨P', Q', hlen⟩

end

end ThompsonNonamenability

end OAI
