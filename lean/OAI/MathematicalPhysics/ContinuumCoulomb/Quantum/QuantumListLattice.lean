import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListMergeMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListMergeProperties
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLatticePromise

namespace OAI

/-! The actual computed coordinate and bond tapes define a valid lattice
source. Canonical merging preserves its full matrix and scalar threshold shift. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListLattice
open MediatorListProgram
open QuantumListMerge

def Adjacent (ps : List Pair) (xs : List Bond) (hb : SourceBondLists.bounded ps.length xs) : Prop :=
  ∀ e (he : e ∈ xs), qmaSquareGrid.Adj
    (ps.get ⟨e.1,(hb e he).1⟩) (ps.get ⟨e.2.1,(hb e he).2⟩)

theorem merge_adjacent (ps : List Pair) (xs : List Bond)
    (hb : SourceBondLists.bounded ps.length xs) (ha : Adjacent ps xs hb)
    (e : Bond) (he : e ∈ value ps.length xs) :
    qmaSquareGrid.Adj
      (ps.get ⟨e.1,(bounded ps.length xs e he).1⟩)
      (ps.get ⟨e.2.1,(bounded ps.length xs e he).2⟩) := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
  obtain ⟨b,hb',hbp⟩ := List.mem_map.mp ((mem_support hb p).mp hp)
  subst p
  by_cases h : b.1 ≤ b.2.1
  · simpa only [ordered,min_eq_left h,max_eq_right h] using ha b hb'
  · have h' : b.2.1 ≤ b.1 := by omega
    simpa only [ordered,min_eq_right h',max_eq_left h'] using (ha b hb').symm

def source (ps : List Pair) (xs : List Bond) (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b) : SquareLatticeHeisenberg where
  vertices := ps.length
  vertices_pos := hp
  coordinate i := qmaGridCoordinate (ps.get i)
  coordinate_injective := qmaGridCoordinate_injective.comp hn.injective_get
  edges := (value ps.length xs).length
  left i := ⟨((value ps.length xs).get i).1,
    (bounded ps.length xs _ (List.get_mem _ i)).1⟩
  right i := ⟨((value ps.length xs).get i).2.1,
    (bounded ps.length xs _ (List.get_mem _ i)).2⟩
  coefficient i := ((value ps.length xs).get i).2.2
  adjacent i := qmaGridCoordinate_adj (merge_adjacent ps xs hb ha _ (List.get_mem _ i))
  edge_simple i j hij := by
    have h := value_simple hl i j hij
    constructor
    · rintro ⟨h1,h2⟩
      exact h.1 ⟨congrArg Fin.val h1,congrArg Fin.val h2⟩
    · rintro ⟨h1,h2⟩
      exact h.2 ⟨congrArg Fin.val h1,congrArg Fin.val h2⟩
  lower := a-c
  upper := b-c
  gap_pos := sub_lt_sub_right hab c

theorem source_matrix (ps : List Pair) (xs : List Bond) (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b) :
    (source ps xs hp hn hb hl ha a b c hab).bonds.matrix = SourceBondLists.matrix ps.length xs :=
  (SourceBondLists.matrix_bonds ps.length (value ps.length xs) (bounded ps.length xs)).symm.trans
    (matrix_eq ps.length xs hb)

theorem source_energy (ps : List Pair) (xs : List Bond) (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b) :
    realSourceGroundEnergy (source ps xs hp hn hb hl ha a b c hab) =
      sourceMatrixBottom ps.length (SourceBondLists.matrix ps.length xs) := by
  rw [← sourceMatrixBottom_eq_realSource,source_matrix]
  rfl

theorem source_energy_shift (ps : List Pair) (xs : List Bond)
    (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b) :
    realSourceGroundEnergy (source ps xs hp hn hb hl ha a b c hab) =
      sourceMatrixBottom ps.length
        (SourceBondLists.matrix ps.length xs+(c:ℂ) • 1)-(c:ℝ) := by
  rw [source_energy]
  simpa only [Complex.ofReal_ratCast,add_sub_cancel_right] using
    sourceMatrixBottom_shift ps.length
      (SourceBondLists.matrix ps.length xs+(c:ℂ) • 1) (c:ℝ)

theorem source_yes (ps : List Pair) (xs : List Bond)
    (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b)
    (he : sourceMatrixBottom ps.length
      (SourceBondLists.matrix ps.length xs+(c:ℂ) • 1) ≤ (a:ℝ)) :
    realSourceGroundEnergy (source ps xs hp hn hb hl ha a b c hab) ≤
      ((source ps xs hp hn hb hl ha a b c hab).lower:ℝ) := by
  rw [source_energy_shift]
  change _ ≤ ((a-c:ℚ):ℝ)
  simpa only [Rat.cast_sub] using sub_le_sub_right he (c:ℝ)

theorem source_no (ps : List Pair) (xs : List Bond)
    (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b)
    (he : (b:ℝ) ≤ sourceMatrixBottom ps.length
      (SourceBondLists.matrix ps.length xs+(c:ℂ) • 1)) :
    ((source ps xs hp hn hb hl ha a b c hab).upper:ℝ) ≤
      realSourceGroundEnergy (source ps xs hp hn hb hl ha a b c hab) := by
  rw [source_energy_shift]
  change ((b-c:ℚ):ℝ) ≤ _
  simpa only [Rat.cast_sub] using sub_le_sub_right he (c:ℝ)

theorem source_polynomialPromise (ps : List Pair) (xs : List Bond)
    (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b) (n k : ℕ) (hsize : n ≤ ps.length)
    (hpos : ∀ p ∈ ps, (p.1:ℝ) ≤ (n+1:ℝ)^k ∧ (p.2:ℝ) ≤ (n+1:ℝ)^k)
    {L : ℝ} (hL : 0 ≤ L) (hJ : ∀ e ∈ xs, |(e.2.2:ℝ)| ≤ L)
    (hcoeff : xs.length*L ≤ (n+1:ℝ)^k)
    (hgap : ((n+1:ℝ)^k)⁻¹ ≤ (b:ℝ)-a) :
    (source ps xs hp hn hb hl ha a b c hab).binary.PolynomialPromise k := by
  apply SquareLatticeHeisenberg.binary_polynomialPromise _ n k hsize
  · intro i
    let j : Fin ps.length := ⟨i.val,i.isLt⟩
    change |(((ps.get j).1:ℤ):ℝ)| ≤ _ ∧ |(((ps.get j).2:ℤ):ℝ)| ≤ _
    have hi := hpos _ (List.get_mem ps j)
    push_cast
    rw [abs_of_nonneg (Nat.cast_nonneg _ : (0:ℝ) ≤ ((ps.get j).1:ℝ)),
      abs_of_nonneg (Nat.cast_nonneg _ : (0:ℝ) ≤ ((ps.get j).2:ℝ))]
    exact hi
  · intro i
    let j : Fin (value ps.length xs).length := ⟨i.val,i.isLt⟩
    change |(((value ps.length xs).get j).2.2:ℝ)| ≤ _
    have he := congrArg (fun e : Bond => |(e.2.2:ℝ)|) (value_get ps.length xs j)
    exact he.le.trans ((weight_abs_le xs _ hL hJ).trans hcoeff)
  · change ((n+1:ℝ)^k)⁻¹ ≤ ((b-c:ℚ):ℝ)-((a-c:ℚ):ℝ)
    push_cast
    linarith

end ContinuumCoulomb.QuantumListLattice

end

end OAI
