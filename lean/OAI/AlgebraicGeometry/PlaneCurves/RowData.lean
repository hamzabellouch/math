import Mathlib.Algebra.Group.End
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Interval.Finset.Fin
import OAI.AlgebraicGeometry.PlaneCurves.ExponentSets

namespace OAI

noncomputable section

/-!
# Sorted finite row data, column fibres, and cardinality bounds
-/

/-!
# Sorting tuples by their values

## Main declarations

* `Tuple.sort`: given `f : Fin n → α`, produces a permutation on `Fin n`
* `Tuple.monotone_sort`: `f ∘ Tuple.sort f` is `Monotone`
-/

namespace Nagata.Workers.W10.LocalTupleSort

variable {n : ℕ}
variable {α : Type*} [LinearOrder α]

/-- `graph f` produces the finset of pairs `(f i, i)`
equipped with the lexicographic order.
-/
def graph (f : Fin n → α) : Finset (α ×ₗ Fin n) :=
  Finset.univ.image fun i => (f i, i)

/-- Given `p : α ×ₗ (Fin n) := (f i, i)` with `p ∈ graph f`,
`graph.proj p` is defined to be `f i`.
-/
def graph.proj {f : Fin n → α} : graph f → α := fun p => p.1.1
@[simp]
theorem graph.card (f : Fin n → α) : (graph f).card = n := by
  erw [graph, Finset.card_image_of_injective]
  · exact Finset.card_fin _
  · intro i j hij
    exact congrArg (fun p : α ×ₗ Fin n => p.2) hij

/-- `graphEquiv₁ f` is the natural equivalence between `Fin n` and `graph f`,
mapping `i` to `(f i, i)`. -/
def graphEquiv₁ (f : Fin n → α) : Fin n ≃ graph f where
  toFun i := ⟨(f i, i), Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  invFun p := p.1.2
  left_inv i := by simp
  right_inv entry := by
    apply Subtype.ext
    obtain ⟨index, _, hindex⟩ := Finset.mem_image.mp entry.property
    change (f entry.val.2, entry.val.2) = entry.val
    rw [← hindex]

@[simp]
theorem proj_equiv₁' (f : Fin n → α) : graph.proj ∘ graphEquiv₁ f = f :=
  rfl

/-- `graphEquiv₂ f` is an equivalence between `Fin n` and `graph f` that respects the order.
-/
def graphEquiv₂ (f : Fin n → α) : Fin n ≃o graph f :=
  Finset.orderIsoOfFin _ (by simp)

/-- `sort f` is the permutation that orders `Fin n` according to the order of the outputs of `f`. -/
def sort (f : Fin n → α) : Equiv.Perm (Fin n) :=
  (graphEquiv₂ f).toEquiv.trans (graphEquiv₁ f).symm

theorem graphEquiv₂_apply (f : Fin n → α) (i : Fin n) :
    graphEquiv₂ f i = graphEquiv₁ f (sort f i) :=
  ((graphEquiv₁ f).apply_symm_apply _).symm

theorem self_comp_sort (f : Fin n → α) : f ∘ sort f = graph.proj ∘ graphEquiv₂ f :=
  show graph.proj ∘ (graphEquiv₁ f ∘ (graphEquiv₁ f).symm) ∘ (graphEquiv₂ f).toEquiv = _ by simp

theorem monotone_proj (f : Fin n → α) : Monotone (graph.proj : graph f → α) := by
  rintro ⟨⟨x, i⟩, hx⟩ ⟨⟨y, j⟩, hy⟩ (_ | h)
  · exact le_of_lt ‹_›
  · simp [graph.proj]

theorem monotone_sort (f : Fin n → α) : Monotone (f ∘ sort f) := by
  rw [self_comp_sort]
  exact (monotone_proj f).comp (graphEquiv₂ f).monotone

end Nagata.Workers.W10.LocalTupleSort

/-!
# Ordered row bounds
-/

namespace Nagata.Workers.W10

section

/-- Every earlier row contributes to the distribution count at the current size. -/
theorem initial_rows_le_distribution (N : ℕ → ℕ) (s i : ℕ) (hi : i < s)
    (horder : ∀ j, j ≤ i → N i ≤ N j) :
    i + 1 ≤ ((Finset.range s).filter fun j => N i ≤ N j).card := by
  calc
    i + 1 = (Finset.range (i + 1)).card := (Finset.card_range _).symm
    _ ≤ ((Finset.range s).filter fun j => N i ≤ N j).card := by
      apply Finset.card_le_card
      intro j hj
      have hji : j ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (lt_of_le_of_lt hji hi), horder j hji⟩

/-- The distribution bounds imply the manuscript's ordered row bound. -/
theorem ordered_row_bound (N : ℕ → ℕ) (s q m : ℕ)
    (horder : ∀ i < s, ∀ j ≤ i, N i ≤ N j)
    (hpos : ∀ i < s, 1 ≤ N i)
    (hsize : ∀ i < s, N i ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      ((Finset.range s).filter fun j => t ≤ N j).card ≤ q * (m - t + 1))
    (i : ℕ) (hi : i < s) : i + 1 ≤ q * (m - N i + 1) :=
  (initial_rows_le_distribution N s i hi (horder i hi)).trans
    (hdistribution (N i) (hpos i hi) (hsize i hi))

/-- The ordered row bound puts every correction monomial inside the allowed region. -/
theorem correction_exponent_bound (q m n i b ell : ℕ)
    (hsize : n ≤ m) (horder : i + 1 ≤ q * (m - n + 1))
    (hb : b < n) (hell : ell ≤ i) : b < m ∧ ell < q * (m - b) := by
  constructor
  · exact lt_of_lt_of_le hb hsize
  · have hsub : m - n + 1 ≤ m - b := by omega
    have hmul := Nat.mul_le_mul_left q hsub
    exact lt_of_le_of_lt hell (lt_of_lt_of_le (Nat.lt_of_succ_le horder) hmul)

/-- Combined form, ready for use by the row-by-row interpolation construction. -/
theorem distributed_correction_exponent_bound (N : ℕ → ℕ) (s q m : ℕ)
    (horder : ∀ i < s, ∀ j ≤ i, N i ≤ N j)
    (hpos : ∀ i < s, 1 ≤ N i)
    (hsize : ∀ i < s, N i ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      ((Finset.range s).filter fun j => t ≤ N j).card ≤ q * (m - t + 1))
    (i b ell : ℕ) (hi : i < s) (hb : b < N i) (hell : ell ≤ i) :
    b < m ∧ ell < q * (m - b) :=
  correction_exponent_bound q m (N i) i b ell (hsize i hi)
    (ordered_row_bound N s q m horder hpos hsize hdistribution i hi) hb hell

/-! Finite-index cardinality bounds and permutation invariance for manuscript Section 4. -/

/-- Reordering the complete row set preserves every distribution count. -/
theorem distribution_card_permutation {s : ℕ} (N : Fin s → ℕ)
    (σ : Equiv.Perm (Fin s)) (t : ℕ) :
    (Finset.univ.filter fun i => t ≤ N (σ i)).card =
      (Finset.univ.filter fun i => t ≤ N i).card := by
  apply Finset.card_equiv σ
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The zero-based ordered row inequality on a finite index type. -/
theorem fin_ordered_row_bound {s : ℕ} (N : Fin s → ℕ) (q m : ℕ)
    (horder : Antitone N) (hpos : ∀ i, 1 ≤ N i) (hsize : ∀ i, N i ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      (Finset.univ.filter fun j => t ≤ N j).card ≤ q * (m - t + 1))
    (i : Fin s) : i.val + 1 ≤ q * (m - N i + 1) := by
  have hindex : i.val + 1 ≤ (Finset.univ.filter fun j => N i ≤ N j).card := by
    calc
      i.val + 1 = (Finset.Iic i).card := (Fin.card_Iic i).symm
      _ ≤ (Finset.univ.filter fun j => N i ≤ N j).card := by
        apply Finset.card_le_card
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, horder (Finset.mem_Iic.mp hj)⟩
  exact hindex.trans (hdistribution (N i) (hpos i) (hsize i))

/-! The literal three-branch exponent set is exactly the disjoint union of its
coefficient fibers, retaining the degree-zero column. -/
open Nagata.FiniteExponents

def ColumnFiber (d m : ℤ) (a Δ : ℝ) (j : ℤ) :=
  {K : ℤ // (j, K) ∈ exponentSet d m a Δ}

instance columnFiberDecidableEq (d m : ℤ) (a Δ : ℝ) (j : ℤ) :
    DecidableEq (ColumnFiber d m a Δ j) := by
  unfold ColumnFiber
  infer_instance

instance columnFiberFintype (d m : ℤ) (a Δ : ℝ) (j : ℤ) :
    Fintype (ColumnFiber d m a Δ j) := by
  classical
  apply Fintype.ofInjective
    (fun K : ColumnFiber d m a Δ j => (⟨(j, K.val), K.property⟩ : Column d m a Δ))
  intro K L h
  apply Subtype.ext
  exact congrArg (fun c : Column d m a Δ => c.val.2) h

theorem column_first_bounds {d m : ℤ} {a Δ : ℝ} (hm : 0 ≤ m) (hd : 3 * m < d)
    (c : Column d m a Δ) : 0 ≤ c.val.1 ∧ c.val.1 ≤ d / 3 := by
  have hmd : m ≤ d / 3 :=
    (Int.le_ediv_iff_mul_le (show (0 : ℤ) < 3 by decide)).mpr (by omega)
  rcases mem_exponentSet_iff.mp c.property with h | h | h
  · exact ⟨h.1, h.2.1.trans hmd⟩
  · exact ⟨hm.trans h.1.le, h.2.1⟩
  · exact ⟨hm.trans h.1.le, h.2.1⟩

/-- The finite coefficient-index family is equivalent to the exact literal columns. -/
def columnFiberEquiv (d m : ℤ) (a Δ : ℝ) (hm : 0 ≤ m) (hd : 3 * m < d) :
    (Σ j : Fin ((d / 3).toNat + 1), ColumnFiber d m a Δ (j.val : ℤ)) ≃
      Column d m a Δ where
  toFun c := ⟨(c.1.val, c.2.val), c.2.property⟩
  invFun c :=
    ⟨⟨c.val.1.toNat, by
        have hb := column_first_bounds hm hd c
        have hnat := Int.toNat_le_toNat hb.2
        omega⟩,
      ⟨c.val.2, by
        have hb := column_first_bounds hm hd c
        simpa only [Int.toNat_of_nonneg hb.1] using c.property⟩⟩
  left_inv c := by
    rcases c with ⟨⟨j, hj⟩, ⟨K, hK⟩⟩
    rfl
  right_inv c := by
    apply Subtype.ext
    have hb := column_first_bounds hm hd c
    simp only [Int.toNat_of_nonneg hb.1, Prod.eta]

/-- A degree-zero fiber contains exactly the retained K=0 column. -/
def zeroColumnFiberEquiv (d m j : ℤ) (a Δ : ℝ) (hj : m < j) (hz : d - 3 * j = 0) :
    ColumnFiber d m a Δ j ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := ⟨0, degree_zero_mem hj hz⟩
  left_inv K := by
    apply Subtype.ext
    rcases mem_exponentSet_iff.mp K.property with h | h | h
    · omega
    · omega
    · exact h.2.2.2.symm
  right_inv _ := rfl

/-- The first coefficient fiber has exactly the source's theta residue indices. -/
def firstColumnFiberEquiv (d m j : ℤ) (a Δ : ℝ) (hj0 : 0 ≤ j) (hjm : j ≤ m)
    (hU : firstLower d m j a Δ ∉ Set.range (Int.cast : ℤ → ℝ)) :
    ColumnFiber d m a Δ j ≃ Nagata.W09.thetaIndices (firstLower d m j a Δ) (commonDegree d m) := by
  apply Equiv.subtypeEquivRight
  intro K
  rw [mem_exponentSet_iff, Nagata.W09.mem_thetaIndices_iff hU]
  constructor
  · rintro (h | h | h)
    · exact h.2.2
    · omega
    · omega
  · intro h
    exact Or.inl ⟨hj0, hjm, h⟩

/-- The positive high coefficient fiber has exactly its source theta indices. -/
def positiveColumnFiberEquiv (d m j : ℤ) (a Δ : ℝ) (hmj : m < j)
    (hjd : j ≤ d / 3) (hn : 0 < d - 3 * j)
    (hU : secondLower d j a Δ ∉ Set.range (Int.cast : ℤ → ℝ)) :
    ColumnFiber d m a Δ j ≃ Nagata.W09.thetaIndices (secondLower d j a Δ) (sourceDegree d j) := by
  apply Equiv.subtypeEquivRight
  intro K
  rw [mem_exponentSet_iff, Nagata.W09.mem_thetaIndices_iff hU]
  constructor
  · rintro (h | h | h)
    · omega
    · exact h.2.2.2
    · omega
  · intro h
    exact Or.inr (Or.inl ⟨hmj, hjd, hn, h⟩)

end

/-! Genuine finite Cartesian-product rows; specializes definitionally to plane rows. -/
section
variable {α β : Type*}

/-- The represented heights of a genuine finite plane set. -/
def rowHeights (S : Finset (α × β)) : Finset β := by
  classical
  exact S.image Prod.snd

/-- The first coordinates of a represented horizontal row. -/
def rowXs (S : Finset (α × β)) (K : β) : Finset α := by
  classical
  exact (S.filter fun p => p.2 = K).image Prod.fst

theorem mem_rowXs {S : Finset (α × β)} {x : α} {K : β} :
    x ∈ rowXs S K ↔ (x, K) ∈ S := by
  classical
  constructor
  · intro hx
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    obtain ⟨hp, hpk⟩ := Finset.mem_filter.mp hp
    have heq : p = (x, K) := Prod.ext hpx hpk
    simpa only [heq] using hp
  · intro hp
    exact Finset.mem_image.mpr
      ⟨(x, K), Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩

theorem rowXs_nonempty {S : Finset (α × β)} {K : β} (hK : K ∈ rowHeights S) :
    (rowXs S K).Nonempty := by
  classical
  obtain ⟨p, hp, hpk⟩ := Finset.mem_image.mp hK
  refine ⟨p.1, mem_rowXs.mpr ?_⟩
  simpa only [← hpk, Prod.eta] using hp

theorem snd_mem_rowHeights {S : Finset (α × β)} {p : α × β} (hp : p ∈ S) :
    p.2 ∈ rowHeights S := by
  classical
  exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

/-- A finite enumeration of actual represented heights preserves the row counts. -/
theorem row_distribution_card (S : Finset (α × β))
    (e : Fin (rowHeights S).card ≃ rowHeights S) (t : ℕ) :
    (Finset.univ.filter fun i => t ≤ (rowXs S (e i).val).card).card =
      ((rowHeights S).filter fun K => t ≤ (rowXs S K).card).card := by
  classical
  apply Finset.card_bij (fun i _ => (e i).val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨(e i).property, (Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj heq
    exact e.injective (Subtype.ext heq)
  · intro K hK
    let k : rowHeights S := ⟨K, (Finset.mem_filter.mp hK).1⟩
    refine ⟨e.symm k, ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.apply_symm_apply] using (Finset.mem_filter.mp hK).2
    · exact congrArg Subtype.val (e.apply_symm_apply k)

end

/-!
# Sorting finite rows
-/

/-- Sort row sizes in nonincreasing order, with no restriction on ties. -/
def descendingRowPermutation {s : ℕ} (N : Fin s → ℕ) : Equiv.Perm (Fin s) :=
  LocalTupleSort.sort (α := OrderDual ℕ) (fun i => N i)

theorem descendingRowPermutation_antitone {s : ℕ} (N : Fin s → ℕ) :
    Antitone (N ∘ descendingRowPermutation N) :=
  LocalTupleSort.monotone_sort (α := OrderDual ℕ) (fun i => N i)

/-- Every finite row family satisfying the distribution hypotheses admits an
ordering satisfying the precise inequality needed by constructive interpolation. -/
theorem exists_ordered_rows {s : ℕ} (N : Fin s → ℕ) (q m : ℕ)
    (hpos : ∀ i, 1 ≤ N i) (hsize : ∀ i, N i ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      (Finset.univ.filter fun j => t ≤ N j).card ≤ q * (m - t + 1)) :
    ∃ σ : Equiv.Perm (Fin s), Antitone (N ∘ σ) ∧
      ∀ i : Fin s, i.val + 1 ≤ q * (m - N (σ i) + 1) := by
  let σ := descendingRowPermutation N
  refine ⟨σ, descendingRowPermutation_antitone N, ?_⟩
  intro i
  apply fin_ordered_row_bound (N ∘ σ) q m (descendingRowPermutation_antitone N)
    (fun j => hpos (σ j)) (fun j => hsize (σ j))
  intro t ht htm
  change (Finset.univ.filter fun j => t ≤ N (σ j)).card ≤ q * (m - t + 1)
  rw [distribution_card_permutation N σ t]
  exact hdistribution t ht htm

end Nagata.Workers.W10

end

end OAI
