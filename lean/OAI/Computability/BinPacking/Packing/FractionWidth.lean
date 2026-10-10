import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OAI.Computability.BinPacking.Model

namespace OAI

namespace BinPackingGap

open scoped BigOperators

namespace Instance

noncomputable def ofFintype {ι : Type*} [Fintype ι]
    (s : ι → ℚ) (hpos : ∀ i, 0 < s i) (hle : ∀ i, s i ≤ 1) : Instance where
  n := Fintype.card ι
  size i := s ((Fintype.equivFin ι).symm i)
  size_pos _ := hpos _
  size_le_one _ := hle _

end Instance

namespace Packing

variable {I : Instance} {b : ℕ}

def binItems (p : Packing I b) (j : Fin b) : Finset I.Item :=
  Finset.univ.filter fun i => p.assignment i = j

@[simp] theorem mem_binItems (p : Packing I b) (j : Fin b) (i : I.Item) :
    i ∈ p.binItems j ↔ p.assignment i = j := by
  simp [binItems]

theorem bin_capacity (p : Packing I b) (j : Fin b) :
    ∑ i ∈ p.binItems j, I.size i ≤ 1 := by
  simpa [binItems, Finset.sum_filter] using p.capacity j

theorem binItems_disjoint (p : Packing I b) {j k : Fin b} (h : j ≠ k) :
    Disjoint (p.binItems j) (p.binItems k) := by
  refine Finset.disjoint_left.mpr ?_
  intro i hi hj
  have hji := (p.mem_binItems j i).mp hi
  have hki := (p.mem_binItems k i).mp hj
  exact h (hji.symm.trans hki)

theorem mem_own_bin (p : Packing I b) (i : I.Item) :
    i ∈ p.binItems (p.assignment i) := by simp

theorem unique_bin (p : Packing I b) (i : I.Item) :
    ∃! j, i ∈ p.binItems j := by
  refine ⟨p.assignment i, p.mem_own_bin i, ?_⟩
  intro j hj
  exact ((p.mem_binItems j i).mp hj).symm

theorem chosen_injective (p : Packing I b) {J : Type*}
    (bin : J → Fin b) (hbin : Function.Injective bin)
    (chosen : J → I.Item) (hchosen : ∀ j, chosen j ∈ p.binItems (bin j)) :
    Function.Injective chosen := by
  intro j k hjk
  apply hbin
  have hj := (p.mem_binItems (bin j) (chosen j)).mp (hchosen j)
  have hk := (p.mem_binItems (bin k) (chosen k)).mp (hchosen k)
  rw [hjk] at hj
  exact hj.symm.trans hk

theorem sum_bins (p : Packing I b) {M : Type*} [AddCommMonoid M]
    (f : I.Item → M) :
    ∑ j, ∑ i ∈ p.binItems j, f i = ∑ i, f i := by
  simp only [binItems, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ j, if p.assignment i = j then f i else 0) =
        (if p.assignment i = p.assignment i then f i else 0) :=
      Finset.sum_eq_single (p.assignment i)
        (fun j _ hj => ite_eq_right (Ne.symm hj))
        (fun h => False.elim (h (Finset.mem_univ _)))
    _ = f i := ite_eq_left rfl

theorem sum_bin_card (p : Packing I b) :
    ∑ j, (p.binItems j).card = I.n := by
  simpa using p.sum_bins (fun _ => (1 : ℕ))

def enlarge (p : Packing I b) {c : ℕ} (hbc : b ≤ c) : Packing I c where
  assignment i := Fin.castLE hbc (p.assignment i)
  capacity j := by
    by_cases hj : j.val < b
    · let k : Fin b := ⟨j.val, hj⟩
      have heq : ∀ i, Fin.castLE hbc (p.assignment i) = j ↔ p.assignment i = k := by
        intro i
        simp [Fin.ext_iff, k]
      simpa only [heq] using p.capacity k
    · have heq : ∀ i, Fin.castLE hbc (p.assignment i) ≠ j := by
        intro i h
        have hv := congrArg Fin.val h
        have hi := (p.assignment i).isLt
        exact hj (hv ▸ hi)
      simp [heq]

end Packing

theorem opt_attained (I : Instance) : HasPacking I (opt I) := by
  classical
  exact Nat.find_spec (exists_packing I)

theorem opt_le_of_hasPacking {I : Instance} {b : ℕ} (h : HasPacking I b) :
    opt I ≤ b := by
  classical
  exact Nat.find_min' (exists_packing I) h

theorem opt_le_n (I : Instance) : opt I ≤ I.n :=
  opt_le_of_hasPacking ⟨singletonPacking I⟩

theorem opt_eq_zero_of_n_eq_zero (I : Instance) (h : I.n = 0) : opt I = 0 := by
  have := opt_le_n I
  omega

theorem HasPacking.mono {I : Instance} {b c : ℕ} (h : HasPacking I b) (hbc : b ≤ c) :
    HasPacking I c := by
  obtain ⟨p⟩ := h
  exact ⟨p.enlarge hbc⟩

theorem hasPacking_iff_opt_le (I : Instance) (b : ℕ) :
    HasPacking I b ↔ opt I ≤ b :=
  ⟨opt_le_of_hasPacking, fun h => (opt_attained I).mono h⟩

theorem not_hasPacking_iff_lt_opt (I : Instance) (b : ℕ) :
    ¬ HasPacking I b ↔ b < opt I := by
  rw [hasPacking_iff_opt_le, Nat.not_le]

noncomputable def packingOfFintype {ι : Type*} [Fintype ι]
    (s : ι → ℚ) (hpos : ∀ i, 0 < s i) (hle : ∀ i, s i ≤ 1)
    {b : ℕ} (a : ι → Fin b)
    (hcap : ∀ j, (∑ i, if a i = j then s i else 0) ≤ 1) :
    Packing (Instance.ofFintype s hpos hle) b where
  assignment i := a ((Fintype.equivFin ι).symm i)
  capacity j := by
    change (∑ i : Fin (Fintype.card ι),
      if a ((Fintype.equivFin ι).symm i) = j
      then s ((Fintype.equivFin ι).symm i) else 0) ≤ 1
    rw [(Fintype.equivFin ι).symm.sum_comp
      (fun i : ι => if a i = j then s i else 0)]
    exact hcap j

namespace IndividualConfiguration

variable {I : Instance}

def singleton (i : I.Item) : IndividualConfiguration I :=
  ⟨{i}, by simpa using I.size_le_one i⟩

theorem card_le_five (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i)
    (H : IndividualConfiguration I) : H.val.card ≤ 5 := by
  by_contra h
  have hcard : 6 ≤ H.val.card := by omega
  have hne : H.val.Nonempty := Finset.card_pos.mp (by omega)
  have hstrict := Finset.sum_lt_sum_of_nonempty hne (fun i _ => hlarge i)
  have hsum : (H.val.card : ℚ) * (1 / 6) < ∑ i ∈ H.val, I.size i := by
    simpa using hstrict
  have hc : (6 : ℚ) ≤ H.val.card := by exact_mod_cast hcard
  have hcap := H.property
  linarith

end IndividualConfiguration

namespace Packing

def configuration {I : Instance} {b : ℕ} (p : Packing I b) (j : Fin b) :
    IndividualConfiguration I := ⟨p.binItems j, p.bin_capacity j⟩

theorem bin_card_le_five {I : Instance} {b : ℕ}
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i) (p : Packing I b) (j : Fin b) :
    (p.binItems j).card ≤ 5 :=
  (p.configuration j).card_le_five hlarge

theorem item_count_le_five_mul {I : Instance} {b : ℕ}
    (hlarge : ∀ i, (1 / 6 : ℚ) < I.size i) (p : Packing I b) : I.n ≤ 5 * b := by
  rw [← p.sum_bin_card]
  calc
    ∑ j, (p.binItems j).card ≤ ∑ _j : Fin b, 5 :=
      Finset.sum_le_sum (fun j _ => p.bin_card_le_five hlarge j)
    _ = 5 * b := by simp [Nat.mul_comm]

end Packing

namespace Instance

structure Reindexing (I J : Instance) where
  equiv : I.Item ≃ J.Item
  size_eq : ∀ i, I.size i = J.size (equiv i)

namespace Reindexing

variable {I J : Instance}

def symm (e : Reindexing I J) : Reindexing J I where
  equiv := e.equiv.symm
  size_eq j := by
    simpa using (e.size_eq (e.equiv.symm j)).symm

theorem count_eq (e : Reindexing I J) : I.n = J.n := by
  simpa [Item] using Fintype.card_congr e.equiv

theorem lower_bound_iff (e : Reindexing I J) (a : ℚ) :
    (∀ i, a < I.size i) ↔ ∀ j, a < J.size j := by
  constructor
  · intro h j
    simpa only [e.size_eq, Equiv.apply_symm_apply] using h (e.equiv.symm j)
  · intro h i
    rw [e.size_eq]
    exact h _

end Reindexing

end Instance

namespace Packing

def reindex {I J : Instance} {b : ℕ} (p : Packing I b)
    (e : Instance.Reindexing I J) : Packing J b where
  assignment j := p.assignment (e.equiv.symm j)
  capacity k := by
    calc
      (∑ j : J.Item, if p.assignment (e.equiv.symm j) = k then J.size j else 0) =
          ∑ i : I.Item, if p.assignment (e.equiv.symm (e.equiv i)) = k
            then J.size (e.equiv i) else 0 :=
        (e.equiv.sum_comp (fun j =>
          if p.assignment (e.equiv.symm j) = k then J.size j else 0)).symm
      _ = ∑ i : I.Item, if p.assignment i = k then I.size i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Equiv.symm_apply_apply, ← e.size_eq i]
      _ ≤ 1 := p.capacity k

end Packing

namespace Instance.Reindexing

variable {I J : Instance}

theorem hasPacking_iff (e : Reindexing I J) (b : ℕ) :
    HasPacking I b ↔ HasPacking J b := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.reindex e⟩
  · rintro ⟨p⟩
    exact ⟨p.reindex e.symm⟩

theorem opt_eq (e : Reindexing I J) : opt I = opt J := by
  apply Nat.le_antisymm
  · exact opt_le_of_hasPacking ((e.hasPacking_iff (opt J)).mpr (opt_attained J))
  · exact opt_le_of_hasPacking ((e.hasPacking_iff (opt I)).mp (opt_attained I))

end Instance.Reindexing

namespace RawInstance

@[simp] theorem toInstance_n (r : RawInstance) (hr : r.Valid) :
    (r.toInstance hr).n = r.length := rfl

@[simp] theorem toInstance_size (r : RawInstance) (hr : r.Valid) (i : Fin r.length) :
    (r.toInstance hr).size i = ratValue (r.get i) := rfl

@[simp] theorem valid_nil : Valid [] := by simp [Valid]

end RawInstance

namespace RawPacking

def addFraction (x y : ℕ × ℕ) : ℕ × ℕ :=
  (x.1 * y.2 + y.1 * x.2, x.2 * y.2)

def loadFraction (r : RawInstance) (a : List ℕ) (j : ℕ) : ℕ × ℕ :=
  (r.zip a).foldl
    (fun acc qa => if qa.2 = j then addFraction acc qa.1 else acc) (0, 1)

theorem addFraction_den_pos (x y : ℕ × ℕ) (hx : 0 < x.2) (hy : 0 < y.2) :
    0 < (addFraction x y).2 := Nat.mul_pos hx hy

theorem ratValue_addFraction (x y : ℕ × ℕ) (hx : 0 < x.2) (hy : 0 < y.2) :
    RawInstance.ratValue (addFraction x y) =
      RawInstance.ratValue x + RawInstance.ratValue y := by
  unfold RawInstance.ratValue addFraction
  simp only [Nat.cast_add, Nat.cast_mul]
  have hx' : (x.2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hx)
  have hy' : (y.2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hy)
  field_simp [hx', hy']

private theorem foldFraction_spec (rows : List ((ℕ × ℕ) × ℕ)) (j : ℕ)
    (acc : ℕ × ℕ) (hacc : 0 < acc.2)
    (hrows : ∀ row ∈ rows, 0 < row.1.2) :
    0 < (rows.foldl
      (fun acc qa => if qa.2 = j then addFraction acc qa.1 else acc) acc).2 ∧
    RawInstance.ratValue (rows.foldl
      (fun acc qa => if qa.2 = j then addFraction acc qa.1 else acc) acc) =
      RawInstance.ratValue acc +
        (rows.map fun qa => if qa.2 = j then RawInstance.ratValue qa.1 else 0).sum := by
  induction rows generalizing acc with
  | nil => simpa using And.intro hacc (rfl : RawInstance.ratValue acc = _)
  | cons row rows ih =>
      have hhead : 0 < row.1.2 := hrows row (List.mem_cons_self ..)
      have htail : ∀ q ∈ rows, 0 < q.1.2 :=
        fun q hq => hrows q (List.mem_cons_of_mem _ hq)
      by_cases h : row.2 = j
      · have hrec := ih (addFraction acc row.1) (addFraction_den_pos _ _ hacc hhead) htail
        refine ⟨?_, ?_⟩
        · simpa only [List.foldl_cons, ite_eq_left h] using hrec.1
        · simpa only [List.foldl_cons, ite_eq_left h, List.map_cons, List.sum_cons,
            ratValue_addFraction _ _ hacc hhead, add_assoc] using hrec.2
      · have hrec := ih acc hacc htail
        simpa only [List.foldl_cons, ite_eq_right h, List.map_cons, List.sum_cons, zero_add]
          using hrec

private theorem zip_den_pos {r : RawInstance} (hr : r.Valid) (a : List ℕ) :
    ∀ row ∈ r.zip a, 0 < row.1.2 := by
  intro row hrow
  exact RawInstance.den_pos hr (List.of_mem_zip hrow).1

theorem loadFraction_den_pos (r : RawInstance) (hr : r.Valid) (a : List ℕ) (j : ℕ) :
    0 < (loadFraction r a j).2 :=
  (foldFraction_spec (r.zip a) j (0, 1) (by decide) (zip_den_pos hr a)).1

theorem load_eq_loadFraction (r : RawInstance) (hr : r.Valid) (a : List ℕ) (j : ℕ) :
    load r a j = RawInstance.ratValue (loadFraction r a j) := by
  have h := (foldFraction_spec (r.zip a) j (0, 1) (by decide) (zip_den_pos hr a)).2
  simpa [load, loadFraction, RawInstance.ratValue] using h.symm

theorem load_le_one_iff (r : RawInstance) (hr : r.Valid) (a : List ℕ) (j : ℕ) :
    load r a j ≤ 1 ↔ (loadFraction r a j).1 ≤ (loadFraction r a j).2 := by
  rw [load_eq_loadFraction r hr a j]
  unfold RawInstance.ratValue
  rw [div_le_one₀ (Nat.cast_pos.mpr (loadFraction_den_pos r hr a j))]
  exact Nat.cast_le

theorem load_eq_zero_of_not_mem (r : RawInstance) (a : List ℕ) (j : ℕ)
    (hj : j ∉ a) : load r a j = 0 := by
  unfold load
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hx
  have hmem : row.2 ∈ a := (List.of_mem_zip hrow).2
  have hne : row.2 ≠ j := fun h => hj (h ▸ hmem)
  simp [hne]

theorem feasible_iff_mem_capacity (r : RawInstance) (p : RawPacking) :
    Feasible r p ↔
      p.assignments.length = r.length ∧
      (∀ j ∈ p.assignments, j < p.bins) ∧
      ∀ j ∈ p.assignments, load r p.assignments j ≤ 1 := by
  constructor
  · rintro ⟨hl, hr, hc⟩
    exact ⟨hl, hr, fun j hj => hc j (hr j hj)⟩
  · rintro ⟨hl, hr, hc⟩
    refine ⟨hl, hr, fun j _ => ?_⟩
    by_cases hj : j ∈ p.assignments
    · exact hc j hj
    · rw [load_eq_zero_of_not_mem _ _ _ hj]
      decide

private theorem zip_ofFn_eq {α β : Type*} {n : ℕ} (f : Fin n → α) (g : Fin n → β) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn (fun i => (f i, g i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ, List.zip_cons_cons, ih]

theorem load_ofFn (r : RawInstance) (f : Fin r.length → ℕ) (j : ℕ) :
    load r (List.ofFn f) j =
      ∑ i : Fin r.length, if f i = j then RawInstance.ratValue (r.get i) else 0 := by
  have hz : r.zip (List.ofFn f) = List.ofFn (fun i => (r.get i, f i)) := by
    calc
      r.zip (List.ofFn f) = (List.ofFn r.get).zip (List.ofFn f) :=
        congrArg (fun xs => xs.zip (List.ofFn f)) (List.ofFn_get r).symm
      _ = _ := zip_ofFn_eq r.get f
  simp only [load, hz, List.map_ofFn, List.sum_ofFn, Function.comp_apply]

def assignmentFn (r : RawInstance) (p : RawPacking)
    (h : p.assignments.length = r.length) (i : Fin r.length) : ℕ :=
  p.assignments.get (Fin.cast h.symm i)

theorem assignments_eq_ofFn (r : RawInstance) (p : RawPacking)
    (h : p.assignments.length = r.length) :
    p.assignments = List.ofFn (assignmentFn r p h) := by
  exact (List.ofFn_get p.assignments).symm.trans
    (List.ofFn_congr h p.assignments.get)

def toPacking (r : RawInstance) (hr : r.Valid) (p : RawPacking) (hp : Feasible r p) :
    Packing (r.toInstance hr) p.bins where
  assignment i := ⟨assignmentFn r p hp.1 i,
    hp.2.1 _ (List.get_mem p.assignments (Fin.cast hp.1.symm i))⟩
  capacity j := by
    have hcap := hp.2.2 j.val j.isLt
    rw [assignments_eq_ofFn r p hp.1, load_ofFn] at hcap
    simpa only [RawInstance.toInstance, Fin.ext_iff] using! hcap

@[simp] theorem toPacking_assignment_val (r : RawInstance) (hr : r.Valid)
    (p : RawPacking) (hp : Feasible r p) (i : Fin r.length) :
    ((toPacking r hr p hp).assignment i).val = assignmentFn r p hp.1 i := rfl

def ofPacking {I : Instance} {b : ℕ} (q : Packing I b) : RawPacking where
  bins := b
  assignments := List.ofFn (fun i => (q.assignment i).val)

theorem ofPacking_feasible (r : RawInstance) (hr : r.Valid) {b : ℕ}
    (q : Packing (r.toInstance hr) b) : Feasible r (ofPacking q) := by
  refine ⟨by simp [ofPacking, RawInstance.toInstance], ?_, ?_⟩
  · intro j hj
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
    exact (q.assignment i).isLt
  · intro j hj
    have hcap := q.capacity ⟨j, hj⟩
    change load r (List.ofFn (fun i : Fin r.length => (q.assignment i).val)) j ≤ 1
    rw [load_ofFn]
    simpa only [RawInstance.toInstance, Fin.ext_iff] using! hcap

theorem feasible_iff_exists_packing (r : RawInstance) (hr : r.Valid) (p : RawPacking) :
    Feasible r p ↔
      ∃ q : Packing (r.toInstance hr) p.bins,
        p.assignments = List.ofFn (fun i => (q.assignment i).val) := by
  constructor
  · intro hp
    exact ⟨toPacking r hr p hp, assignments_eq_ofFn r p hp.1⟩
  · rintro ⟨q, hq⟩
    have hp := ofPacking_feasible r hr q
    simpa only [ofPacking, ← hq] using hp

theorem hasPacking_iff_exists_feasible (r : RawInstance) (hr : r.Valid) (b : ℕ) :
    HasPacking (r.toInstance hr) b ↔
      ∃ a : List ℕ, Feasible r ⟨b, a⟩ := by
  constructor
  · rintro ⟨q⟩
    exact ⟨(ofPacking q).assignments, ofPacking_feasible r hr q⟩
  · rintro ⟨a, ha⟩
    exact ⟨toPacking r hr ⟨b, a⟩ ha⟩

@[simp] theorem feasible_nil_iff (p : RawPacking) :
    Feasible [] p ↔ p.assignments = [] := by
  constructor
  · intro hp
    exact List.length_eq_zero_iff.mp hp.1
  · intro h
    cases p with
    | mk b a =>
        dsimp at h
        subst a
        simp [Feasible, load]

theorem feasible_zero_bins_iff (r : RawInstance) (a : List ℕ) :
    Feasible r ⟨0, a⟩ ↔ r = [] ∧ a = [] := by
  constructor
  · rintro ⟨hl, hr, _⟩
    have ha : a = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro j hj
      exact Nat.not_lt_zero j (hr j hj)
    refine ⟨?_, ha⟩
    apply List.length_eq_zero_iff.mp
    simpa [ha] using hl.symm
  · rintro ⟨rfl, rfl⟩
    simp

end RawPacking

namespace Instance

def toRaw (I : Instance) : RawInstance :=
  List.ofFn fun i : Fin I.n => ((I.size i).num.toNat, (I.size i).den)

@[simp] theorem toRaw_length (I : Instance) : I.toRaw.length = I.n := by
  simp [toRaw]

private theorem ratValue_num_den (x : ℚ) (hx : 0 ≤ x) :
    RawInstance.ratValue (x.num.toNat, x.den) = x := by
  have hn : 0 ≤ x.num := Rat.num_nonneg.mpr hx
  have hc : (x.num.toNat : ℚ) = (x.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  simpa only [RawInstance.ratValue, hc] using Rat.num_div_den x

theorem toRaw_valid (I : Instance) : I.toRaw.Valid := by
  intro q hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  have hpos : 0 < (I.size i).num := Rat.num_pos.mpr (I.size_pos i)
  have hn : 0 < (I.size i).num.toNat := Int.pos_iff_toNat_pos.mp hpos
  refine ⟨hn, ?_⟩
  have hrat := I.size_le_one i
  rw [← ratValue_num_den (I.size i) (I.size_pos i).le] at hrat
  change ((I.size i).num.toNat : ℚ) / (I.size i).den ≤ 1 at hrat
  exact Nat.cast_le.mp ((div_le_one₀ (Nat.cast_pos.mpr (I.size i).den_pos)).mp hrat)

theorem toRaw_size (I : Instance) (i : Fin I.toRaw.length) :
    RawInstance.ratValue (I.toRaw.get i) = I.size (Fin.cast (toRaw_length I) i) := by
  have hget : I.toRaw.get i =
      ((I.size (Fin.cast (toRaw_length I) i)).num.toNat,
        (I.size (Fin.cast (toRaw_length I) i)).den) :=
    List.get_ofFn (fun j : Fin I.n => ((I.size j).num.toNat, (I.size j).den)) i
  rw [hget]
  exact ratValue_num_den (I.size (Fin.cast (toRaw_length I) i)) (I.size_pos _).le

def toRawReindexing (I : Instance) :
    Reindexing I (I.toRaw.toInstance (toRaw_valid I)) where
  equiv := finCongr (toRaw_length I).symm
  size_eq i := by
    change I.size i =
      RawInstance.ratValue (I.toRaw.get (Fin.cast (toRaw_length I).symm i))
    rw [toRaw_size]
    rfl

private theorem eq_of_indexed_sizes {I J : Instance} (h : I.n = J.n)
    (hs : ∀ i : I.Item, I.size i = J.size (Fin.cast h i)) : I = J := by
  cases I with
  | mk n s hp hl =>
    cases J with
    | mk m t hq hk =>
      dsimp at h hs
      subst m
      simp only [Fin.cast_refl] at hs
      have hst : s = t := funext hs
      subst t
      rfl

theorem toInstance_toRaw (I : Instance) :
    I.toRaw.toInstance (toRaw_valid I) = I := by
  apply eq_of_indexed_sizes (toRaw_length I)
  intro i
  exact toRaw_size I i

end Instance

namespace RawPacking

theorem ofPacking_cast {I J : Instance} {b : ℕ} (h : I = J) (q : Packing I b) :
    ofPacking (h ▸ q) = ofPacking q := by
  cases h
  rfl

theorem ofPacking_toRaw_feasible {I : Instance} {b : ℕ} (q : Packing I b) :
    Feasible I.toRaw (ofPacking q) := by
  have hI := (Instance.toInstance_toRaw I).symm
  have h := ofPacking_feasible I.toRaw I.toRaw_valid (hI ▸ q)
  rwa [ofPacking_cast hI q] at h

end RawPacking

end BinPackingGap

namespace BinPackingGap.FractionWidth

def denominatorBits (r : RawInstance) : ℕ :=
  (r.map fun q => q.2.size).sum

@[simp] theorem denominatorBits_nil : denominatorBits [] = 0 := rfl

@[simp] theorem denominatorBits_cons (q : ℕ × ℕ) (r : RawInstance) :
    denominatorBits (q :: r) = q.2.size + denominatorBits r := rfl

theorem size_mono {a b : ℕ} (h : a ≤ b) : a.size ≤ b.size := by
  apply Nat.size_le.mpr
  exact lt_of_le_of_lt h (Nat.size_le.mp (le_refl b.size))

theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ a.size := Nat.size_le.mp (le_refl a.size)
  have hb : b < 2 ^ b.size := Nat.size_le.mp (le_refl b.size)
  calc
    a * b ≤ a * 2 ^ b.size := Nat.mul_le_mul_left a (Nat.le_of_lt hb)
    _ < 2 ^ a.size * 2 ^ b.size :=
      mul_lt_mul_of_pos_right ha (pow_pos (by decide) _)
    _ = 2 ^ (a.size + b.size) := (pow_add 2 a.size b.size).symm

theorem size_add_le {a b H : ℕ} (ha : a.size ≤ H) (hb : b.size ≤ H) :
    (a + b).size ≤ H + 1 := by
  apply Nat.size_le.mpr
  have h := Nat.add_lt_add (Nat.size_le.mp ha) (Nat.size_le.mp hb)
  simpa only [pow_succ, Nat.mul_two] using h

theorem addFraction_left_product_size_le {x q : ℕ × ℕ} (hx : x.1 ≤ x.2) :
    (x.1 * q.2).size ≤ x.2.size + q.2.size := by
  exact (size_mono (Nat.mul_le_mul_right q.2 hx)).trans (size_mul_le x.2 q.2)

theorem addFraction_right_product_size_le {x q : ℕ × ℕ} (hq : q.1 ≤ q.2) :
    (q.1 * x.2).size ≤ x.2.size + q.2.size := by
  have h := (size_mono (Nat.mul_le_mul_right x.2 hq)).trans
    (size_mul_le q.2 x.2)
  simpa only [Nat.add_comm] using h

theorem addFraction_num_size_le {x q : ℕ × ℕ}
    (hx : x.1 ≤ x.2) (hq : q.1 ≤ q.2) :
    (RawPacking.addFraction x q).1.size ≤ x.2.size + q.2.size + 1 := by
  exact size_add_le (addFraction_left_product_size_le hx)
    (addFraction_right_product_size_le hq)

theorem addFraction_den_size_le (x q : ℕ × ℕ) :
    (RawPacking.addFraction x q).2.size ≤ x.2.size + q.2.size :=
  size_mul_le x.2 q.2

theorem fold_den_size_le (r : RawInstance) (a : List ℕ) (j : ℕ) (x : ℕ × ℕ) :
    ((r.zip a).foldl
      (fun acc qa => if qa.2 = j then RawPacking.addFraction acc qa.1 else acc) x).2.size
      ≤ x.2.size + denominatorBits r := by
  induction r generalizing a x with
  | nil => simp
  | cons q r ih =>
      cases a with
      | nil => simp
      | cons b a =>
          simp only [List.zip_cons_cons, List.foldl_cons, denominatorBits_cons]
          by_cases hb : b = j
          · simp only [ite_eq_left hb]
            have hfold := ih a (RawPacking.addFraction x q)
            have hstep := addFraction_den_size_le x q
            omega
          · simp only [ite_eq_right hb]
            have hfold := ih a x
            omega

theorem loadFraction_den_size_le (r : RawInstance) (a : List ℕ) (j : ℕ) :
    (RawPacking.loadFraction r a j).2.size ≤ denominatorBits r + 1 := by
  simpa [RawPacking.loadFraction, Nat.add_comm] using
    fold_den_size_le r a j (0, 1)

theorem loadFraction_num_size_le_of_accepted
    (r : RawInstance) (a : List ℕ) (j : ℕ)
    (h : (RawPacking.loadFraction r a j).1 ≤ (RawPacking.loadFraction r a j).2) :
    (RawPacking.loadFraction r a j).1.size ≤ denominatorBits r + 1 :=
  (size_mono h).trans (loadFraction_den_size_le r a j)

theorem addFraction_width_of_budget {x q : ℕ × ℕ} {H : ℕ}
    (hx : x.1 ≤ x.2) (hq : q.1 ≤ q.2) (hD : x.2.size ≤ H + 1) :
    (RawPacking.addFraction x q).2.size ≤ H + q.2.size + 1 ∧
    (x.1 * q.2).size ≤ H + q.2.size + 1 ∧
    (q.1 * x.2).size ≤ H + q.2.size + 1 ∧
    (RawPacking.addFraction x q).1.size ≤ H + q.2.size + 2 := by
  have hden := addFraction_den_size_le x q
  have hleft := addFraction_left_product_size_le (q := q) hx
  have hright := addFraction_right_product_size_le (x := x) hq
  have hnum := addFraction_num_size_le hx hq
  omega

theorem loadFraction_next_width (r : RawInstance) (a : List ℕ) (j : ℕ)
    (q : ℕ × ℕ)
    (h : (RawPacking.loadFraction r a j).1 ≤ (RawPacking.loadFraction r a j).2)
    (hq : q.1 ≤ q.2) :
    (RawPacking.addFraction (RawPacking.loadFraction r a j) q).2.size
        ≤ denominatorBits r + q.2.size + 1 ∧
    ((RawPacking.loadFraction r a j).1 * q.2).size
        ≤ denominatorBits r + q.2.size + 1 ∧
    (q.1 * (RawPacking.loadFraction r a j).2).size
        ≤ denominatorBits r + q.2.size + 1 ∧
    (RawPacking.addFraction (RawPacking.loadFraction r a j) q).1.size
        ≤ denominatorBits r + q.2.size + 2 :=
  addFraction_width_of_budget h hq (loadFraction_den_size_le r a j)

theorem addFraction_overflow {x q : ℕ × ℕ}
    (hx : x.2 < x.1) (hq : 0 < q.2) :
    (RawPacking.addFraction x q).2 < (RawPacking.addFraction x q).1 := by
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hx hq)
    (Nat.le_add_right (x.1 * q.2) (q.1 * x.2))

theorem fold_overflow (r : RawInstance) (a : List ℕ) (j : ℕ) (x : ℕ × ℕ)
    (hr : r.Valid) (hx : x.2 < x.1) :
    let y := (r.zip a).foldl
      (fun acc qa => if qa.2 = j then RawPacking.addFraction acc qa.1 else acc) x
    y.2 < y.1 := by
  induction r generalizing a x with
  | nil => simpa using hx
  | cons q r ih =>
      have hr' : RawInstance.Valid r := fun z hz => hr z (List.mem_cons_of_mem q hz)
      have hq : 0 < q.2 := RawInstance.den_pos hr (List.mem_cons_self ..)
      cases a with
      | nil => simpa using hx
      | cons b a =>
          simp only [List.zip_cons_cons, List.foldl_cons]
          by_cases hb : b = j
          · simp only [ite_eq_left hb]
            exact ih a (RawPacking.addFraction x q) hr' (addFraction_overflow hx hq)
          · simp only [ite_eq_right hb]
            exact ih a x hr' hx

end BinPackingGap.FractionWidth

end OAI
