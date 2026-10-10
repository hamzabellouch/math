import Mathlib
import OAI.Combinatorics.KMedian.Binary.NumericParserProgram
import OAI.Combinatorics.KMedian.Hardness.Coverage
import OAI.Combinatorics.KMedian.Process.RoundingListOperations

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Binary Binary.Automatic Binary.Automatic.Poly

abbrev Raw := ℕ × ℕ × ℕ × List Bool

namespace Raw
abbrev m (r : Raw) := r.1
abbrev n (r : Raw) := r.2.1
abbrev k (r : Raw) := r.2.2.1
abbrev table (r : Raw) := r.2.2.2

def parse (xs : List Bool) : Raw :=
  let a := InputParser.natRead xs
  let b := InputParser.natRead a.2
  let c := InputParser.natRead b.2
  (a.1, b.1, c.1, c.2)

@[fun_prop] theorem parse_poly : Poly parse := by unfold parse; fun_prop

def indices (r : Raw) : List ℕ :=
  List.range ((r.table.take r.m ++ r.table.take r.n).length)

@[fun_prop] theorem indices_poly : Poly indices := by
  unfold indices
  apply Poly.comp Poly.list_indices
  dsimp only [m, n, table]
  apply Poly.comp (f := fun lists : List Bool × List Bool => lists.1 ++ lists.2)
    (g := fun raw : Raw => (raw.2.2.2.take raw.1, raw.2.2.2.take raw.2.1))
    Poly.list_append
  apply Poly.pair
  · exact Poly.comp (f := fun input : List Bool × ℕ => input.1.take input.2)
      InputParser.take_poly (g := fun raw : Raw => (raw.2.2.2, raw.1)) (by fun_prop)
  · exact Poly.comp (f := fun input : List Bool × ℕ => input.1.take input.2)
      InputParser.take_poly (g := fun raw : Raw => (raw.2.2.2, raw.2.1)) (by fun_prop)

noncomputable def bitsProgram : PolyProgram Nat.bits (Binary.encodeList Binary.encodeBool) Nat.bits :=
  BooleanLists.packProgram.recode Nat.bits (fun _ => rfl) (fun _ => rfl)

@[fun_prop] theorem bits_poly : Poly Nat.bits := ⟨bitsProgram⟩

@[fun_prop] theorem encodeNat_poly : Poly encodeNat := by
  change Poly (fun n : ℕ => encodeNat n)
  have h : Poly (fun n : ℕ => n.bits.map (fun _ => true) ++ [false] ++ n.bits) := by
    fun_prop
  simpa only [List.map_const', encodeNat] using h

def entry (r : Raw) (a b : ℕ) : List Bool :=
  if a = b then encodeRat 0 else
  if a < r.m then
    if b < r.m then encodeRat 2 else
      if (r.table[a * r.n + (b - r.m)]?).getD false then encodeRat 1 else encodeRat 3
  else
    if b < r.m then
      if (r.table[b * r.n + (a - r.m)]?).getD false then encodeRat 1 else encodeRat 3
    else encodeRat 2

@[fun_prop] theorem entry_poly : Poly (fun x : Raw × ℕ × ℕ => x.1.entry x.2.1 x.2.2) := by
  unfold entry; fun_prop

def medianBytes (r : Raw) : List Bool :=
  encodeNat (r.m + r.n) ++ encodeNat r.k ++
  (r.indices.map (fun a => decide (a < r.m))) ++
  (r.indices.map (fun a => decide (r.m ≤ a))) ++
  (r.indices.flatMap (fun a => r.indices.flatMap (fun b => r.entry a b)))

@[fun_prop] theorem medianBytes_poly : Poly medianBytes := by
  have hr : Poly (fun x : Raw × ℕ =>
      x.1.indices.flatMap (fun b => x.1.entry x.2 b)) := by
    apply Poly.list_flatMap
    · exact Poly.comp (g := fun x : (Raw × ℕ) × ℕ => (x.1.1, x.1.2, x.2))
        entry_poly (by fun_prop)
    · exact Poly.comp indices_poly Poly.fst
  have hmatrix : Poly (fun r : Raw => r.indices.flatMap (fun a =>
      r.indices.flatMap (fun b => r.entry a b))) :=
    Poly.list_flatMap hr indices_poly
  have hc : Poly (fun r : Raw => r.indices.map (fun a => decide (a < r.m))) := by
    apply Poly.list_map _ indices_poly
    dsimp only [m]; fun_prop
  have hf : Poly (fun r : Raw => r.indices.map (fun a => decide (r.m ≤ a))) := by
    apply Poly.list_map _ indices_poly
    dsimp only [m]; fun_prop
  have hn : Poly (fun r : Raw => encodeNat (r.m + r.n)) :=
    Poly.comp encodeNat_poly (by dsimp only [m, n]; fun_prop)
  have hk : Poly (fun r : Raw => encodeNat r.k) :=
    Poly.comp (g := fun r : Raw => r.k) encodeNat_poly (by fun_prop)
  let app := Poly.list_append (α := Bool)
  have hh : Poly (fun r : Raw => encodeNat (r.m + r.n) ++ encodeNat r.k) :=
    Poly.comp (f := fun x : List Bool × List Bool => x.1 ++ x.2) app (Poly.pair hn hk)
  have hh1 : Poly (fun r : Raw => encodeNat (r.m + r.n) ++ encodeNat r.k ++
      r.indices.map (fun a => decide (a < r.m))) :=
    Poly.comp (f := fun x : List Bool × List Bool => x.1 ++ x.2) app (Poly.pair hh hc)
  have hh2 : Poly (fun r : Raw => encodeNat (r.m + r.n) ++ encodeNat r.k ++
      r.indices.map (fun a => decide (a < r.m)) ++
      r.indices.map (fun a => decide (r.m ≤ a))) :=
    Poly.comp (f := fun x : List Bool × List Bool => x.1 ++ x.2) app (Poly.pair hh1 hf)
  exact Poly.comp (f := fun x : List Bool × List Bool => x.1 ++ x.2) app (Poly.pair hh2 hmatrix)

noncomputable def parsedProgram : PolyProgram id enc parse :=
  BooleanLists.packProgram.comp parse_poly.program

attribute [irreducible] parsedProgram

noncomputable def typedMedianProgram : PolyProgram id enc (fun xs => (parse xs).medianBytes) :=
  PolyProgram.comp (ea := id) (eb := enc) (ec := enc)
    (f := parse) (g := medianBytes) parsedProgram medianBytes_poly.program

attribute [irreducible] typedMedianProgram

noncomputable def medianProgram : PolyProgram id id (fun xs => (parse xs).medianBytes) :=
  PolyProgram.comp (f := fun xs : List Bool => (parse xs).medianBytes)
    (g := id) typedMedianProgram BooleanLists.unpackProgram

end Raw

namespace Input

def raw (C : Input) : Raw :=
  (C.m, C.n, C.k, (List.ofFn (fun j : Fin C.m => List.ofFn (C.incident j))).flatten)

theorem parse_encode (C : Input) : Raw.parse C.encode = C.raw := by
  simp only [Raw.parse, encode, List.append_assoc, InputParser.natRead_append, raw]

theorem table_length (C : Input) : C.raw.table.length = C.m * C.n := by
  simp [raw, Raw.table, List.length_flatten, List.sum_ofFn, Finset.sum_const]

theorem n_pos (C : Input) : 0 < C.n := lt_of_lt_of_le C.k_pos C.k_le

theorem indices_raw (C : Input) : C.raw.indices = List.range (C.m + C.n) := by
  have hm : C.m ≤ C.raw.table.length := by
    rw [C.table_length]; exact Nat.le_mul_of_pos_right _ C.n_pos
  have hn : C.n ≤ C.raw.table.length := by
    rw [C.table_length]; exact Nat.le_mul_of_pos_left _ C.m_pos
  simp only [Raw.indices, List.length_append, List.length_take]
  change List.range (min C.m C.raw.table.length + min C.n C.raw.table.length) = _
  rw [Nat.min_eq_left hm, Nat.min_eq_left hn]

@[simp] theorem raw_m (C : Input) : C.raw.m = C.m := rfl
@[simp] theorem raw_n (C : Input) : C.raw.n = C.n := rfl
@[simp] theorem raw_k (C : Input) : C.raw.k = C.k := rfl

theorem table_flatten (C : Input) : C.raw.table =
    List.ofFn (fun t : Fin (C.m * C.n) =>
      C.incident (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2) := by
  symm
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  apply congrArg List.ofFn
  funext i
  have hji : j.val * C.n + i.val < C.m * C.n := by
    calc
      _ < j.val * C.n + C.n := Nat.add_lt_add_left i.isLt _
      _ = (j.val + 1) * C.n := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ j.isLt
  have he : (⟨j.val * C.n + i.val, hji⟩ : Fin (C.m * C.n)) =
      finProdFinEquiv (j, i) := by
    apply Fin.ext
    change _ = i.val + C.n * j.val
    ac_rfl
  rw [he, finProdFinEquiv.symm_apply_apply]

theorem table_get (C : Input) (j : Fin C.m) (i : Fin C.n) :
    (C.raw.table[j.val * C.n + i.val]?).getD false = C.incident j i := by
  rw [C.table_flatten]
  have hji : j.val * C.n + i.val < C.m * C.n := by
    calc
      _ < j.val * C.n + C.n := Nat.add_lt_add_left i.isLt _
      _ = (j.val + 1) * C.n := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ j.isLt
  simp only [List.getElem?_ofFn, dite_eq_left hji, Option.getD_some]
  have he : (⟨j.val * C.n + i.val, hji⟩ : Fin (C.m * C.n)) =
      finProdFinEquiv (j, i) := by
    apply Fin.ext
    change _ = i.val + C.n * j.val
    ac_rfl
  rw [he, finProdFinEquiv.symm_apply_apply]

@[simp] theorem client_val (C : Input) (j : Fin C.m) : (C.client j).val = j.val := rfl
@[simp] theorem facility_val (C : Input) (i : Fin C.n) : (C.facility i).val = C.m + i.val := rfl

theorem entry_point (C : Input) (x y : C.Point) :
    C.raw.entry (finSumFinEquiv x).val (finSumFinEquiv y).val =
      encodeRat (C.pointDistance x y) := by
  cases x with
  | inl j =>
    cases y with
    | inl l =>
      simp only [finSumFinEquiv_apply_left, Fin.val_castAdd, Raw.entry, raw_m,
        j.isLt, l.isLt, ↓reduceIte, pointDistance, Fin.val_inj]
      split_ifs <;> rfl
    | inr i =>
      have hij : j.val ≠ C.m + i.val := by omega
      have hm : ¬ C.m + i.val < C.m := by omega
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.val_castAdd, Fin.val_natAdd, Raw.entry, raw_m, raw_n, hij,
        j.isLt, hm, ↓reduceIte, Nat.add_sub_cancel_left, C.table_get, pointDistance]
      split_ifs <;> rfl
  | inr i =>
    cases y with
    | inl j =>
      have hij : C.m + i.val ≠ j.val := by omega
      have hm : ¬ C.m + i.val < C.m := by omega
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.val_castAdd, Fin.val_natAdd, Raw.entry, raw_m, raw_n, hij,
        j.isLt, hm, ↓reduceIte, Nat.add_sub_cancel_left, C.table_get, pointDistance]
      split_ifs <;> rfl
    | inr h =>
      have hi : ¬ C.m + i.val < C.m := by omega
      have hh : ¬ C.m + h.val < C.m := by omega
      simp only [finSumFinEquiv_apply_right, Fin.val_natAdd, Raw.entry, raw_m,
        hi, hh, ↓reduceIte, Nat.add_left_cancel_iff, Fin.val_inj, pointDistance]
      split_ifs <;> rfl

theorem entry_distance (C : Input) (x y : Fin (C.m + C.n)) :
    C.raw.entry x.val y.val = encodeRat (C.toMedian.distance x y) := by
  simpa only [Equiv.apply_symm_apply, toMedian] using
    C.entry_point (finSumFinEquiv.symm x) (finSumFinEquiv.symm y)

theorem mem_clients_iff (C : Input) (x : Fin (C.m + C.n)) :
    x ∈ C.toMedian.clients ↔ x.val < C.m := by
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective x
  cases a with
  | inl j =>
    constructor
    · intro _; exact j.isLt
    · intro _; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  | inr i =>
    constructor
    · intro hx
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
      exact False.elim (C.client_ne_facility j i hj)
    · intro hx
      change C.m + i.val < C.m at hx
      omega

theorem mem_facilities_iff (C : Input) (x : Fin (C.m + C.n)) :
    x ∈ C.toMedian.facilities ↔ C.m ≤ x.val := by
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective x
  cases a with
  | inl j =>
    constructor
    · intro hx
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
      exact False.elim (C.client_ne_facility j i hi.symm)
    · intro hx
      change C.m ≤ j.val at hx
      omega
  | inr i =>
    constructor
    · intro _; change C.m ≤ C.m + i.val; omega
    · intro _; exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem medianBytes_correct (C : Input) : C.raw.medianBytes = encodeInstance C.toMedian := by
  change C.raw.medianBytes =
    encodeNat (C.m + C.n) ++ encodeNat C.k ++
      List.ofFn (fun i : Fin (C.m + C.n) => decide (i ∈ Finset.univ.image C.client)) ++
      List.ofFn (fun i : Fin (C.m + C.n) => decide (i ∈ C.chosenFacilities Finset.univ)) ++
      (List.ofFn (fun i : Fin (C.m + C.n) => (List.ofFn (fun j : Fin (C.m + C.n) =>
        encodeRat (C.pointDistance (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)))).flatten)).flatten
  have hc (x : Fin (C.m + C.n)) : x ∈ Finset.univ.image C.client ↔ x.val < C.m :=
    C.mem_clients_iff x
  have hf (x : Fin (C.m + C.n)) : x ∈ C.chosenFacilities Finset.univ ↔ C.m ≤ x.val :=
    C.mem_facilities_iff x
  have he (x y : Fin (C.m + C.n)) : C.raw.entry x.val y.val =
      encodeRat (C.pointDistance (finSumFinEquiv.symm x) (finSumFinEquiv.symm y)) :=
    C.entry_distance x y
  unfold Raw.medianBytes
  change encodeNat (C.m + C.n) ++ encodeNat C.k ++
    (C.raw.indices.map (fun a => decide (a < C.m))) ++
    (C.raw.indices.map (fun a => decide (C.m ≤ a))) ++
    (C.raw.indices.flatMap (fun a => C.raw.indices.flatMap (fun b => C.raw.entry a b))) = _
  simp only [C.indices_raw, RoundingList.range_finRange,
    ← List.ofFn_eq_map, List.flatMap_def, List.map_ofFn, Function.comp_def, he]
  simp only [hc, hf]

noncomputable def reductionProgram : Binary.PolyProgram encode encodeInstance toMedian :=
  Raw.medianProgram.recode encode (fun _ => rfl) (fun C => by
    simp only [C.parse_encode, C.medianBytes_correct, id_eq])

theorem reduction_finite_poly : Complexity.FinitePolyTime encode encodeInstance toMedian :=
  ⟨reductionProgram.stock, reductionProgram.finite_work⟩

end Input
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
