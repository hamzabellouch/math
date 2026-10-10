import OAI.ModelTheory.Categoricity.ArrayMaps

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Tests

open Tuples

theorem congr {I : Type v} (hCH : CH.{u}) {c d : Tuple I → Colors.Palette.{u}}
    (t : Tuple I) (h : ∀ m (e : Fin (m + 1) ↪o Fin (t.1 + 1)), c (sub t e) = d (sub t e)) :
    Test hCH c t ↔ Test hCH d t := by
  have he : (fun m (e : Fin (m + 1) ↪o Fin (t.1 + 1)) => c (sub t e)) =
      (fun m (e : Fin (m + 1) ↪o Fin (t.1 + 1)) => d (sub t e)) := funext (fun m => funext (h m))
  exact iff_of_eq (congrArg (Passes hCH) he)

@[simp] theorem map {I J : Type u} (hCH : CH.{u}) (f : I ↪ J)
    (c : Tuple J → Colors.Palette.{u}) (t : Tuple I) :
    Test hCH c (Tuples.map f t) ↔ Test hCH (fun s => c (Tuples.map f s)) t := Iff.rfl

end Tests

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N P : Data.{u}}
local instance : DecidableEq M.B := Classical.decEq M.B
local instance : DecidableEq N.B := Classical.decEq N.B
local instance : DecidableEq P.B := Classical.decEq P.B

def Map.colors (f : Map M N) (t : Tuple M.I) (b : N.B) : Colors.Palette.{u} :=
  ⟨Colors.color (fun n => N.bits (Tuples.map f.index t) n b ^^ decide (b ∈ f.rowShift t n))⟩

theorem color_column (a : ℕ → Bool) (v : Finset ℕ) :
    Colors.color (fun n => a n ^^ decide (n ∈ v)) = Colors.color a := by
  apply Quotient.sound
  apply v.finite_toSet.subset
  intro n hn
  by_contra h
  have h' : n ∉ v := h
  exact hn (by simp [h'])

@[simp] theorem Map.colors_base (f : Map M N) (t : Tuple M.I) (b : M.B) :
    f.colors t (f.base b) = M.colors t b := by
  apply ULift.ext
  change Colors.color _ = Colors.color _
  have he : (fun n => N.bits (Tuples.map f.index t) n (f.base b) ^^
      decide (f.base b ∈ f.rowShift t n)) =
      (fun n => M.bits t n b ^^ decide (n ∈ f.colShift t b)) := by
    funext n
    have h := f.bit_agrees t n b
    dsimp [Matrix.bit] at h
    rw [← h, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  rw [he, color_column]

def Map.exceptions (f : Map M N) (t : Tuple M.I) : Set N.B :=
  ⋃ m : ℕ, ⋃ e : Fin (m + 1) ↪o Fin (t.1 + 1), ⋃ n : ℕ,
    (f.rowShift (sub t e) n : Set N.B)

theorem Map.exceptions_countable (f : Map M N) (t : Tuple M.I) :
    (f.exceptions t).Countable := by
  classical
  apply Set.countable_iUnion
  intro m
  apply Set.countable_iUnion
  intro e
  exact Set.countable_iUnion (fun n => (f.rowShift (sub t e) n).countable_toSet)

theorem Map.test_away (f : Map M N) (hCH : CH.{u}) (t : Tuple M.I) (b : N.B)
    (hb : b ∉ f.exceptions t) :
    Tests.Test hCH (fun s => f.colors s b) t ↔
      Tests.Test hCH (fun s => N.colors s b) (Tuples.map f.index t) := by
  rw [Tests.map]
  apply Tests.congr
  intro m e
  have hn : ∀ n, b ∉ f.rowShift (sub t e) n := by
    intro n h
    apply hb
    exact Set.mem_iUnion.2 ⟨m, Set.mem_iUnion.2 ⟨e, Set.mem_iUnion.2 ⟨n, h⟩⟩⟩
  simp only [Map.colors, Data.colors, hn, decide_false, Bool.xor_false]

structure Map.Strong (hCH : CH.{u}) (f : Map M N) : Prop where
  convex : Set.OrdConnected (Set.range f.base)
  outside : ∀ (t : Tuple M.I) (b : N.B), b ∉ Set.range f.base →
    Tests.Test hCH (fun s => f.colors s b) t

@[simp] theorem Map.id_strong (hCH : CH.{u}) (M : Data.{u}) : (Map.id M).Strong hCH := by
  constructor
  · simpa only [Map.id, OrderIso.coe_toOrderEmbedding, OrderIso.coe_refl, Set.range_id] using
      (Set.ordConnected_univ : Set.OrdConnected (Set.univ : Set M.B))
  · intro t b hb
    exact (hb ⟨b, rfl⟩).elim

theorem Map.comp_colors_base (g : Map N P) (f : Map M N) (t : Tuple M.I) (b : N.B) :
    (g.comp f).colors t (g.base b) = f.colors t b := by
  apply ULift.ext
  change Colors.color _ = Colors.color _
  have he : (fun n => P.bits (Tuples.map (g.comp f).index t) n (g.base b) ^^
      decide (g.base b ∈ (g.comp f).rowShift t n)) =
      (fun n => (N.bits (Tuples.map f.index t) n b ^^ decide (b ∈ f.rowShift t n)) ^^
        decide (n ∈ g.colShift (Tuples.map f.index t) b)) := by
    funext n
    have hv : g.colShift (Tuples.map f.index t) b ∆ ∅ =
        g.colShift (Tuples.map f.index t) b := by simp
    have h := g.bit_all (Tuples.map f.index t) n (f.rowShift t n) b ∅
    simp only [Matrix.bit, Finset.notMem_empty, decide_false, Bool.xor_false, hv] at h
    change (P.bits (Tuples.map g.index (Tuples.map f.index t)) n (g.base b) ^^
      decide (g.base b ∈ g.rowShift (Tuples.map f.index t) n ∆
        (f.rowShift t n).map g.base.toEmbedding)) = _
    rw [← h, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  rw [he, color_column]

theorem Map.comp_colors_outside (g : Map N P) (f : Map M N) (t : Tuple M.I) (b : P.B)
    (hb : b ∉ Set.range g.base) :
    (g.comp f).colors t b = g.colors (Tuples.map f.index t) b := by
  have hn : ∀ n, b ∉ (f.rowShift t n).map g.base.toEmbedding := by
    intro n h
    obtain ⟨a, _, ha⟩ := Finset.mem_map.1 h
    exact hb ⟨a, ha⟩
  apply ULift.ext
  apply congrArg Colors.color
  funext n
  change (P.bits (Tuples.map g.index (Tuples.map f.index t)) n b ^^ _) = _
  congr 1
  simp only [Map.comp, Finset.mem_symmDiff, hn, not_false_eq_true, and_true, false_and, or_false]

theorem Map.Strong.comp (hCH : CH.{u}) {g : Map N P} {f : Map M N}
    (hg : g.Strong hCH) (hf : f.Strong hCH) : (g.comp f).Strong hCH := by
  constructor
  · constructor
    intro x hx y hy z hz
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := hg.convex.out (by exact ⟨f.base a, rfl⟩)
      (by exact ⟨f.base b, rfl⟩) hz
    have hc : c ∈ Set.Icc (f.base a) (f.base b) := by
      exact ⟨g.base.le_iff_le.1 hz.1, g.base.le_iff_le.1 hz.2⟩
    obtain ⟨d, rfl⟩ := hf.convex.out ⟨a, rfl⟩ ⟨b, rfl⟩ hc
    exact ⟨d, rfl⟩
  · intro t b hb
    by_cases hbg : b ∈ Set.range g.base
    · obtain ⟨c, rfl⟩ := hbg
      have hc : c ∉ Set.range f.base := by
        rintro ⟨d, rfl⟩
        exact hb ⟨d, rfl⟩
      simpa only [Map.comp_colors_base] using hf.outside t c hc
    · have h := hg.outside (Tuples.map f.index t) b hbg
      rw [Tests.map] at h
      simpa only [Map.comp_colors_outside g f _ b hbg] using h

end Arrays

namespace Tuples

variable {I J : Type u}

def mapEquiv (e : I ≃ J) : Tuple I ≃ Tuple J where
  toFun := map e.toEmbedding
  invFun := map e.symm.toEmbedding
  left_inv t := by
    have h : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl I := by ext x; simp
    rw [map_comp, h, map_refl]
  right_inv t := by
    have h : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl J := by ext x; simp
    rw [map_comp, h, map_refl]

end Tuples

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N : Data.{u}}
local instance : DecidableEq M.B := Classical.decEq M.B
local instance : DecidableEq N.B := Classical.decEq N.B

theorem Map.surjective (f : Map M N) (hi : Function.Surjective f.index)
    (hb : Function.Surjective f.base) : Function.Surjective f.onPoint := by
  classical
  let ei : M.I ≃ N.I := Equiv.ofBijective f.index ⟨f.index.injective, hi⟩
  let eb : M.B ≃ N.B := Equiv.ofBijective f.base ⟨f.base.injective, hb⟩
  have hfin : ∀ s : Finset N.B, ∃ v : Finset M.B, v.map f.base.toEmbedding = s := by
    intro s
    refine ⟨s.map eb.symm.toEmbedding, ?_⟩
    rw [Finset.map_map]
    have he : eb.symm.toEmbedding.trans f.base.toEmbedding = Function.Embedding.refl N.B := by
      ext b
      exact eb.apply_symm_apply b
    rw [he, Finset.map_refl]
  have htup : Function.Surjective (Tuples.map f.index) := (Tuples.mapEquiv ei).surjective
  intro p
  cases p with
  | index i => obtain ⟨j, rfl⟩ := hi i; exact ⟨.index j, rfl⟩
  | base b => obtain ⟨a, rfl⟩ := hb b; exact ⟨.base a, rfl⟩
  | group s => obtain ⟨v, rfl⟩ := hfin s; exact ⟨.group v, rfl⟩
  | star v => exact ⟨.star v, rfl⟩
  | row t n s =>
    obtain ⟨r, rfl⟩ := htup t
    obtain ⟨v, hv⟩ := hfin (f.rowShift r n ∆ s)
    exact ⟨.row r n v, by simp [Map.onPoint, hv]⟩
  | col t b v =>
    obtain ⟨r, rfl⟩ := htup t
    obtain ⟨a, rfl⟩ := hb b
    exact ⟨.col r a (f.colShift r a ∆ v), by simp [Map.onPoint]⟩

def Map.equiv (f : Map M N) (hi : Function.Surjective f.index)
    (hb : Function.Surjective f.base) : M.Carrier ≃ N.Carrier :=
  Equiv.ofBijective f.onPoint ⟨f.injective, f.surjective hi hb⟩

def countableMap [Countable M.B] (ei : M.I ≃ N.I) (eb : M.B ≃o N.B) : Map M N := by
  have h := fun t : Tuple M.I => Matrix.normalize (M.bits t)
    (fun n b => N.bits (Tuples.map ei.toEmbedding t) n (eb b))
  choose U V hUV using h
  exact {
    index := ei.toEmbedding
    base := eb.toOrderEmbedding
    rowShift := fun t n => (U t n).map eb.toOrderEmbedding.toEmbedding
    colShift := V
    bit_agrees := fun t n b => by
      simpa only [Matrix.bit, Finset.mem_map, OrderIso.coe_toOrderEmbedding,
        RelEmbedding.coe_toEmbedding, eb.injective.eq_iff, exists_eq_right] using hUV t n b }

theorem countable_isomorphic [Countable M.B] [Countable N.B] (hI : #M.I = #N.I) :
    ∃ f : Map M N, Function.Surjective f.index ∧ Function.Surjective f.base := by
  obtain ⟨ei⟩ := Cardinal.eq.1 hI
  obtain ⟨eb⟩ := Order.iso_of_countable_dense M.B N.B
  exact ⟨countableMap ei eb, ei.surjective, eb.surjective⟩

theorem Map.strong_of_surjective (f : Map M N) (hCH : CH.{u})
    (hb : Function.Surjective f.base) : f.Strong hCH := by
  constructor
  · rw [Set.range_eq_univ.2 hb]
    exact Set.ordConnected_univ
  · intro t b h
    exact (h (hb b)).elim

theorem Map.object_of_surjective (f : Map M N) (hCH : CH.{u})
    (hi : Function.Surjective f.index) (hb : Function.Surjective f.base)
    (hM : M.IsObject hCH) : N.IsObject hCH := by
  classical
  let ei : M.I ≃ N.I := Equiv.ofBijective f.index ⟨f.index.injective, hi⟩
  intro t
  obtain ⟨r, rfl⟩ := (Tuples.mapEquiv ei).surjective t
  apply ((f.exceptions_countable r).union ((hM r).image f.base)).mono
  intro b hbad
  by_cases he : b ∈ f.exceptions r
  · exact Or.inl he
  · right
    obtain ⟨a, rfl⟩ := hb b
    refine ⟨a, ?_, rfl⟩
    intro hgood
    apply hbad
    apply (f.test_away hCH r (f.base a) he).1
    simpa only [Map.colors_base] using hgood

end Arrays

namespace Tuples

def entriesList {I : Type u} (t : Tuple I) : List I := List.ofFn t.2

theorem entriesList_injective {I : Type u} : Function.Injective (@entriesList I) := by
  rintro ⟨n, a⟩ ⟨m, b⟩ h
  have hn := congrArg List.length h
  simp only [entriesList, List.length_ofFn] at hn
  have he : n = m := Nat.add_right_cancel hn
  subst m
  congr 1
  apply Function.Embedding.ext
  intro i
  have hv := congrArg (fun l : List I => l[i.val]?) h
  simpa only [entriesList, List.getElem?_ofFn, i.isLt, dite_eq_left, Option.some.injEq] using hv

end Tuples

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N : Data.{u}}
local instance : DecidableEq M.B := Classical.decEq M.B
local instance : DecidableEq N.B := Classical.decEq N.B

structure RawEmbedding (M N : Data.{u}) where
  toEmbedding : M.Carrier ↪ N.Carrier
  relates : ∀ s xs, N.rawRel s (xs.map toEmbedding) ↔ M.rawRel s xs
  supports : ∀ (s : Finset M.B) (b : N.B),
    N.rawRel .incidence [.base b, toEmbedding (.group s)] ↔
      ∃ a ∈ s, toEmbedding (.base a) = .base b

variable (f : RawEmbedding M N)

theorem RawEmbedding.index_exists (i : M.I) : ∃ j, f.toEmbedding (.index i) = .index j := by
  have h := (f.relates .index [.index i]).2 trivial
  cases he : f.toEmbedding (.index i) <;> simp_all [Data.rawRel]

theorem RawEmbedding.base_exists (b : M.B) : ∃ c, f.toEmbedding (.base b) = .base c := by
  have h := (f.relates .base [.base b]).2 trivial
  cases he : f.toEmbedding (.base b) <;> simp_all [Data.rawRel]

def RawEmbedding.index (i : M.I) : N.I := (f.index_exists i).choose

def RawEmbedding.base (b : M.B) : N.B := (f.base_exists b).choose

@[simp] theorem RawEmbedding.index_apply (i : M.I) :
    f.toEmbedding (.index i) = .index (f.index i) := (f.index_exists i).choose_spec

@[simp] theorem RawEmbedding.base_apply (b : M.B) :
    f.toEmbedding (.base b) = .base (f.base b) := (f.base_exists b).choose_spec

def RawEmbedding.indexEmb : M.I ↪ N.I where
  toFun := f.index
  inj' a b h := Point.index.inj (f.toEmbedding.injective (by simp only [f.index_apply, h]))

def RawEmbedding.baseEmb : M.B ↪o N.B := OrderEmbedding.ofStrictMono f.base (by
  intro a b hab
  have h := (f.relates .order [.base a, .base b]).2 hab
  simpa only [List.map_cons, List.map_nil, f.base_apply, Data.rawRel] using h)

@[simp] theorem RawEmbedding.indexEmb_apply (i : M.I) : f.indexEmb i = f.index i := rfl
@[simp] theorem RawEmbedding.baseEmb_apply (b : M.B) : f.baseEmb b = f.base b := rfl

@[simp] theorem RawEmbedding.group_apply (s : Finset M.B) :
    f.toEmbedding (.group s) = .group (s.map f.baseEmb.toEmbedding) := by
  have h := (f.relates .group [.group s]).2 trivial
  cases he : f.toEmbedding (.group s) <;> simp only [List.map_cons, List.map_nil, he,
    Data.rawRel] at h
  case group v =>
    congr 1
    ext b
    have hs := f.supports s b
    simp only [he, Data.rawRel, f.base_apply, Point.base.injEq] at hs
    simpa only [Finset.mem_map, RelEmbedding.coe_toEmbedding, RawEmbedding.baseEmb_apply] using hs

@[simp] theorem RawEmbedding.star_apply (v : Finset ℕ) : f.toEmbedding (.star v) = .star v := by
  have h := (f.relates (.label v) [.star v]).2 rfl
  cases he : f.toEmbedding (.star v) <;> simp only [List.map_cons, List.map_nil, he,
    Data.rawRel] at h
  case star w => exact congrArg Point.star h.symm

theorem RawEmbedding.row_exists (t : Tuple M.I) (n : ℕ) (s : Finset M.B) :
    ∃ v, f.toEmbedding (.row t n s) = .row (Tuples.map f.indexEmb t) n v := by
  have hu := (f.relates (.row t.1 n) [.row t n s]).2 ⟨rfl, rfl⟩
  have hp := (f.relates (.rowProjection t.1 n)
    (.row t n s :: List.ofFn (fun i => Point.index (t.2 i)))).2 ⟨rfl, rfl, rfl⟩
  cases he : f.toEmbedding (.row t n s) <;>
    simp only [List.map_cons, List.map_nil, he, Data.rawRel] at hu
  case row r m v =>
    obtain ⟨hk, rfl⟩ := hu
    simp only [List.map_cons, List.map_ofFn, Function.comp_def, he, f.index_apply, Data.rawRel, true_and] at hp
    have ht : r = Tuples.map f.indexEmb t := by
      apply Tuples.entriesList_injective
      apply (show Function.Injective (Point.index (I := N.I) (B := N.B)) from fun _ _ h => Point.index.inj h).list_map
      simp only [Tuples.entriesList, List.map_ofFn]
      exact hp.2.symm
    exact ⟨v, by rw [ht]⟩

theorem RawEmbedding.col_exists (t : Tuple M.I) (b : M.B) (v : Finset ℕ) :
    ∃ w, f.toEmbedding (.col t b v) = .col (Tuples.map f.indexEmb t) (f.base b) w := by
  have hu := (f.relates (.col t.1) [.col t b v]).2 rfl
  have hp := (f.relates (.colProjection t.1)
    (.col t b v :: .base b :: List.ofFn (fun i => Point.index (t.2 i)))).2 ⟨rfl, rfl, rfl⟩
  cases he : f.toEmbedding (.col t b v) <;>
    simp only [List.map_cons, List.map_nil, he, Data.rawRel] at hu
  case col r c w =>
    simp only [List.map_cons, List.map_ofFn, Function.comp_def, he, f.index_apply, f.base_apply, Data.rawRel,
      Point.base.injEq] at hp
    have ht : r = Tuples.map f.indexEmb t := by
      apply Tuples.entriesList_injective
      apply (show Function.Injective (Point.index (I := N.I) (B := N.B)) from fun _ _ h => Point.index.inj h).list_map
      simp only [Tuples.entriesList, List.map_ofFn]
      exact hp.2.2.symm
    exact ⟨w, by rw [ht, ← hp.2.1]⟩

def RawEmbedding.rowShift (t : Tuple M.I) (n : ℕ) : Finset N.B :=
  (f.row_exists t n ∅).choose

def RawEmbedding.colShift (t : Tuple M.I) (b : M.B) : Finset ℕ :=
  (f.col_exists t b ∅).choose

@[simp] theorem RawEmbedding.row_zero (t : Tuple M.I) (n : ℕ) :
    f.toEmbedding (.row t n ∅) = .row (Tuples.map f.indexEmb t) n (f.rowShift t n) :=
  (f.row_exists t n ∅).choose_spec

@[simp] theorem RawEmbedding.col_zero (t : Tuple M.I) (b : M.B) :
    f.toEmbedding (.col t b ∅) = .col (Tuples.map f.indexEmb t) (f.base b) (f.colShift t b) :=
  (f.col_exists t b ∅).choose_spec

@[simp] theorem RawEmbedding.row_apply (t : Tuple M.I) (n : ℕ) (s : Finset M.B) :
    f.toEmbedding (.row t n s) = .row (Tuples.map f.indexEmb t) n
      (f.rowShift t n ∆ s.map f.baseEmb.toEmbedding) := by
  obtain ⟨v, hv⟩ := f.row_exists t n s
  have h := (f.relates .rowAct [.row t n ∅, .group s, .row t n s]).2
    ⟨rfl, rfl, (bot_symmDiff s).symm⟩
  simp only [List.map_cons, List.map_nil, f.row_zero, f.group_apply, hv, Data.rawRel,
    true_and] at h
  rw [hv, h]

@[simp] theorem RawEmbedding.col_apply (t : Tuple M.I) (b : M.B) (v : Finset ℕ) :
    f.toEmbedding (.col t b v) = .col (Tuples.map f.indexEmb t) (f.base b)
      (f.colShift t b ∆ v) := by
  obtain ⟨w, hw⟩ := f.col_exists t b v
  have h := (f.relates .colAct [.col t b ∅, .star v, .col t b v]).2
    ⟨rfl, rfl, (bot_symmDiff v).symm⟩
  simp only [List.map_cons, List.map_nil, f.col_zero, f.star_apply, hw, Data.rawRel,
    true_and] at h
  rw [hw, h]

def RawEmbedding.toMap : Map M N where
  index := f.indexEmb
  base := f.baseEmb
  rowShift := f.rowShift
  colShift := f.colShift
  bit_agrees t n b := by
    have h := f.relates .bit [.row t n ∅, .col t b ∅]
    simp only [List.map_cons, List.map_nil, f.row_zero, f.col_zero, Data.rawRel,
      true_and] at h
    have he : Matrix.bit (M.bits t) n ∅ b ∅ = M.bits t n b := by simp [Matrix.bit]
    rw [he] at h
    exact Bool.eq_iff_iff.2 h

@[simp] theorem RawEmbedding.toMap_onPoint (x : M.Carrier) :
    f.toMap.onPoint x = f.toEmbedding x := by
  cases x <;> simp [RawEmbedding.toMap, Map.onPoint]

end Arrays

end CHObstruction

end

end OAI
