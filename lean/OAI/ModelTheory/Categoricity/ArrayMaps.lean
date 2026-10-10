import OAI.ModelTheory.Categoricity.Arrays

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Arrays

section

open Tuples
open scoped symmDiff

variable {M N : Data.{u}} (f : Map M N)
local instance : DecidableEq M.B := Classical.decEq M.B
local instance : DecidableEq N.B := Classical.decEq N.B

private theorem row_action_iff (t t' : Tuple M.I) (n n' : ℕ) (s u s' : Finset M.B) :
    (Tuples.map f.index t' = Tuples.map f.index t ∧ n' = n ∧
      f.rowShift t' n' ∆ s'.map f.base.toEmbedding =
        (f.rowShift t n ∆ s.map f.base.toEmbedding) ∆ u.map f.base.toEmbedding) ↔
      (t' = t ∧ n' = n ∧ s' = s ∆ u) := by
  rw [Tuples.map_eq_iff]
  constructor
  · rintro ⟨rfl, rfl, h⟩
    refine ⟨rfl, rfl, ?_⟩
    rw [symmDiff_assoc, ← FiniteSupports.map_symmDiff, symmDiff_right_inj] at h
    exact Finset.map_injective _ h
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, by rw [FiniteSupports.map_symmDiff, symmDiff_assoc]⟩

private theorem col_action_iff (t t' : Tuple M.I) (b b' : M.B) (v u v' : Finset ℕ) :
    (Tuples.map f.index t' = Tuples.map f.index t ∧ f.base b' = f.base b ∧
      f.colShift t' b' ∆ v' = (f.colShift t b ∆ v) ∆ u) ↔
      (t' = t ∧ b' = b ∧ v' = v ∆ u) := by
  rw [Tuples.map_eq_iff, f.base.injective.eq_iff]
  constructor
  · rintro ⟨rfl, rfl, h⟩
    exact ⟨rfl, rfl, by simpa only [symmDiff_assoc, symmDiff_right_inj] using h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, (symmDiff_assoc _ _ _).symm⟩

private theorem bit_relation_iff (t t' : Tuple M.I) (n : ℕ) (b : M.B)
    (s : Finset M.B) (v : Finset ℕ) :
    (Tuples.map f.index t = Tuples.map f.index t' ∧
      Matrix.bit (N.bits (Tuples.map f.index t)) n
        (f.rowShift t n ∆ s.map f.base.toEmbedding) (f.base b) (f.colShift t' b ∆ v) = true) ↔
      (t = t' ∧ Matrix.bit (M.bits t) n s b v = true) := by
  rw [Tuples.map_eq_iff]
  constructor
  · rintro ⟨rfl, hb⟩
    exact ⟨rfl, by simpa only [f.bit_all] using hb⟩
  · rintro ⟨rfl, hb⟩
    exact ⟨rfl, by simpa only [f.bit_all] using hb⟩

private theorem group_add_iff (s t w : Finset M.B) :
    w.map f.base.toEmbedding = s.map f.base.toEmbedding ∆ t.map f.base.toEmbedding ↔
      w = s ∆ t := by
  rw [← FiniteSupports.map_symmDiff]
  exact (Finset.map_injective _).eq_iff

attribute [local simp] Data.rawRel Map.onPoint group_add_iff row_action_iff
  col_action_iff bit_relation_iff

private theorem raw_map_index (xs : List M.Carrier) :
    N.rawRel (.index) (xs.map f.onPoint) ↔ M.rawRel (.index) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

private theorem raw_map_base (xs : List M.Carrier) :
    N.rawRel (.base) (xs.map f.onPoint) ↔ M.rawRel (.base) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

private theorem raw_map_group (xs : List M.Carrier) :
    N.rawRel (.group) (xs.map f.onPoint) ↔ M.rawRel (.group) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

private theorem raw_map_star (xs : List M.Carrier) :
    N.rawRel (.star) (xs.map f.onPoint) ↔ M.rawRel (.star) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

private theorem raw_map_row (k n : ℕ) (xs : List M.Carrier) :
    N.rawRel (.row k n) (xs.map f.onPoint) ↔ M.rawRel (.row k n) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

private theorem raw_map_col (k : ℕ) (xs : List M.Carrier) :
    N.rawRel (.col k) (xs.map f.onPoint) ↔ M.rawRel (.col k) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

private theorem raw_map_label (s : Finset ℕ) (xs : List M.Carrier) :
    N.rawRel (.label s) (xs.map f.onPoint) ↔ M.rawRel (.label s) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> simp
  · cases x <;> simp

private theorem raw_map_order (xs : List M.Carrier) :
    N.rawRel (.order) (xs.map f.onPoint) ↔ M.rawRel (.order) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> simp
  · cases x <;> cases y <;> simp

private theorem raw_map_incidence (xs : List M.Carrier) :
    N.rawRel (.incidence) (xs.map f.onPoint) ↔ M.rawRel (.incidence) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> simp
  · cases x <;> cases y <;> simp

private theorem raw_map_bit (xs : List M.Carrier) :
    N.rawRel (.bit) (xs.map f.onPoint) ↔ M.rawRel (.bit) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> simp
    rintro rfl
    exact f.bit_all _ _ _ _ _
  · cases x <;> cases y <;> simp

private theorem raw_map_groupAdd (xs : List M.Carrier) :
    N.rawRel (.groupAdd) (xs.map f.onPoint) ↔ M.rawRel (.groupAdd) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨z, xs⟩
  · cases x <;> cases y <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> cases z <;> simp
  · cases x <;> cases y <;> cases z <;> simp

private theorem raw_map_starAdd (xs : List M.Carrier) :
    N.rawRel (.starAdd) (xs.map f.onPoint) ↔ M.rawRel (.starAdd) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨z, xs⟩
  · cases x <;> cases y <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> cases z <;> simp
  · cases x <;> cases y <;> cases z <;> simp

private theorem raw_map_rowAct (xs : List M.Carrier) :
    N.rawRel (.rowAct) (xs.map f.onPoint) ↔ M.rawRel (.rowAct) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨z, xs⟩
  · cases x <;> cases y <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> cases z <;> simp
    rintro rfl rfl
    rw [symmDiff_assoc, ← FiniteSupports.map_symmDiff, symmDiff_right_inj]
    exact (Finset.map_injective _).eq_iff
  · cases x <;> cases y <;> cases z <;> simp

private theorem raw_map_colAct (xs : List M.Carrier) :
    N.rawRel (.colAct) (xs.map f.onPoint) ↔ M.rawRel (.colAct) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, xs⟩
  · cases x <;> simp
  rcases xs with _ | ⟨z, xs⟩
  · cases x <;> cases y <;> simp
  rcases xs with _ | ⟨q, qs⟩
  · cases x <;> cases y <;> cases z <;> simp
    rintro rfl rfl
    rw [symmDiff_assoc, symmDiff_right_inj]
  · cases x <;> cases y <;> cases z <;> simp

private theorem tuple_list_eq_iff (t : Tuple M.I) (xs : List M.Carrier) :
    xs.map f.onPoint = List.ofFn (fun i => Point.index ((Tuples.map f.index t).2 i)) ↔
      xs = List.ofFn (fun i => Point.index (t.2 i)) := by
  have he : List.ofFn (fun i => Point.index ((Tuples.map f.index t).2 i)) =
      (List.ofFn (fun i => Point.index (t.2 i))).map f.onPoint := by
    rw [List.map_ofFn]
    rfl
  rw [he]
  exact f.injective.list_map.eq_iff

private theorem base_point_eq_iff (x : M.Carrier) (b : M.B) :
    f.onPoint x = Point.base (f.base b) ↔ x = Point.base b := by
  change f.onPoint x = f.onPoint (.base b) ↔ _
  exact f.injective.eq_iff

private theorem raw_map_rowProjection (k n : ℕ) (xs : List M.Carrier) :
    N.rawRel (.rowProjection k n) (xs.map f.onPoint) ↔ M.rawRel (.rowProjection k n) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  cases x <;> simp
  intro _ _
  simpa only [Tuples.map, List.ofFn_succ] using tuple_list_eq_iff f _ xs

private theorem raw_map_colProjection (k : ℕ) (xs : List M.Carrier) :
    N.rawRel (.colProjection k) (xs.map f.onPoint) ↔ M.rawRel (.colProjection k) xs := by
  rcases xs with _ | ⟨x, xs⟩
  · simp
  rcases xs with _ | ⟨y, ys⟩
  · cases x <;> simp
  cases x <;> simp
  intro _
  exact and_congr (base_point_eq_iff f y _) (by
    simpa only [Tuples.map, List.ofFn_succ] using tuple_list_eq_iff f _ ys)

theorem Map.rawRel (s : Symbol) (xs : List M.Carrier) :
    N.rawRel s (xs.map f.onPoint) ↔ M.rawRel s xs := by
  cases s with
  | index => exact raw_map_index f xs
  | base => exact raw_map_base f xs
  | group => exact raw_map_group f xs
  | star => exact raw_map_star f xs
  | row k n => exact raw_map_row f k n xs
  | col k => exact raw_map_col f k xs
  | label v => exact raw_map_label f v xs
  | rowProjection k n => exact raw_map_rowProjection f k n xs
  | colProjection k => exact raw_map_colProjection f k xs
  | order => exact raw_map_order f xs
  | incidence => exact raw_map_incidence f xs
  | bit => exact raw_map_bit f xs
  | groupAdd => exact raw_map_groupAdd f xs
  | starAdd => exact raw_map_starAdd f xs
  | rowAct => exact raw_map_rowAct f xs
  | colAct => exact raw_map_colAct f xs

theorem Map.rel (n : ℕ) (s : Language n) (a : Fin n → M.Carrier) :
    N.rel n s (f.onPoint ∘ a) ↔ M.rel n s a := by
  simpa only [Data.rel, List.map_ofFn] using f.rawRel s.val (List.ofFn a)

end

open Tuples
open scoped symmDiff

variable {M N P : Data.{u}}
local instance : DecidableEq M.B := Classical.decEq M.B
local instance : DecidableEq N.B := Classical.decEq N.B
local instance : DecidableEq P.B := Classical.decEq P.B

def Map.id (M : Data.{u}) : Map M M where
  index := Function.Embedding.refl _
  base := (OrderIso.refl _).toOrderEmbedding
  rowShift _ _ := ∅
  colShift _ _ := ∅
  bit_agrees t n b := by simp [Matrix.bit]

def Map.comp (g : Map N P) (f : Map M N) : Map M P where
  index := f.index.trans g.index
  base := f.base.trans g.base
  rowShift t n := g.rowShift (Tuples.map f.index t) n ∆
    (f.rowShift t n).map g.base.toEmbedding
  colShift t b := g.colShift (Tuples.map f.index t) (f.base b) ∆ f.colShift t b
  bit_agrees t n b := by
    exact (g.bit_all (Tuples.map f.index t) n (f.rowShift t n) (f.base b)
      (f.colShift t b)).trans (f.bit_agrees t n b)

@[simp] theorem Map.id_onPoint (M : Data.{u}) (x : M.Carrier) : (Map.id M).onPoint x = x := by
  have he : (OrderIso.refl M.B).toOrderEmbedding.toEmbedding = Function.Embedding.refl M.B := rfl
  cases x <;> simp [Map.id, Map.onPoint, he]

@[simp] theorem Map.comp_onPoint (g : Map N P) (f : Map M N) (x : M.Carrier) :
    (g.comp f).onPoint x = g.onPoint (f.onPoint x) := by
  have he : (f.base.trans g.base).toEmbedding = f.base.toEmbedding.trans g.base.toEmbedding := rfl
  cases x <;> simp [Map.comp, Map.onPoint, Finset.map_map, symmDiff_assoc, he]

theorem Map.ext_onPoint {f g : Map M N} (h : ∀ x, f.onPoint x = g.onPoint x) : f = g := by
  have hi : f.index = g.index := by
    ext i
    exact Point.index.inj (h (.index i))
  have hb : f.base = g.base := by
    ext b
    exact Point.base.inj (h (.base b))
  have hr : f.rowShift = g.rowShift := by
    funext t n
    have he := (Point.row.inj (h (.row t n ∅))).2.2
    simpa using he
  have hc : f.colShift = g.colShift := by
    funext t b
    have he := (Point.col.inj (h (.col t b ∅))).2.2
    simpa using he
  cases f
  cases g
  cases hi
  cases hb
  cases hr
  cases hc
  rfl

@[simp] theorem Map.comp_id (f : Map M N) : f.comp (Map.id M) = f :=
  Map.ext_onPoint (fun x => by simp)

@[simp] theorem Map.id_comp (f : Map M N) : (Map.id N).comp f = f :=
  Map.ext_onPoint (fun x => by simp)

end Arrays

end CHObstruction

end

end OAI
