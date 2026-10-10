import OAI.ModelTheory.Categoricity.TailBound

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Matrix

open scoped symmDiff

variable {B : Type u}

local instance : DecidableEq B := Classical.decEq B

def bit (a : ℕ → B → Bool) (n : ℕ) (u : Finset B) (b : B) (v : Finset ℕ) : Bool :=
  a n b ^^ decide (b ∈ u) ^^ decide (n ∈ v)

theorem decompose [Countable B] (d : ℕ → B → Bool) :
    ∃ (U : ℕ → Finset B) (V : B → Finset ℕ),
      ∀ n b, (decide (b ∈ U n) ^^ decide (n ∈ V b)) = d n b := by
  classical
  obtain ⟨e⟩ := nonempty_encodable B
  let ix : B → ℕ := Encodable.encode
  have hi : Function.Injective ix := Encodable.encode_injective
  let U : ℕ → Finset B := fun n =>
    ((Finset.range (n + 1)).preimage ix (hi.injOn)).filter (fun b => d n b)
  let V : B → Finset ℕ := fun b => (Finset.range (ix b)).filter (fun n => d n b)
  refine ⟨U, V, ?_⟩
  intro n b
  simp only [U, V, Finset.mem_filter, Finset.mem_preimage, Finset.mem_range]
  by_cases h : ix b ≤ n
  · have hn : ¬ n < ix b := not_lt_of_ge h
    simp only [Nat.lt_succ_iff, h, hn, true_and, false_and, decide_false, Bool.xor_false,
      Bool.decide_coe]
  · have hn : n < ix b := lt_of_not_ge h
    simp only [Nat.lt_succ_iff, h, hn, true_and, false_and, decide_false, Bool.false_xor,
      Bool.decide_coe]

theorem normalize [Countable B] (a a' : ℕ → B → Bool) :
    ∃ (U : ℕ → Finset B) (V : B → Finset ℕ),
      ∀ n b, bit a' n (U n) b (V b) = a n b := by
  obtain ⟨U, V, h⟩ := decompose (fun n b => a n b ^^ a' n b)
  refine ⟨U, V, ?_⟩
  intro n b
  rw [bit, Bool.xor_assoc, h]
  cases a n b <;> cases a' n b <;> rfl

end Matrix

namespace Arrays

open Tuples
open scoped symmDiff

inductive Point (I B : Type u) : Type u
  | index : I → Point I B
  | base : B → Point I B
  | group : Finset B → Point I B
  | star : Finset ℕ → Point I B
  | row : Tuple I → ℕ → Finset B → Point I B
  | col : Tuple I → B → Finset ℕ → Point I B

inductive Symbol : Type
  | index | base | group | star
  | row (k n : ℕ) | col (k : ℕ) | label (s : Finset ℕ)
  | rowProjection (k n : ℕ) | colProjection (k : ℕ)
  | order | incidence | bit
  | groupAdd | starAdd | rowAct | colAct
  deriving DecidableEq, Encodable

def Symbol.arity : Symbol → ℕ
  | .index | .base | .group | .star | .row _ _ | .col _ | .label _ => 1
  | .rowProjection k _ => k + 2
  | .colProjection k => k + 3
  | .order | .incidence | .bit => 2
  | .groupAdd | .starAdd | .rowAct | .colAct => 3

def Language (n : ℕ) := {s : Symbol // s.arity = n}

instance language_countable : Countable (Σ n, Language n) := by
  have hi : Function.Injective (fun x : Σ n, Language n => x.2.val) := by
    rintro ⟨n, s, hs⟩ ⟨m, r, hr⟩ h
    dsimp at h
    subst r
    cases hs
    cases hr
    rfl
  exact hi.countable

structure Data where
  I : Type u
  B : Type u
  indexNonempty : Nonempty I
  baseNonempty : Nonempty B
  order : LinearOrder B
  dense : @DenselyOrdered B order.toLT
  noMin : @NoMinOrder B order.toLT
  noMax : @NoMaxOrder B order.toLT
  locallyCountable : ∀ a b : B, (@Set.Icc B order.toPreorder a b).Countable
  bits : Tuple I → ℕ → B → Bool

attribute [instance] Data.indexNonempty Data.baseNonempty Data.order Data.dense Data.noMin Data.noMax

abbrev Data.Carrier (M : Data.{u}) := Point M.I M.B

variable (M : Data.{u})

local instance : DecidableEq M.B := Classical.decEq M.B

def Data.rawRel : Symbol → List M.Carrier → Prop
  | .index, [.index _] => True
  | .base, [.base _] => True
  | .group, [.group _] => True
  | .star, [.star _] => True
  | .row k n, [.row t m _] => t.1 = k ∧ m = n
  | .col k, [.col t _ _] => t.1 = k
  | .label s, [.star t] => s = t
  | .rowProjection k n, (.row t m _) :: xs =>
      t.1 = k ∧ m = n ∧ xs = List.ofFn (fun i => Point.index (t.2 i))
  | .colProjection k, (.col t b _) :: x :: xs =>
      t.1 = k ∧ x = .base b ∧ xs = List.ofFn (fun i => Point.index (t.2 i))
  | .order, [.base a, .base b] => a < b
  | .incidence, [.base b, .group s] => b ∈ s
  | .bit, [.row t n s, .col t' b v] => t = t' ∧ Matrix.bit (M.bits t) n s b v = true
  | .groupAdd, [.group s, .group t, .group w] => w = s ∆ t
  | .starAdd, [.star s, .star t, .star w] => w = s ∆ t
  | .rowAct, [.row t n s, .group u, .row t' n' s'] => t' = t ∧ n' = n ∧ s' = s ∆ u
  | .colAct, [.col t b v, .star u, .col t' b' v'] => t' = t ∧ b' = b ∧ v' = v ∆ u
  | _, _ => False

def Data.rel (n : ℕ) (s : Language n) (a : Fin n → M.Carrier) : Prop :=
  M.rawRel s.val (List.ofFn a)

def Data.colors (t : Tuple M.I) (b : M.B) : Colors.Palette.{u} :=
  ⟨Colors.color (fun n => M.bits t n b)⟩

def Data.IsObject (hCH : CH.{u}) : Prop :=
  ∀ t : Tuple M.I, {b | ¬ Tests.Test hCH (fun t => M.colors t b) t}.Countable

theorem Data.countable_object (hCH : CH.{u}) [Countable M.B] : M.IsObject hCH :=
  fun _ => Set.to_countable _

theorem Data.base_bound : #M.B ≤ (ℵ_ 1 : Cardinal.{u}) :=
  BaseOrders.cardinal_le M.locallyCountable

theorem Data.uncountable_index_bound (hCH : CH.{u}) (hM : M.IsObject hCH)
    (hB : ¬ Countable M.B) : #M.I < tailThreshold.{u} :=
  TailBound.index_lt hCH M.base_bound hB M.colors hM

end Arrays

namespace Tuples

variable {I J K : Type u}

def map (f : I ↪ J) (t : Tuple I) : Tuple J := ⟨t.1, t.2.trans f⟩

@[simp] theorem map_fst (f : I ↪ J) (t : Tuple I) : (map f t).1 = t.1 := rfl

theorem map_injective (f : I ↪ J) : Function.Injective (map f) := by
  rintro ⟨n, t⟩ ⟨m, s⟩ heq
  have hn : n = m := congrArg Sigma.fst heq
  subst m
  have he : t.trans f = s.trans f := (Sigma.mk.inj heq).2 |> eq_of_heq
  congr 1
  ext i
  exact f.injective (congrArg (fun g : Fin (n + 1) ↪ J => g i) he)

@[simp] theorem map_refl (t : Tuple I) : map (Function.Embedding.refl I) t = t := by
  cases t
  rfl

@[simp] theorem map_comp (f : I ↪ J) (g : J ↪ K) (t : Tuple I) :
    map g (map f t) = map (f.trans g) t := rfl

@[simp] theorem map_sub (f : I ↪ J) (t : Tuple I) {m : ℕ}
    (e : Fin (m + 1) ↪o Fin (t.1 + 1)) : map f (sub t e) = sub (map f t) e := rfl

theorem cardinal_bound (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hI : #I ≤ κ) : #(Tuple I) ≤ κ := by
  rw [Cardinal.mk_sigma]
  have h : ∀ n : ℕ, #(Fin (n + 1) ↪ I) ≤ κ := by
    intro n
    calc
      #(Fin (n + 1) ↪ I) ≤ #(Fin (n + 1) → I) :=
        Cardinal.mk_le_of_injective DFunLike.coe_injective
      _ = #I ^ ((n + 1 : ℕ) : Cardinal.{u}) := by simp
      _ ≤ κ ^ ((n + 1 : ℕ) : Cardinal.{u}) := Cardinal.power_le_power_right hI
      _ ≤ κ := Cardinal.power_nat_le hκ
  calc
    Cardinal.sum (fun n : ℕ => #(Fin (n + 1) ↪ I)) ≤
        Cardinal.sum (fun _ : ℕ => κ) := Cardinal.sum_le_sum _ _ h
    _ = κ := by
      simp only [Cardinal.sum_const, Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_uzero]
      exact Cardinal.aleph0_mul_eq hκ

end Tuples

namespace FiniteSupports

open scoped symmDiff

variable {A : Type u} {B : Type v} [DecidableEq A] [DecidableEq B]

@[simp] theorem map_symmDiff (f : A ↪ B) (s t : Finset A) :
    (s ∆ t).map f = s.map f ∆ t.map f := by
  ext b
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb
    simp only [Finset.mem_map, Function.Embedding.apply_eq_iff_eq, exists_eq_right,
      Finset.mem_symmDiff]
  · have hn : ∀ s : Finset A, b ∉ s.map f := by
      intro s hs
      obtain ⟨a, _, ha⟩ := Finset.mem_map.1 hs
      exact hb ⟨a, ha⟩
    simp only [hn, Finset.mem_symmDiff, not_false_eq_true, false_and, or_self]

@[simp] theorem bit_symmDiff (b : A) (s t : Finset A) :
    decide (b ∈ s ∆ t) = (decide (b ∈ s) ^^ decide (b ∈ t)) := by
  simp only [Finset.mem_symmDiff]
  by_cases hs : b ∈ s <;> by_cases ht : b ∈ t <;> simp [hs, ht]

@[simp] theorem bit_map (f : A ↪ B) (b : A) (s : Finset A) :
    decide (f b ∈ s.map f) = decide (b ∈ s) := by
  simp

end FiniteSupports

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N : Data.{u}}
local instance : DecidableEq M.B := Classical.decEq M.B
local instance : DecidableEq N.B := Classical.decEq N.B

structure Map (M N : Data.{u}) where
  index : M.I ↪ N.I
  base : M.B ↪o N.B
  rowShift : Tuple M.I → ℕ → Finset N.B
  colShift : Tuple M.I → M.B → Finset ℕ
  bit_agrees : ∀ t n b, Matrix.bit (N.bits (Tuples.map index t)) n (rowShift t n)
    (base b) (colShift t b) = M.bits t n b

def Map.onPoint (f : Map M N) : M.Carrier → N.Carrier
  | .index i => .index (f.index i)
  | .base b => .base (f.base b)
  | .group s => .group (s.map f.base.toEmbedding)
  | .star v => .star v
  | .row t n s => .row (Tuples.map f.index t) n (f.rowShift t n ∆ s.map f.base.toEmbedding)
  | .col t b v => .col (Tuples.map f.index t) (f.base b) (f.colShift t b ∆ v)

theorem Map.injective (f : Map M N) : Function.Injective f.onPoint := by
  intro x y h
  cases x <;> cases y <;> simp only [Map.onPoint, Point.index.injEq, Point.base.injEq,
    Point.group.injEq, Point.star.injEq, Point.row.injEq, Point.col.injEq,
    reduceCtorEq] at h ⊢
  · exact f.index.injective h
  · exact f.base.injective h
  · exact Finset.map_injective _ h
  · exact h
  · obtain ⟨ht, hn, hs⟩ := h
    have ht' := Tuples.map_injective f.index ht
    subst_vars
    exact ⟨rfl, rfl, Finset.map_injective _ (symmDiff_right_inj.1 hs)⟩
  · obtain ⟨ht, hb, hv⟩ := h
    have ht' := Tuples.map_injective f.index ht
    have hb' := f.base.injective hb
    subst_vars
    exact ⟨rfl, rfl, symmDiff_right_inj.1 hv⟩

def Map.toEmbedding (f : Map M N) : M.Carrier ↪ N.Carrier :=
  ⟨f.onPoint, f.injective⟩

@[simp] theorem Map.base_embedding_apply (f : Map M N) (b : M.B) :
    f.base.toEmbedding b = f.base b := rfl

theorem Map.bit_all (f : Map M N) (t : Tuple M.I) (n : ℕ) (s : Finset M.B)
    (b : M.B) (v : Finset ℕ) :
    Matrix.bit (N.bits (Tuples.map f.index t)) n
      (f.rowShift t n ∆ s.map f.base.toEmbedding) (f.base b) (f.colShift t b ∆ v) =
      Matrix.bit (M.bits t) n s b v := by
  have hb := f.bit_agrees t n b
  simp only [Matrix.bit, FiniteSupports.bit_symmDiff, Finset.mem_map,
    Map.base_embedding_apply, f.base.injective.eq_iff, exists_eq_right] at *
  rw [← hb]
  generalize N.bits (Tuples.map f.index t) n (f.base b) = a
  generalize decide (f.base b ∈ f.rowShift t n) = c
  generalize decide (b ∈ s) = d
  generalize decide (n ∈ f.colShift t b) = e
  generalize decide (n ∈ v) = g
  cases a <;> cases c <;> cases d <;> cases e <;> cases g <;> rfl

end Arrays

namespace Tuples

@[simp] theorem map_eq_iff {I J : Type u} (f : I ↪ J) (s t : Tuple I) :
    map f s = map f t ↔ s = t := (map_injective f).eq_iff

end Tuples

end CHObstruction

end

end OAI
