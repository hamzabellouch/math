import OAI.ModelTheory.Categoricity.Subarrays

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N P : Data.{u}}
local instance : DecidableEq M.B := Classical.decEq M.B
local instance : DecidableEq N.B := Classical.decEq N.B
local instance : DecidableEq P.B := Classical.decEq P.B

structure RawIso (M N : Data.{u}) where
  toEquiv : M.Carrier ≃ N.Carrier
  relates : ∀ s xs, N.rawRel s (xs.map toEquiv) ↔ M.rawRel s xs

variable (e : RawIso M N)

theorem RawIso.base_surjective_point (b : N.B) : ∃ a, e.toEquiv (.base a) = .base b := by
  obtain ⟨x, hx⟩ := e.toEquiv.surjective (.base b)
  have h := (e.relates .base [x]).1 (by simp only [List.map_cons, List.map_nil, hx, Data.rawRel])
  cases x <;> simp only [Data.rawRel] at h
  case base a => exact ⟨a, hx⟩

theorem RawIso.index_surjective_point (b : N.I) : ∃ a, e.toEquiv (.index a) = .index b := by
  obtain ⟨x, hx⟩ := e.toEquiv.surjective (.index b)
  have h := (e.relates .index [x]).1 (by simp only [List.map_cons, List.map_nil, hx, Data.rawRel])
  cases x <;> simp only [Data.rawRel] at h
  case index a => exact ⟨a, hx⟩

def RawIso.toRawEmbedding : RawEmbedding M N where
  toEmbedding := e.toEquiv.toEmbedding
  relates := e.relates
  supports s b := by
    obtain ⟨a, ha⟩ := e.base_surjective_point b
    have hr := e.relates .incidence [.base a, .group s]
    simp only [List.map_cons, List.map_nil, ha] at hr
    change N.rawRel .incidence [.base b, e.toEquiv (.group s)] ↔ a ∈ s at hr
    change N.rawRel .incidence [.base b, e.toEquiv (.group s)] ↔ _
    rw [hr]
    constructor
    · intro h; exact ⟨a, h, ha⟩
    · rintro ⟨c, hc, he⟩
      have hca : c = a := Point.base.inj (e.toEquiv.injective (he.trans ha.symm))
      exact hca ▸ hc

def RawIso.toMap : Map M N := e.toRawEmbedding.toMap

theorem RawIso.toMap_onPoint (x : M.Carrier) : e.toMap.onPoint x = e.toEquiv x :=
  e.toRawEmbedding.toMap_onPoint x

theorem RawIso.base_surjective : Function.Surjective e.toMap.base := by
  intro b
  obtain ⟨a, ha⟩ := e.base_surjective_point b
  refine ⟨a, Point.base.inj (I := N.I) ?_⟩
  exact (e.toMap_onPoint (.base a)).trans ha

theorem RawIso.index_surjective : Function.Surjective e.toMap.index := by
  intro b
  obtain ⟨a, ha⟩ := e.index_surjective_point b
  refine ⟨a, Point.index.inj (B := N.B) ?_⟩
  exact (e.toMap_onPoint (.index a)).trans ha

theorem Map.factor (f : Map M P) (g : Map N P)
    (h : ∀ x : M.Carrier, ∃ y, g.onPoint y = f.onPoint x) :
    ∃ k : Map M N, g.comp k = f := by
  let ef : M.Carrier → N.Carrier := fun x => (h x).choose
  have hef (x) : g.onPoint (ef x) = f.onPoint x := (h x).choose_spec
  have hinj : Function.Injective ef := by
    intro a b hab
    apply f.injective
    rw [← hef a, ← hef b, hab]
  let r : RawEmbedding M N := {
    toEmbedding := ⟨ef, hinj⟩
    relates := by
      intro s xs
      have he : (xs.map ef).map g.onPoint = xs.map f.onPoint := by
        rw [List.map_map]
        exact List.map_congr_left (fun x _ => hef x)
      change N.rawRel s (xs.map ef) ↔ M.rawRel s xs
      rw [← g.rawRel s (xs.map ef), he, f.rawRel]
    supports := by
      intro s b
      have hr := g.rawRel .incidence [.base b, ef (.group s)]
      simp only [List.map_cons, List.map_nil] at hr
      rw [hef] at hr
      change g.base b ∈ s.map f.base.toEmbedding ↔
        N.rawRel .incidence [.base b, ef (.group s)] at hr
      change N.rawRel .incidence [.base b, ef (.group s)] ↔
        ∃ a ∈ s, ef (.base a) = .base b
      rw [← hr]
      constructor
      · intro hb
        obtain ⟨a, has, ha⟩ := Finset.mem_map.1 hb
        refine ⟨a, has, g.injective ?_⟩
        rw [hef]
        exact congrArg Point.base ha
      · rintro ⟨a, has, ha⟩
        refine Finset.mem_map.2 ⟨a, has, ?_⟩
        have he := hef (.base a)
        rw [ha] at he
        exact Point.base.inj he.symm }
  refine ⟨r.toMap, Map.ext_onPoint (fun x => ?_)⟩
  rw [Map.comp_onPoint, r.toMap_onPoint]
  exact hef x

theorem Map.Strong.factor (hCH : CH.{u}) {f : Map M P} {g : Map N P} {k : Map M N}
    (hf : f.Strong hCH) (he : g.comp k = f) : k.Strong hCH := by
  have hb (a : M.B) : g.base (k.base a) = f.base a := by
    have h := congrArg (fun l : Map M P => l.base a) he
    exact h
  constructor
  · constructor
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩ z ⟨haz, hzb⟩
    have hgz : g.base z ∈ Set.Icc (f.base a) (f.base b) := by
      rw [← hb, ← hb]
      exact ⟨g.base.monotone haz, g.base.monotone hzb⟩
    obtain ⟨c, hc⟩ := hf.convex.out ⟨a, rfl⟩ ⟨b, rfl⟩ hgz
    exact ⟨c, g.base.injective ((hb c).trans hc)⟩
  · intro t b hnb
    have hn : g.base b ∉ Set.range f.base := by
      rintro ⟨a, ha⟩
      exact hnb ⟨a, g.base.injective ((hb a).trans ha)⟩
    have ht := hf.outside t (g.base b) hn
    rw [← he] at ht
    simpa only [Map.comp_colors_base] using ht

end Arrays

namespace CardinalTools

theorem union_le {X A : Type u} (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (hA : #A ≤ κ) (s : A → Set X) (hs : ∀ a, #(s a) ≤ κ) : #(⋃ a, s a) ≤ κ := by
  apply Cardinal.mk_iUnion_le_sum_mk.trans
  apply (Cardinal.sum_le_sum _ _ hs).trans
  simpa only [Cardinal.sum_const, Cardinal.lift_id, Cardinal.mul_eq_self hκ] using
    (mul_le_mul' hA (le_refl κ))

end CardinalTools

namespace Arrays

open Tuples
open scoped symmDiff

variable {M : Data.{u}}
local instance : DecidableEq M.I := Classical.decEq M.I
local instance : DecidableEq M.B := Classical.decEq M.B

def Point.indexSupport : M.Carrier → Finset M.I
  | .index i => {i}
  | .row t _ _ | .col t _ _ => (Finset.univ.map t.2)
  | _ => ∅

def Point.baseSupport : M.Carrier → Finset M.B
  | .base b | .col _ b _ => {b}
  | .group s | .row _ _ s => s
  | _ => ∅

theorem Data.restrictMap_range (J : Set M.I) (S : Set M.B) [Nonempty J] [Nonempty S]
    [DenselyOrdered S] [NoMinOrder S] [NoMaxOrder S] (x : M.Carrier)
    (hi : ↑x.indexSupport ⊆ J) (hb : ↑x.baseSupport ⊆ S) :
    x ∈ Set.range (M.restrictMap J S).onPoint := by
  classical
  have ht (t : Tuple M.I) (h : ↑((Finset.univ.map t.2)) ⊆ J) :
      ∃ r : Tuple J, Tuples.map (Function.Embedding.subtype J) r = t := by
    let r : Tuple J := ⟨t.1, ⟨fun i => ⟨t.2 i, h (Finset.mem_map.2 ⟨i, Finset.mem_univ i, rfl⟩)⟩,
      fun a b he => t.2.injective (congrArg Subtype.val he)⟩⟩
    exact ⟨r, rfl⟩
  have hs (s : Finset M.B) (h : ↑s ⊆ S) :
      (s.subtype (· ∈ S)).map (OrderEmbedding.subtype S).toEmbedding = s :=
    Finset.subtype_map_of_mem (p := fun x => x ∈ S) (fun _ ha => h ha)
  cases x with
  | index i => exact ⟨.index ⟨i, hi (Finset.mem_singleton_self i)⟩, rfl⟩
  | base b => exact ⟨.base ⟨b, hb (Finset.mem_singleton_self b)⟩, rfl⟩
  | group s => exact ⟨.group (s.subtype (· ∈ S)), congrArg Point.group (hs s hb)⟩
  | star v => exact ⟨.star v, rfl⟩
  | row t n s =>
    obtain ⟨r, hr⟩ := ht t hi
    refine ⟨.row r n (s.subtype (· ∈ S)), ?_⟩
    change Point.row (Tuples.map (Function.Embedding.subtype J) r) n
      (∅ ∆ (s.subtype (· ∈ S)).map (OrderEmbedding.subtype S).toEmbedding) = _
    rw [hr, hs s hb]
    simp
  | col t b v =>
    obtain ⟨r, hr⟩ := ht t hi
    refine ⟨.col r ⟨b, hb (Finset.mem_singleton_self b)⟩ v, ?_⟩
    change Point.col (Tuples.map (Function.Embedding.subtype J) r) b (∅ ∆ v) = _
    rw [hr]
    simp

theorem Data.small_subarray (M : Data.{u}) (hCH : CH.{u}) (hM : M.IsObject hCH)
    (A : Set M.Carrier) :
    ∃ N : Data.{u}, ∃ f : Map N M, N.IsObject hCH ∧ f.Strong hCH ∧
      A ⊆ Set.range f.onPoint ∧ #N.Carrier ≤ #A + ℵ₀ := by
  classical
  let κ : Cardinal.{u} := #A + ℵ₀
  have hκ : ℵ₀ ≤ κ := le_add_self
  have hA : #A ≤ κ := le_self_add
  let p : M.I := Classical.arbitrary M.I
  let J : Set M.I := (⋃ a : A, (a.val.indexSupport : Set M.I)) ∪ {p}
  have hJ : #J ≤ κ := by
    apply (Cardinal.mk_union_le _ _).trans
    apply Cardinal.add_le_of_le hκ
    · exact CardinalTools.union_le κ hκ hA _ (fun a =>
        (Cardinal.mk_le_aleph0_iff.2 (a.val.indexSupport.countable_toSet)).trans hκ)
    · simpa only [Cardinal.mk_singleton] using Cardinal.one_le_aleph0.trans hκ
  let : Nonempty J := ⟨⟨p, Or.inr rfl⟩⟩
  let T : Set M.B := (⋃ a : A, (a.val.baseSupport : Set M.B)) ∪
    (⋃ t : Tuple J, {b | ¬ Tests.Test hCH (fun r => M.colors r b)
      (Tuples.map (Function.Embedding.subtype J) t)})
  have hT : #T ≤ κ := by
    apply (Cardinal.mk_union_le _ _).trans
    apply Cardinal.add_le_of_le hκ
    · exact CardinalTools.union_le κ hκ hA _ (fun a =>
        (Cardinal.mk_le_aleph0_iff.2 (a.val.baseSupport.countable_toSet)).trans hκ)
    · exact CardinalTools.union_le κ hκ (Tuples.cardinal_bound κ hκ hJ) _
        (fun t => (Cardinal.mk_le_aleph0_iff.2 (hM _)).trans hκ)
  obtain ⟨S, hTS, hc, hn, hmin, hmax, hd, hS⟩ :=
    BaseOrders.small_hull M.locallyCountable T κ hκ hT
  let : Nonempty S := hn
  let : NoMinOrder S := hmin
  let : NoMaxOrder S := hmax
  let : DenselyOrdered S := hd
  refine ⟨M.restrict J S, M.restrictMap J S, M.restrict_object J S hCH hM,
    M.restrict_strong J S hCH hc ?_, ?_, ?_⟩
  · intro t b hb
    exact hTS (Or.inr (Set.mem_iUnion.2 ⟨t, hb⟩))
  · intro x hx
    apply Data.restrictMap_range J S x
    · intro i hi
      exact Or.inl (Set.mem_iUnion.2 ⟨⟨x, hx⟩, hi⟩)
    · intro b hb
      exact hTS (Or.inl (Set.mem_iUnion.2 ⟨⟨x, hx⟩, hb⟩))
  · exact Data.cardinal_le κ hκ hJ hS

end Arrays

end CHObstruction

end

end OAI
