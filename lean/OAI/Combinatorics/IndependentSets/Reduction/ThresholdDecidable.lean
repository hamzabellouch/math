import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.CircleCost
import OAI.Combinatorics.IndependentSets.Reduction.IntegerEdgeTest

namespace OAI

namespace LargeIndependentSets.ShortestPaths
open scoped ENNReal

def thresholdDecidable {Q : Type*} [DecidableEq Q] {M : Q → Type*}
    [∀ q, Fintype (M q)] [∀ q, DecidableEq (M q)]
    (S : ProjectionSystem Q M) [∀ q q' π, Decidable (S.imposed q q' π)]
    {D : ℕ} [NeZero D] {n : ℕ} (e : Fin n ≃ GridLocation M D) (x y : GridLocation M D) :
    Decidable (pathDistance S.linkLength x y ≤ ENNReal.ofReal (1/8)) := by
  have he : pathDistance S.linkLength x y ≤ ENNReal.ofReal (1/8) ↔
      8 * (gridMatrix S e).allPairs.get (e.symm x) (e.symm y) ≤ (D:ℕ∞) := by
    have hd := grid_allPairs_exact S e (e.symm x) (e.symm y)
    simp only [Equiv.apply_symm_apply] at hd
    rw [← hd]
    exact integer_edge_test (D:=D) _
  exact decidable_of_iff _ he.symm

end LargeIndependentSets.ShortestPaths

namespace LargeIndependentSets

structure ExplicitEnum (α : Type*) where
  values : List α
  nodup : values.Nodup
  covers : ∀ a, a ∈ values

namespace ExplicitEnum

def ofCover {α : Type*} [DecidableEq α] (xs : List α) (h : ∀ a, a ∈ xs) : ExplicitEnum α :=
  ⟨xs.dedup,List.nodup_dedup xs,fun a => List.mem_dedup.mpr (h a)⟩

def fin (n : ℕ) : ExplicitEnum (Fin n) :=
  ⟨List.finRange n,List.nodup_finRange n,List.mem_finRange⟩

def sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (ea : ExplicitEnum α) (eb : ExplicitEnum β) : ExplicitEnum (α⊕β) :=
  ofCover (ea.values.map Sum.inl ++ eb.values.map Sum.inr) (by
    intro x
    cases x with
    | inl a => exact List.mem_append_left _ (List.mem_map.mpr ⟨a,ea.covers a,rfl⟩)
    | inr b => exact List.mem_append_right _ (List.mem_map.mpr ⟨b,eb.covers b,rfl⟩))

def prod {α β : Type*} [DecidableEq α] [DecidableEq β]
    (ea : ExplicitEnum α) (eb : ExplicitEnum β) : ExplicitEnum (α×β) :=
  ofCover (ea.values.product eb.values) (fun a => List.mem_product.mpr ⟨ea.covers a.1,eb.covers a.2⟩)

def sigma {α : Type*} [DecidableEq α] {β : α → Type*} [∀ a, DecidableEq (β a)]
    (ea : ExplicitEnum α) (eb : ∀ a, ExplicitEnum (β a)) : ExplicitEnum (Sigma β) :=
  ofCover (ea.values.flatMap (fun a => (eb a).values.map (Sigma.mk a))) (by
    rintro ⟨a,b⟩
    exact List.mem_flatMap.mpr ⟨a,ea.covers a,List.mem_map.mpr ⟨b,(eb a).covers b,rfl⟩⟩)

def pi {α : Type*} [Fintype α] [DecidableEq α] {β : α → Type*} [∀ a, DecidableEq (β a)]
    (ea : ExplicitEnum α) (eb : ∀ a, ExplicitEnum (β a)) : ExplicitEnum (∀ a,β a) :=
  ofCover ((List.pi ea.values (fun a => (eb a).values)).map
    (fun f a => f a (ea.covers a))) (by
      intro f
      apply List.mem_map.mpr
      refine ⟨fun a _ => f a,?_,rfl⟩
      exact (List.mem_pi _ _).mpr (fun a _ => (eb a).covers (f a)))

def subtype {α : Type*} [DecidableEq α] (ea : ExplicitEnum α)
    (P : α → Prop) [DecidablePred P] : ExplicitEnum {a // P a} :=
  ofCover (ea.values.filterMap (fun a => if h : P a then some ⟨a,h⟩ else none)) (by
    rintro ⟨a,ha⟩
    apply List.mem_filterMap.mpr
    exact ⟨a,ea.covers a,by simp [ha]⟩)

def zmod (D : ℕ) [NeZero D] : ExplicitEnum (ZMod D) :=
  ofCover ((List.finRange D).map (fun a => (a.val : ZMod D))) (by
    intro a
    refine List.mem_map.mpr ⟨⟨a.val,ZMod.val_lt a⟩,List.mem_finRange _,?_⟩
    exact ZMod.natCast_zmod_val a)

end ExplicitEnum

def enumerationEquiv {W : Type*} [DecidableEq W] (vertices : List W)
    (nodup : vertices.Nodup) (covers : ∀ w, w ∈ vertices) : Fin vertices.length ≃ W where
  toFun i := vertices[i.val]
  invFun w := ⟨vertices.idxOf w,List.idxOf_lt_length_iff.mpr (covers w)⟩
  left_inv i := by
    apply Fin.ext
    exact nodup.idxOf_getElem i.val i.isLt
  right_inv w := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (covers w))

namespace Graph

def ofEnumeration {W : Type} (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (hn : 0<n) (e : Fin n ≃ W) : Graph where
  vertices := n
  nonempty := hn
  adj i j := decide (H.Adj (e i) (e j))
  symm i j := by simp only [decide_eq_decide]; exact H.adj_comm _ _
  loopless i := by simp

lemma ofEnumeration_colorable {W : Type} (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (hn : 0<n) (e : Fin n ≃ W)
    (h : ∃ color : W → Fin 3, ∀ u v, H.Adj u v → color u ≠ color v) :
    (ofEnumeration H hn e).ThreeColorable := by
  obtain ⟨color,hcolor⟩ := h
  refine ⟨fun i => color (e i),?_⟩
  intro i j hij
  exact hcolor _ _ (of_decide_eq_true hij)

lemma ofEnumeration_independent {W : Type} [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (hn : 0<n) (e : Fin n ≃ W) (A : Finset (Fin n))
    (hA : (ofEnumeration H hn e).Independent A) : H.IsIndepSet (A.image e : Set W) := by
  classical
  intro u hu v hv hne hadj
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
  have hne' : i ≠ j := fun h => hne (congrArg e h)
  have hh := hA i hi j hj hne'
  have ht : (ofEnumeration H hn e).adj i j = true := by exact decide_eq_true hadj
  exact Bool.false_ne_true (hh.symm.trans ht)

end Graph
end LargeIndependentSets

namespace LargeIndependentSets.Graph

theorem ofEnumeration_alpha {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ} (hn : 0<n) (e : Fin n ≃ W)
    {δ : ℝ} (h : ∀ A : Finset W, H.IsIndepSet (A : Set W) →
      (A.card : ℝ) / Fintype.card W < δ) :
    ((ofEnumeration H hn e).independenceNumber : ℝ) < δ * (ofEnumeration H hn e).vertices := by
  obtain ⟨A,hA,he⟩ := (ofEnumeration H hn e).exists_max_independent
  have hh := h (A.image e) (ofEnumeration_independent H hn e A hA)
  have hc : (A.image e).card = A.card := Finset.card_image_of_injective _ e.injective
  have hncard : Fintype.card W = n := by
    simpa using (Fintype.card_congr e).symm
  rw [hc,hncard] at hh
  rw [he]
  exact (div_lt_iff₀ (Nat.cast_pos.mpr hn)).mp hh

end LargeIndependentSets.Graph

end OAI
