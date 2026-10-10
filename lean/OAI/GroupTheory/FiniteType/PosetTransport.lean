import Mathlib
import OAI.GroupTheory.FiniteType.OrderChainsExactInOfDirected

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace PosetTransport
section
universe u v w
variable {P : Type u} [Preorder P] {Q : Type v} [Preorder Q]
variable {H : Type w} [Group H]
structure Cocycle (P : Type u) [Preorder P] (H : Type w) [Group H] where
  edge : ∀ {x y : P}, x ≤ y → H
  refl : ∀ x, edge (le_refl x) = 1
  comp : ∀ {x y z : P} (h : x ≤ y) (k : y ≤ z), edge h * edge k = edge (h.trans k)
namespace Cocycle
@[ext] lemma ext {c d : Cocycle P H}
    (h : ∀ {x y} (hxy : x ≤ y), c.edge hxy = d.edge hxy) : c = d := by
  cases c with
  | mk e r k =>
    cases d with
    | mk e' r' k' =>
      have he : @e = @e' := by funext x y hxy; exact h hxy
      subst e'
      rfl
variable (c : Cocycle P H)
def Potential (v : P → H) : Prop := ∀ {x y}, (h : x ≤ y) → v x * c.edge h = v y
def Trivial : Prop := ∃ v : P → H, c.Potential v
def pull (f : Q →o P) : Cocycle Q H where
  edge h := c.edge (f.monotone h)
  refl x := c.refl (f x)
  comp h k := c.comp (f.monotone h) (f.monotone k)
lemma trivial_pull (hc : c.Trivial) (f : Q →o P) : (c.pull f).Trivial := by
  obtain ⟨v,hv⟩ := hc
  exact ⟨v ∘ f,fun h => hv (f.monotone h)⟩
lemma square (f g : Q →o P) (h : ∀ x, f x ≤ g x) {x y : Q} (hxy : x ≤ y) :
    c.edge (h x) * c.edge (g.monotone hxy) =
      c.edge (f.monotone hxy) * c.edge (h y) := by
  rw [c.comp,c.comp]
lemma trivial_compare (f g : Q →o P) (h : ∀ x, f x ≤ g x)
    (hf : (c.pull f).Trivial) : (c.pull g).Trivial := by
  obtain ⟨v,hv⟩ := hf
  refine ⟨fun x => v x * c.edge (h x),?_⟩
  intro x y hxy
  change (v x * c.edge (h x)) * c.edge (g.monotone hxy) = v y * c.edge (h y)
  rw [mul_assoc,c.square f g h hxy,← mul_assoc]
  rw [show v x * c.edge (f.monotone hxy) = v y from hv hxy]
lemma trivial_compare_rev (f g : Q →o P) (h : ∀ x, f x ≤ g x)
    (hg : (c.pull g).Trivial) : (c.pull f).Trivial := by
  obtain ⟨v,hv⟩ := hg
  refine ⟨fun x => v x * (c.edge (h x))⁻¹,?_⟩
  intro x y hxy
  change (v x * (c.edge (h x))⁻¹) * c.edge (f.monotone hxy) =
    v y * (c.edge (h y))⁻¹
  apply mul_right_cancel (b := c.edge (h y))
  rw [mul_assoc,mul_assoc,← c.square f g h hxy,← mul_assoc (c.edge (h x))⁻¹,
    inv_mul_cancel,one_mul]
  simpa only [pull,mul_assoc,inv_mul_cancel,mul_one] using hv hxy
lemma trivial_of_top (t : P) (ht : ∀ x, x ≤ t) : c.Trivial := by
  refine ⟨fun x => (c.edge (ht x))⁻¹,?_⟩
  intro x y hxy
  apply mul_right_cancel (b := c.edge (ht y))
  rw [mul_assoc,c.comp,inv_mul_cancel,inv_mul_cancel]
lemma trivial_of_bottom (t : P) (ht : ∀ x, t ≤ x) : c.Trivial := by
  exact ⟨fun x => c.edge (ht x),fun h => c.comp _ h⟩
end Cocycle

def Adj (x y : P) : Prop := x ≤ y ∨ y ≤ x
def Connected (P : Type u) [Preorder P] : Prop :=
  ∀ x y : P, Relation.ReflTransGen Adj x y
lemma Connected.constant (h : Connected P) {Y : Type*} (f : P → Y)
    (hf : ∀ {x y}, x ≤ y → f x = f y) (x y : P) : f x = f y := by
  induction h x y with
  | refl => rfl
  | @tail b d hxb hbd ih =>
    exact ih.trans (hbd.elim hf (fun hh => (hf hh).symm))
lemma connected_of_bottom (t : P) (ht : ∀ x, t ≤ x) : Connected P := by
  intro x y
  exact (Relation.ReflTransGen.single (show Adj x t from Or.inr (ht x))).trans
    (Relation.ReflTransGen.single (show Adj t y from Or.inl (ht y)))
lemma connected_of_top (t : P) (ht : ∀ x, x ≤ t) : Connected P := by
  intro x y
  exact (Relation.ReflTransGen.single (show Adj x t from Or.inl (ht x))).trans
    (Relation.ReflTransGen.single (show Adj t y from Or.inr (ht y)))

theorem Cocycle.trivial_of_lower_fibers (c : Cocycle P H) (f : Q →o P)
    (hne : ∀ p : P, ∃ q : Q, f q ≤ p)
    (hconn : ∀ p : P, Connected {q : Q // f q ≤ p})
    (hq : (c.pull f).Trivial) : c.Trivial := by
  classical
  obtain ⟨v,hv⟩ := hq
  choose q hq using hne
  let rv (p : P) (x : {q : Q // f q ≤ p}) : H := v x.val * c.edge x.property
  have hrv (p : P) (x y : {q : Q // f q ≤ p}) : rv p x = rv p y := by
    apply (hconn p).constant (rv p) ?_ x y
    intro a b hab
    dsimp [rv]
    rw [← c.comp (f.monotone hab) b.property,← mul_assoc]
    rw [show v a.val * c.edge (f.monotone hab) = v b.val from hv hab]
  refine ⟨fun p => rv p ⟨q p,hq p⟩,?_⟩
  intro x y hxy
  change (v (q x) * c.edge (hq x)) * c.edge hxy = rv y ⟨q y,hq y⟩
  rw [mul_assoc,c.comp]
  exact hrv y ⟨q x,(hq x).trans hxy⟩ ⟨q y,hq y⟩

lemma connected_of_constant
    (h : ∀ f : P → Bool, (∀ {x y}, x ≤ y → f x = f y) → ∀ x y, f x = f y) :
    Connected P := by
  classical
  intro x y
  let f (z : P) : Bool := decide (Relation.ReflTransGen Adj x z)
  have hf : ∀ {a b : P}, a ≤ b → f a = f b := by
    intro a b hab
    have he : Relation.ReflTransGen Adj x a ↔ Relation.ReflTransGen Adj x b := by
      constructor
      · intro ha
        exact ha.tail (show Adj a b from Or.inl hab)
      · intro hb
        exact hb.tail (show Adj b a from Or.inr hab)
    simp only [f,he]
  have he := h f hf x y
  have hx : f x = true := by
    simp only [f,decide_eq_true_eq]
    exact Relation.ReflTransGen.refl
  have hy : f y = true := he.symm.trans hx
  exact of_decide_eq_true hy

lemma Connected.of_orderIso (h : Connected P) (e : P ≃o Q) : Connected Q := by
  apply connected_of_constant
  intro f hf x y
  simpa only [Function.comp_apply,e.apply_symm_apply] using
    h.constant (f ∘ e) (fun hab => hf (e.monotone hab)) (e.symm x) (e.symm y)

theorem Cocycle.trivial_of_upper_fibers (c : Cocycle P H) (f : Q →o P)
    (hne : ∀ p : P, ∃ q : Q, p ≤ f q)
    (hconn : ∀ p : P, Connected {q : Q // p ≤ f q})
    (hq : (c.pull f).Trivial) : c.Trivial := by
  classical
  obtain ⟨v,hv⟩ := hq
  choose q hq using hne
  let rv (p : P) (x : {q : Q // p ≤ f q}) : H := v x.val * (c.edge x.property)⁻¹
  have hrv (p : P) (x y : {q : Q // p ≤ f q}) : rv p x = rv p y := by
    apply (hconn p).constant (rv p) ?_ x y
    intro a b hab
    dsimp [rv]
    apply mul_right_cancel (b := c.edge b.property)
    rw [mul_assoc,← c.comp a.property (f.monotone hab),
      ← mul_assoc (c.edge a.property)⁻¹,inv_mul_cancel,one_mul]
    simpa only [mul_assoc,inv_mul_cancel,mul_one,pull] using hv hab
  refine ⟨fun p => rv p ⟨q p,hq p⟩,?_⟩
  intro x y hxy
  have he := hrv x ⟨q x,hq x⟩ ⟨q y,hxy.trans (hq y)⟩
  change rv x ⟨q x,hq x⟩ * c.edge hxy = rv y ⟨q y,hq y⟩
  rw [he]
  dsimp [rv]
  rw [← c.comp hxy (hq y),mul_inv_rev,mul_assoc,mul_assoc,inv_mul_cancel,mul_one]

section Rank
variable {R : Type*} [PartialOrder R]
def rankAbove (r : R → ℕ) (m : ℕ) : Set R := {x | m ≤ r x}
def rankEmbed (r : R → ℕ) (m : ℕ) : rankAbove r m →o R where
  toFun := Subtype.val
  monotone' := fun _ _ h => h

def rankStep (r : R → ℕ) (m : ℕ) : rankAbove r (m+1) →o rankAbove r m where
  toFun x := ⟨x.val,Nat.le_trans (Nat.le_succ m) x.property⟩
  monotone' := fun _ _ h => h

def rankFiberIso (r : R → ℕ) (hr : StrictMono r) (m : ℕ)
    (p : rankAbove r m) (hp : r p.val = m) :
    {q : rankAbove r (m+1) // p ≤ rankStep r m q} ≃o Set.Ioi p.val where
  toFun q := ⟨q.val.val,lt_of_le_of_ne q.property (by
    intro he
    have hq := q.val.property
    change m+1 ≤ r q.val.val at hq
    rw [← he,hp] at hq
    omega)⟩
  invFun q := ⟨⟨q.val,by
    have h := hr q.property
    change m+1 ≤ r q.val
    omega⟩,q.property.le⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem Cocycle.trivial_rank_step (c : Cocycle R H) (r : R → ℕ) (hr : StrictMono r)
    (m : ℕ)
    (hupper : ∀ x, r x = m → Nonempty (Set.Ioi x) ∧ Connected (Set.Ioi x))
    (hm : (c.pull (rankEmbed r (m+1))).Trivial) :
    (c.pull (rankEmbed r m)).Trivial := by
  classical
  apply (c.pull (rankEmbed r m)).trivial_of_upper_fibers (rankStep r m)
  · intro p
    by_cases hp : m+1 ≤ r p.val
    · exact ⟨⟨p.val,hp⟩,le_refl _⟩
    · have he : r p.val = m := by have hh := p.property; change m ≤ r p.val at hh; omega
      obtain ⟨y⟩ := (hupper p.val he).1
      exact ⟨((rankFiberIso r hr m p he).symm y).val,
        ((rankFiberIso r hr m p he).symm y).property⟩
  · intro p
    by_cases hp : m+1 ≤ r p.val
    · exact connected_of_bottom (⟨⟨p.val,hp⟩,le_refl _⟩) (fun y => y.property)
    · have he : r p.val = m := by have hh := p.property; change m ≤ r p.val at hh; omega
      exact (hupper p.val he).2.of_orderIso (rankFiberIso r hr m p he).symm
  · exact hm

theorem Cocycle.trivial_of_rank (c : Cocycle R H) (r : R → ℕ) (hr : StrictMono r)
    (m : ℕ)
    (hupper : ∀ x, r x < m → Nonempty (Set.Ioi x) ∧ Connected (Set.Ioi x))
    (hm : (c.pull (rankEmbed r m)).Trivial) : c.Trivial := by
  induction m with
  | zero =>
    obtain ⟨v,hv⟩ := hm
    refine ⟨fun x => v ⟨x,Nat.zero_le _⟩,?_⟩
    intro x y h
    exact hv (x := ⟨x,Nat.zero_le _⟩) (y := ⟨y,Nat.zero_le _⟩) h
  | succ m ih =>
    apply ih (fun x hx => hupper x (Nat.lt_succ_of_lt hx))
    apply c.trivial_rank_step r hr m (fun x hx => hupper x (by omega)) hm
end Rank

section RankBelow
variable {R : Type*} [PartialOrder R]
def rankBelow (r : R → ℕ) (m : ℕ) : Set R := {x | r x ≤ m}
def belowEmbed (r : R → ℕ) (m : ℕ) : rankBelow r m →o R :=
  ⟨Subtype.val,fun _ _ h => h⟩
def belowStep (r : R → ℕ) (m : ℕ) : rankBelow r m →o rankBelow r (m+1) :=
  ⟨fun x => ⟨x.val,Nat.le_trans x.property (Nat.le_succ m)⟩,fun _ _ h => h⟩
def linkBelow (r : R → ℕ) (hr : StrictMono r) (m : ℕ) (a : R) (ha : r a = m+1) :
    Set.Iio a →o rankBelow r m where
  toFun x := ⟨x.val,by have hh := hr x.property; change r x.val ≤ m; omega⟩
  monotone' := fun _ _ h => h

namespace Cocycle
variable (r : R → ℕ) (hr : StrictMono r) (m : ℕ) (c : Cocycle (rankBelow r m) H)
variable (hlink : ∀ a, r a = m+1 → ∀ d : Cocycle (Set.Iio a) H, d.Trivial)
noncomputable def linkPotential (a : R) (ha : r a = m+1) : Set.Iio a → H :=
  (hlink a ha (c.pull (linkBelow r hr m a ha))).choose
lemma linkPotential_spec (a : R) (ha : r a = m+1) :
    (c.pull (linkBelow r hr m a ha)).Potential (linkPotential r hr m c hlink a ha) :=
  (hlink a ha (c.pull (linkBelow r hr m a ha))).choose_spec

noncomputable def nextEdge {x y : rankBelow r (m+1)} (h : x ≤ y) : H := by
  classical
  exact if hy : r y.val ≤ m then
    c.edge (x := ⟨x.val,(hr.monotone h).trans hy⟩) (y := ⟨y.val,hy⟩) h
  else if he : x = y then 1
  else (linkPotential r hr m c hlink y.val (by
    have hh := y.property; change r y.val ≤ m+1 at hh; omega)
    ⟨x.val,lt_of_le_of_ne h (fun hv => he (Subtype.ext hv))⟩)⁻¹

lemma nextEdge_old {x y : rankBelow r (m+1)} (h : x ≤ y) (hy : r y.val ≤ m) :
    nextEdge r hr m c hlink h =
      c.edge (x := ⟨x.val,(hr.monotone h).trans hy⟩) (y := ⟨y.val,hy⟩) h := by
  classical
  simp only [nextEdge,dite_eq_left hy]
lemma nextEdge_refl (x : rankBelow r (m+1)) : nextEdge r hr m c hlink (le_refl x) = 1 := by
  classical
  by_cases hx : r x.val ≤ m
  · rw [nextEdge_old r hr m c hlink _ hx]
    exact c.refl _
  · simp [nextEdge,hx]
lemma nextEdge_comp {x y z : rankBelow r (m+1)} (h : x ≤ y) (k : y ≤ z) :
    nextEdge r hr m c hlink h * nextEdge r hr m c hlink k =
      nextEdge r hr m c hlink (h.trans k) := by
  classical
  by_cases hz : r z.val ≤ m
  · have hy : r y.val ≤ m := (hr.monotone k).trans hz
    rw [nextEdge_old r hr m c hlink _ hy,nextEdge_old r hr m c hlink _ hz,
      nextEdge_old r hr m c hlink _ hz]
    exact c.comp _ _
  · by_cases hyz : y = z
    · subst z
      rw [nextEdge_refl,mul_one]
    · have hyz' : y.val < z.val := lt_of_le_of_ne k (fun he => hyz (Subtype.ext he))
      have hyr := hr hyz'
      have hzr := z.property
      change r z.val ≤ m+1 at hzr
      have hze : r z.val = m+1 := by omega
      have hy : r y.val ≤ m := by omega
      have hxz : x ≠ z := fun he => hyz (le_antisymm k (he ▸ h))
      have hv := linkPotential_spec r hr m c hlink z.val hze
        (x := ⟨x.val,lt_of_le_of_lt h hyz'⟩) (y := ⟨y.val,hyz'⟩) h
      rw [nextEdge_old r hr m c hlink _ hy]
      simp only [nextEdge,dite_eq_right hz,dite_eq_right hyz,dite_eq_right hxz]
      apply mul_left_cancel (a := linkPotential r hr m c hlink z.val hze
        ⟨x.val,lt_of_le_of_lt h hyz'⟩)
      rw [← mul_assoc,show linkPotential r hr m c hlink z.val hze
        ⟨x.val,lt_of_le_of_lt h hyz'⟩ * c.edge (x := ⟨x.val,(hr.monotone h).trans hy⟩)
          (y := ⟨y.val,hy⟩) h = linkPotential r hr m c hlink z.val hze ⟨y.val,hyz'⟩ from hv]
      simp only [mul_inv_cancel]

noncomputable def next : Cocycle (rankBelow r (m+1)) H where
  edge h := nextEdge r hr m c hlink h
  refl := nextEdge_refl r hr m c hlink
  comp := nextEdge_comp r hr m c hlink
lemma next_pull : (next r hr m c hlink).pull (belowStep r m) = c := by
  apply Cocycle.ext
  intro x y h
  exact nextEdge_old r hr m c hlink (x := belowStep r m x) (y := belowStep r m y)
    h y.property
end Cocycle
end RankBelow

lemma connected_of_directed (hd : ∀ x y : P, ∃ z, x ≤ z ∧ y ≤ z) : Connected P := by
  intro x y
  obtain ⟨z,hxz,hyz⟩ := hd x y
  exact (Relation.ReflTransGen.single (show Adj x z from Or.inl hxz)).trans
    (Relation.ReflTransGen.single (show Adj z y from Or.inr hyz))
theorem Cocycle.trivial_of_directed [Nonempty P] (c : Cocycle P H)
    (hd : ∀ x y : P, ∃ z, x ≤ z ∧ y ≤ z) : c.Trivial := by
  classical
  let b : P := Classical.choice ‹Nonempty P›
  let f : Set.Ici b →o P := ⟨Subtype.val,fun _ _ h => h⟩
  apply c.trivial_of_upper_fibers f
  · intro p
    obtain ⟨z,hbz,hpz⟩ := hd b p
    exact ⟨⟨z,hbz⟩,hpz⟩
  · intro p
    apply connected_of_directed
    intro x y
    obtain ⟨z,hxz,hyz⟩ := hd x.val.val y.val.val
    exact ⟨⟨⟨z,x.val.property.trans hxz⟩,x.property.trans hxz⟩,hxz,hyz⟩
  · exact (c.pull f).trivial_of_bottom ⟨b,le_refl b⟩ (fun x => x.property)

variable {R : Type*} [PartialOrder R]
namespace Cocycle
variable (r : R → ℕ) (hr : StrictMono r) (h : ℕ)
variable (c : Cocycle (rankBelow r h) H)
variable (hlink : ∀ a, h < r a → ∀ d : Cocycle (Set.Iio a) H, d.Trivial)
noncomputable def extension : (k : ℕ) → Cocycle (rankBelow r (h+k)) H
  | 0 => c
  | k+1 => next r hr (h+k) (extension k)
    (fun a ha => hlink a (by omega))
noncomputable def extensionLabel (k : ℕ) {x y : R} (hxy : x ≤ y) (hy : r y ≤ h+k) : H :=
  (extension r hr h c hlink k).edge
    (x := ⟨x,(hr.monotone hxy).trans hy⟩) (y := ⟨y,hy⟩) hxy
lemma extensionLabel_succ (k : ℕ) {x y : R} (hxy : x ≤ y) (hy : r y ≤ h+k) :
    extensionLabel r hr h c hlink (k+1) hxy (Nat.le_trans hy (Nat.le_succ _)) =
      extensionLabel r hr h c hlink k hxy hy := by
  exact nextEdge_old r hr (h+k) _ _
    (x := ⟨x,(hr.monotone hxy).trans (hy.trans (Nat.le_succ _))⟩)
    (y := ⟨y,hy.trans (Nat.le_succ _)⟩) hxy hy
lemma extensionLabel_stable {i j : ℕ} (hij : i ≤ j) {x y : R}
    (hxy : x ≤ y) (hy : r y ≤ h+i) :
    extensionLabel r hr h c hlink j hxy (hy.trans (Nat.add_le_add_left hij h)) =
      extensionLabel r hr h c hlink i hxy hy := by
  induction j,hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    rw [extensionLabel_succ r hr h c hlink j hxy (hy.trans (Nat.add_le_add_left hij h))]
    exact ih

noncomputable def fullExtension : Cocycle R H where
  edge {x y} hxy := extensionLabel r hr h c hlink (r y) hxy (Nat.le_add_left _ _)
  refl x := (extension r hr h c hlink (r x)).refl ⟨x,Nat.le_add_left _ _⟩
  comp {x y z} hxy hyz := by
    have hz : r z ≤ h+r z := Nat.le_add_left _ _
    have hy : r y ≤ h+r y := Nat.le_add_left _ _
    rw [← extensionLabel_stable r hr h c hlink (hr.monotone hyz) hxy hy]
    exact (extension r hr h c hlink (r z)).comp
      (x := ⟨x,(hr.monotone (hxy.trans hyz)).trans hz⟩)
      (y := ⟨y,(hr.monotone hyz).trans hz⟩) (z := ⟨z,hz⟩) hxy hyz
lemma fullExtension_pull : (fullExtension r hr h c hlink).pull (belowEmbed r h) = c := by
  apply Cocycle.ext
  intro x y hxy
  have hh := extensionLabel_stable r hr h c hlink (Nat.zero_le (r y.val))
    (show x.val ≤ y.val from hxy) (show r y.val ≤ h+0 from y.property)
  exact hh

include hr hlink in

theorem trivial_sublevel [Nonempty R]
    (hd : ∀ x y : R, ∃ z, x ≤ z ∧ y ≤ z) : c.Trivial := by
  have hf := (fullExtension r hr h c hlink).trivial_of_directed hd
  have hp := (fullExtension r hr h c hlink).trivial_pull hf (belowEmbed r h)
  rw [fullExtension_pull] at hp
  exact hp
end Cocycle
end

open OrderListChains OrderChains
variable (P : Type*) [Preorder P]
lemma connected_of_exactIn (h : ExactIn P 0) : Connected P := by
  have hu : ExactSet P Set.univ 0 := by
    intro c hc hn hd ha
    obtain ⟨d,hdM,hdn,hdd⟩ := h c (onSet_le_module P _ hc) hn hd ha
    exact ⟨d,fun s hs => ⟨hdM hs,Set.subset_univ _⟩,hdn,hdd⟩
  apply connected_of_constant
  intro f hf x y
  exact constant_of_exact_zero P hu f (fun _ _ _ _ h => hf h)
    (Set.mem_univ x) (Set.mem_univ y)
end PosetTransport

end

end OAI
