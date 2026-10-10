import Mathlib

namespace OAI

/-! Prefix-pruned coordinate trees and enumeration bounds. -/

namespace DeterministicThreeSum.Pruned
open Finset

structure Alphabet where
  radix : ℕ
  weight : ℕ → ℕ

abbrev Node := ℕ × ℕ

def next (A : Alphabet) (p : Node) (v : ℕ) : Node :=
  (p.1*A.radix+v,p.2+A.weight v)

def children (A : Alphabet) (D : ℕ) (p : Node) : List Node :=
  ((List.range A.radix).filter (fun v => p.2+A.weight v≤D)).map (next A p)

def expand (A : Alphabet) (D : ℕ) (l : List Node) : List Node :=
  l.flatMap (children A D)

lemma children_length_le (A : Alphabet) (D : ℕ) (p : Node) :
    (children A D p).length≤A.radix := by
  simpa [children] using List.length_filter_le (fun v => decide (p.2+A.weight v≤D)) (List.range A.radix)

lemma mem_children_iff (A : Alphabet) (D : ℕ) (p z : Node) :
    z∈children A D p ↔ ∃ v, v<A.radix ∧ p.2+A.weight v≤D ∧ z=next A p v := by
  simp only [children,List.mem_map,List.mem_filter,List.mem_range,decide_eq_true_eq]
  constructor
  · rintro ⟨v,⟨hv,hd⟩,he⟩; exact ⟨v,hv,hd,he.symm⟩
  · rintro ⟨v,hv,hd,he⟩; exact ⟨v,⟨hv,hd⟩,he.symm⟩

lemma expand_length_le (A : Alphabet) (D : ℕ) (l : List Node) :
    (expand A D l).length≤l.length*A.radix := by
  induction l with
  | nil => simp [expand]
  | cons p l ih =>
    have hh:=children_length_le A D p
    simpa only [expand,List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,one_mul,Nat.add_comm] using Nat.add_le_add hh ih

lemma expand_append (A : Alphabet) (D : ℕ) (l m : List Node) :
    expand A D (l++m)=expand A D l++expand A D m := by simp [expand]

lemma children_valid (A : Alphabet) (D : ℕ) (p : Node) (z : Node) (hz : z∈children A D p) : z.2≤D := by
  obtain ⟨v,hv,hd,rfl⟩:=(mem_children_iff ..).mp hz
  exact hd

lemma expand_valid (A : Alphabet) (D : ℕ) (l : List Node) :
    ∀ z∈expand A D l, z.2≤D := by
  intro z hz
  obtain ⟨p,hp,hz⟩:=List.mem_flatMap.mp hz
  exact children_valid A D p z hz

lemma children_nonempty (A : Alphabet) (hA : 0<A.radix) (h0 : A.weight 0=0)
    (D : ℕ) (p : Node) (hp : p.2≤D) : 0<(children A D p).length := by
  have hh : next A p 0∈children A D p := (mem_children_iff ..).mpr ⟨0,hA,by simpa [h0] using hp,rfl⟩
  exact List.length_pos_of_mem hh

lemma length_le_expand (A : Alphabet) (hA : 0<A.radix) (h0 : A.weight 0=0)
    (D : ℕ) (l : List Node) (hl : ∀ p∈l, p.2≤D) : l.length≤(expand A D l).length := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp:=children_nonempty A hA h0 D p (hl p (by simp))
    have hi:=ih (by intro p hp; exact hl p (by simp [hp]))
    simp only [List.length_cons,expand,List.flatMap_cons,List.length_append] at *
    omega

def enumerate (D : ℕ) : List Alphabet → List Node
  | [] => [(0,0)]
  | A::rest => expand A D (enumerate D rest)

def volume : List Alphabet → ℕ
  | [] => 1
  | A::rest => volume rest*A.radix

def degree : List Alphabet → ℕ → ℕ
  | [],_ => 0
  | A::rest,c => degree rest (c/A.radix)+A.weight (c%A.radix)

lemma enumerate_valid (D : ℕ) (shape : List Alphabet) : ∀ p∈enumerate D shape, p.2≤D := by
  cases shape with
  | nil => simp [enumerate]
  | cons A rest => exact expand_valid A D _

lemma enumerate_child (D : ℕ) (shape : List Alphabet) (hpos : ∀ A∈shape, 0<A.radix) :
    ∀ p, p∈enumerate D shape ↔ p.1<volume shape ∧ p.2=degree shape p.1 ∧ p.2≤D := by
  induction shape with
  | nil =>
    intro p
    simp only [enumerate,List.mem_singleton,volume,degree]
    rcases p with ⟨c,d⟩
    simp only [Prod.mk.injEq]
    omega
  | cons A rest ih =>
    intro p
    have hA:=hpos A (by simp)
    have hrest : ∀ A∈rest, 0<A.radix := by intro B hB; exact hpos B (by simp [hB])
    rw [enumerate,expand,List.mem_flatMap]
    constructor
    · rintro ⟨z,hz,hp⟩
      obtain ⟨v,hv,hd,rfl⟩:=(mem_children_iff ..).mp hp
      obtain ⟨hc,he,hd'⟩:=(ih hrest z).mp hz
      refine ⟨?_,?_,hd⟩
      · simp only [next,volume]
        nlinarith only [Nat.mul_le_mul_right A.radix hc,hv]
      · simp only [next,degree]
        rw [Nat.mul_comm z.1 A.radix,Nat.mul_add_div hA,Nat.div_eq_of_lt hv]
        simp [Nat.add_mod,Nat.mod_eq_of_lt hv,he]
    · rintro ⟨hc,he,hd⟩
      have hq : p.1/A.radix<volume rest := (Nat.div_lt_iff_lt_mul hA).mpr hc
      have hv : p.1%A.radix<A.radix := Nat.mod_lt _ hA
      have hdeg : degree rest (p.1/A.radix)≤D := by simp only [degree] at he; omega
      refine ⟨(p.1/A.radix,degree rest (p.1/A.radix)),(ih hrest _).mpr ⟨hq,rfl,hdeg⟩,?_⟩
      apply (mem_children_iff ..).mpr
      refine ⟨p.1%A.radix,hv,?_,?_⟩
      · change degree (A::rest) p.1≤D
        rw [←he]; exact hd
      · apply Prod.ext
        · exact (Nat.div_add_mod' p.1 A.radix).symm
        · exact he

lemma length_enumerate_suffix (D : ℕ) (front back : List Alphabet)
    (hpos : ∀ A∈front, 0<A.radix) (hzero : ∀ A∈front, A.weight 0=0) :
    (enumerate D back).length≤(enumerate D (front++back)).length := by
  induction front with
  | nil => simp
  | cons A front ih =>
    have hA:=hpos A (by simp)
    have h0:=hzero A (by simp)
    have hi:=ih (by intro B h; exact hpos B (by simp [h])) (by intro B h; exact hzero B (by simp [h]))
    exact hi.trans (length_le_expand A hA h0 D _ (enumerate_valid D _))

end DeterministicThreeSum.Pruned

end OAI
