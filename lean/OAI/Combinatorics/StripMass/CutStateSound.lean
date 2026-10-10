import Mathlib
import OAI.Combinatorics.StripMass.CutPatch

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset
open scoped Classical
namespace Pairing

theorem tileStep_sound_vacant {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (d : Finset (Fin 4 × Fin 4))
    (ha : ¬ p.Occupied a) (hb : ¬ p.Occupied b)
    (hq : p.tileStep a b hab t = some q)
    (hd : CutPatch.profile (p.cutShape a b) t = some d) (i j : Fin n) :
    q.Adj i j ↔ p.cutRelation a b d i j := by
  have hp := adj_decompose_partners p a b i j
  cases t <;> simp [tileStep,cutShape,ha,hb,CutPatch.profile] at hq hd
  all_goals subst q; subst d
  all_goals simp only [insertCup_adj,cutRelation_single,cutRelation_empty,cutLabels,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  all_goals simp only [ha,hb,false_and,or_false] at hp
  all_goals try { exact hp }
  all_goals itauto

theorem tileStep_sound_single₀ {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (d : Finset (Fin 4 × Fin 4))
    (ha : p.Occupied a) (hb : ¬ p.Occupied b)
    (hq : p.tileStep a b hab t = some q)
    (hd : CutPatch.profile (p.cutShape a b) t = some d) (i j : Fin n) :
    q.Adj i j ↔ p.cutRelation a b d i j := by
  have hp := adj_decompose_partners p a b i j
  have hs := adj_decompose_partners p a b (Equiv.swap a b i) (Equiv.swap a b j)
  rw [omitTwo_swap_invariant] at hs
  cases t <;> simp [tileStep,cutShape,ha,hb,CutPatch.profile] at hq hd
  all_goals subst q; subst d
  all_goals simp only [moveIntoVacancy_adj,cutRelation_single,cutLabels,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  all_goals simp only [ha,hb,false_and,true_and,or_false] at hp
  all_goals try { simpa only [ha,hb,true_and,false_and,or_false,false_or,Equiv.swap_apply_eq_iff,
      Equiv.swap_apply_left,Equiv.swap_apply_right,and_comm,swap_eq_partner_iff p a b i ha hb,
      swap_eq_partner_iff p a b j ha hb] using hs }
  all_goals itauto

theorem tileStep_sound_single₁ {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (d : Finset (Fin 4 × Fin 4))
    (ha : ¬ p.Occupied a) (hb : p.Occupied b)
    (hq : p.tileStep a b hab t = some q)
    (hd : CutPatch.profile (p.cutShape a b) t = some d) (i j : Fin n) :
    q.Adj i j ↔ p.cutRelation a b d i j := by
  have hp := adj_decompose_partners p a b i j
  have hs := adj_decompose_partners p a b (Equiv.swap a b i) (Equiv.swap a b j)
  rw [omitTwo_swap_invariant] at hs
  cases t <;> simp [tileStep,cutShape,ha,hb,CutPatch.profile] at hq hd
  all_goals subst q; subst d
  all_goals simp only [moveIntoLowerVacancy_adj,cutRelation_single,cutLabels,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  all_goals simp only [ha,hb,false_and,true_and,false_or] at hp
  all_goals try { simpa only [ha,hb,true_and,false_and,or_false,false_or,Equiv.swap_apply_eq_iff,
      Equiv.swap_apply_left,Equiv.swap_apply_right,and_comm,swap_eq_partner_iff_lower p a b i ha hb,
      swap_eq_partner_iff_lower p a b j ha hb] using hs }
  all_goals itauto

theorem tileStep_sound_paired {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (d : Finset (Fin 4 × Fin 4))
    (ha : p.Occupied a) (hb : p.Occupied b) (hn : p.Adj a b)
    (hq : p.tileStep a b hab t = some q)
    (hd : CutPatch.profile (p.cutShape a b) t = some d) (i j : Fin n) :
    q.Adj i j ↔ p.cutRelation a b d i j := by
  have hp := adj_decompose_partners p a b i j
  have hpa : p.partnerOrSelf a = b := ((adj_partnerOrSelf p a b).mp hn).2.symm
  have hpb : p.partnerOrSelf b = a := ((adj_partnerOrSelf p b a).mp (adj_symm hn)).2.symm
  cases t <;> simp [tileStep,cutShape,ha,hb,hn,CutPatch.profile] at hq hd
  all_goals subst q; subst d
  all_goals simp only [cutRelation_single,cutLabels,Matrix.cons_val_zero,Matrix.cons_val_one]
  all_goals simp only [ha,hb,hpa,hpb,true_and] at hp
  all_goals itauto

theorem tileStep_sound_separate {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (d : Finset (Fin 4 × Fin 4))
    (ha : p.Occupied a) (hb : p.Occupied b) (hn : ¬ p.Adj a b)
    (hq : p.tileStep a b hab t = some q)
    (hd : CutPatch.profile (p.cutShape a b) t = some d) (i j : Fin n) :
    q.Adj i j ↔ p.cutRelation a b d i j := by
  have hp := adj_decompose_partners p a b i j
  cases t <;> simp [tileStep,cutShape,ha,hb,hn,CutPatch.profile] at hq hd
  all_goals subst q; subst d
  all_goals simp only [insertCup_adj,capRemove_adj,Finset.insert_eq,cutRelation_union,
    cutRelation_single,cutLabels,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  all_goals simp only [ha,hb,true_and] at hp
  all_goals try { simp only [and_comm, or_assoc, or_left_comm, or_comm] }
  all_goals itauto

theorem tileStep_sound {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (d : Finset (Fin 4 × Fin 4))
    (hq : p.tileStep a b hab t = some q)
    (hd : CutPatch.profile (p.cutShape a b) t = some d) (i j : Fin n) :
    q.Adj i j ↔ p.cutRelation a b d i j := by
  by_cases ha : p.Occupied a
  · by_cases hb : p.Occupied b
    · by_cases hn : p.Adj a b
      · exact tileStep_sound_paired p a b hab t q d ha hb hn hq hd i j
      · exact tileStep_sound_separate p a b hab t q d ha hb hn hq hd i j
    · exact tileStep_sound_single₀ p a b hab t q d ha hb hq hd i j
  · by_cases hb : p.Occupied b
    · exact tileStep_sound_single₁ p a b hab t q d ha hb hq hd i j
    · exact tileStep_sound_vacant p a b hab t q d ha hb hq hd i j

end Pairing
end

 

 

noncomputable section
namespace Pairing

theorem adj_trans_eq {n : ℕ} {p : Pairing n} {i j k : Fin n}
    (h : p.Adj i j) (g : p.Adj j k) : i = k :=
  adj_unique (adj_symm h) g

theorem reach_adj_iff {n : ℕ} (p : Pairing n) (i j : Fin n) :
    Relation.ReflTransGen p.Adj i j ↔ i=j ∨ p.Adj i j := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @tail j k h hjk ih =>
      rcases ih with rfl | h
      · exact Or.inr hjk
      · exact Or.inl (adj_trans_eq h hjk)
  · rintro (rfl|h)
    · exact .refl
    · exact .single h

end Pairing

namespace Patch
variable {A I : Type*} {n : ℕ}
variable (r : A → A → Prop) (s : Fin n → Fin n → Prop)
  (a : I → A) (b : I → Fin n) (active : I → Prop)
  (d : I → I → Prop) (q : Pairing n)
variable (hd : ∀ i j, d i j → active i ∧ active j)
  (ha : ∀ i, active i → ∃ j, d i j)
  (hr : ∀ i j, Relation.ReflTransGen r (a i) (a j) ↔ i=j ∨ d i j)
  (hq : ∀ x y, q.Adj x y ↔ s x y ∨ ∃ i j, d i j ∧ b i=x ∧ b j=y)

include hd hr hq in
theorem pairing_adj_compressed {x y : Fin n} (h : q.Adj x y) :
    compressed r s a b active x y := by
  rcases (hq x y).mp h with hxy | ⟨i,j,hdi,rfl,rfl⟩
  · exact Or.inl hxy
  · exact Or.inr ⟨i,j,(hd i j hdi).1,(hd i j hdi).2,(hr i j).mpr (Or.inr hdi),rfl,rfl⟩

include ha hr hq in
theorem compressed_pairing {x y : Fin n} (h : compressed r s a b active x y) :
    (x=y ∨ q.Adj x y) ∧ q.Occupied x := by
  rcases h with h | ⟨i,j,hi,hj,h,rfl,rfl⟩
  · have h' := (hq x y).mpr (Or.inl h)
    exact ⟨Or.inr h',⟨y,h'⟩⟩
  · rcases (hr i j).mp h with rfl | h
    · obtain ⟨k,hk⟩ := ha i hi
      exact ⟨Or.inl rfl,⟨b k,(hq _ _).mpr (Or.inr ⟨i,k,hk,rfl,rfl⟩)⟩⟩
    · have h' := (hq _ _).mpr (Or.inr ⟨i,j,h,rfl,rfl⟩)
      exact ⟨Or.inr h',⟨b j,h'⟩⟩

include hd ha hr hq in
theorem compressed_reach_pairing (x y : Fin n) :
    Relation.ReflTransGen (compressed r s a b active) x y ↔ x=y ∨ q.Adj x y := by
  constructor
  · intro h
    apply (q.reach_adj_iff x y).mp
    induction h with
    | refl => exact .refl
    | @tail j k h hjk ih =>
      rcases (compressed_pairing r s a b active d q ha hr hq hjk).1 with rfl | h
      · exact ih
      · exact ih.tail h
  · rintro (rfl|h)
    · exact .refl
    · exact .single (pairing_adj_compressed r s a b active d q hd hr hq h)

include ha hr hq in
theorem compressed_drains_pairing : drains (compressed r s a b active) q.Occupied := by
  intro x y h
  exact ⟨x,(compressed_pairing r s a b active d q ha hr hq h).2,.refl⟩

include hd ha hr hq in
theorem glued_reach_pairing (x y : Fin n) :
    Relation.ReflTransGen (glued r s a b active) (.inr x) (.inr y) ↔ x=y ∨ q.Adj x y := by
  rw [exterior_reach_iff]
  exact compressed_reach_pairing r s a b active d q hd ha hr hq x y

include ha hr hq in
theorem glued_drains_pairing
    (hlocal : ∀ x y, r x y → ∃ i, active i ∧ Relation.ReflTransGen r x (a i)) :
    drains (glued r s a b active) (exteriorOutput q.Occupied) := by
  apply (drains_glued_iff r s a b active q.Occupied).mpr
  exact ⟨hlocal,compressed_drains_pairing r s a b active d q ha hr hq⟩

end Patch

 

 


 

structure GraphRealizes {V : Type*} {n : ℕ} (r : V → V → Prop)
    (boundary : Fin n → V) (p : Pairing n) : Prop where
  no_loop : ∀ v w, r v w → ∃ i, p.Occupied i ∧ Relation.ReflTransGen r v (boundary i)
  reach : ∀ i j, Relation.ReflTransGen r (boundary i) (boundary j) ↔ i=j ∨ p.Adj i j

namespace CutPatch

theorem Realizes.reach {s : Shape} {t : Tile} {d : Finset (Fin 4 × Fin 4)}
    (h : Realizes s t d) (i j : Fin 4) :
    Relation.ReflTransGen (Adj s t) (boundary i) (boundary j) ↔ i=j ∨ boundaryAdj d i j := by
  by_cases hij : i=j
  · subst j
    exact ⟨fun _ => Or.inl rfl,fun _ => .refl⟩
  · simp only [hij,false_or]
    exact (h.output i j hij).symm

theorem Realizes.edge_active {s : Shape} {t : Tile} {d : Finset (Fin 4 × Fin 4)}
    (h : Realizes s t d) (i j : Fin 4) (hd : boundaryAdj d i j) :
    active s t i ∧ active s t j := by
  exact ⟨(h.occupied i).mpr ⟨j,hd⟩,
    (h.occupied j).mpr ⟨i,hd.elim Or.inr Or.inl⟩⟩

end CutPatch

namespace Pairing

def cutGraph {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) :
    Sum (Fin 6) (Fin n) → Sum (Fin 6) (Fin n) → Prop :=
  Patch.glued (CutPatch.Adj (p.cutShape a b) t) (p.omitTwo a b).Adj
    CutPatch.boundary (p.cutLabels a b) (CutPatch.active (p.cutShape a b) t)

theorem cutGraph_realizes {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (q : Pairing n)
    (hq : p.tileStep a b hab t = some q) :
    GraphRealizes (p.cutGraph a b t) Sum.inr q := by
  have hne : CutPatch.profile (p.cutShape a b) t ≠ none := by
    intro hh
    have := (p.tileStep_none_iff a b hab t).mpr hh
    rw [hq] at this
    cases this
  obtain ⟨d,hd⟩ := Option.ne_none_iff_exists'.mp hne
  have hh := CutPatch.realizes_of_profile hd
  have ha : ∀ i, CutPatch.active (p.cutShape a b) t i → ∃ j, CutPatch.boundaryAdj d i j :=
    fun i hi => (hh.occupied i).mp hi
  have hq' : ∀ x y, q.Adj x y ↔ (p.omitTwo a b).Adj x y ∨
      ∃ i j, CutPatch.boundaryAdj d i j ∧ p.cutLabels a b i=x ∧ p.cutLabels a b j=y :=
    p.tileStep_sound a b hab t q d hq hd
  have hhloop := Patch.glued_drains_pairing
    (CutPatch.Adj (p.cutShape a b) t) (p.omitTwo a b).Adj CutPatch.boundary
    (p.cutLabels a b) (CutPatch.active (p.cutShape a b) t)
    (CutPatch.boundaryAdj d) q ha hh.reach hq' hh.no_loop
  constructor
  · intro v w hvw
    obtain ⟨z,hz,hr⟩ := hhloop v w hvw
    cases z with
    | inl z => exact hz.elim
    | inr z => exact ⟨z,hz,hr⟩
  · exact Patch.glued_reach_pairing
      (CutPatch.Adj (p.cutShape a b) t) (p.omitTwo a b).Adj CutPatch.boundary
      (p.cutLabels a b) (CutPatch.active (p.cutShape a b) t)
      (CutPatch.boundaryAdj d) q hh.edge_active ha hh.reach hq'

end Pairing

 

 


namespace Graph

def Used {V : Type*} (r : V → V → Prop) (v : V) : Prop := ∃ w, r v w

theorem map_reach {V W : Type*} {r : V → V → Prop} {s : W → W → Prop}
    (f : V → W) (hf : ∀ v w, r v w → Relation.ReflTransGen s (f v) (f w))
    {v w : V} (h : Relation.ReflTransGen r v w) : Relation.ReflTransGen s (f v) (f w) := by
  induction h with
  | refl => exact .refl
  | @tail y z h hyz ih => exact ih.trans (hf y z hyz)

 

structure BoundaryEquiv {V W : Type*} {n : ℕ} (r : V → V → Prop) (s : W → W → Prop)
    (a : Fin n → V) (b : Fin n → W) where
  toFun : V → W
  invFun : W → V
  map_edge : ∀ v w, r v w → Relation.ReflTransGen s (toFun v) (toFun w)
  inv_edge : ∀ v w, s v w → Relation.ReflTransGen r (invFun v) (invFun w)
  map_boundary : ∀ i, toFun (a i) = b i
  inv_boundary : ∀ i, invFun (b i) = a i
  map_used : ∀ v, Used r v → Used s (toFun v)
  inv_used : ∀ v, Used s v → Used r (invFun v)
  retract : ∀ v, Used r v → Relation.ReflTransGen r v (invFun (toFun v))
  inv_retract : ∀ v, Used s v → Relation.ReflTransGen s v (toFun (invFun v))

namespace BoundaryEquiv
variable {V W : Type*} {n : ℕ} {r : V → V → Prop} {s : W → W → Prop}
  {a : Fin n → V} {b : Fin n → W}

protected def symm (e : BoundaryEquiv r s a b) : BoundaryEquiv s r b a :=
  ⟨e.invFun,e.toFun,e.inv_edge,e.map_edge,e.inv_boundary,e.map_boundary,
    e.inv_used,e.map_used,e.inv_retract,e.retract⟩

theorem realizes (e : BoundaryEquiv r s a b) {p : Pairing n}
    (h : GraphRealizes r a p) : GraphRealizes s b p := by
  constructor
  · intro v w hvw
    obtain ⟨x,hx⟩ := e.inv_used v ⟨w,hvw⟩
    obtain ⟨i,hi,hr⟩ := h.no_loop (e.invFun v) x hx
    refine ⟨i,hi,?_⟩
    have hmap := Graph.map_reach e.toFun e.map_edge hr
    rw [e.map_boundary] at hmap
    exact (e.inv_retract v ⟨w,hvw⟩).trans hmap
  · intro i j
    constructor
    · intro hh
      have hm := Graph.map_reach e.invFun e.inv_edge hh
      rw [e.inv_boundary,e.inv_boundary] at hm
      exact (h.reach i j).mp hm
    · intro hh
      have hm := Graph.map_reach e.toFun e.map_edge ((h.reach i j).mpr hh)
      rwa [e.map_boundary,e.map_boundary] at hm

theorem realizes_iff (e : BoundaryEquiv r s a b) {p : Pairing n} :
    GraphRealizes r a p ↔ GraphRealizes s b p :=
  ⟨e.realizes,e.symm.realizes⟩

end BoundaryEquiv
end Graph

 

 

open Finset
open scoped Classical

inductive StepVertex (n : ℕ) where
  | old : Fin n → StepVertex n
  | box : Fin 4 → StepVertex n
  | out : Fin n → StepVertex n
  deriving DecidableEq

namespace Pairing

def stepWiring {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) :
    StepVertex n → StepVertex n → Prop
  | .old i, .old j => p.Adj i j
  | .box k, .box l => t.Adj k l
  | .old i, .box k | .box k, .old i =>
      (i=a ∧ k=0 ∧ p.Occupied a) ∨ (i=b ∧ k=1 ∧ p.Occupied b)
  | .old i, .out j | .out j, .old i =>
      i=j ∧ i≠a ∧ i≠b ∧ p.Occupied i
  | .box k, .out i | .out i, .box k =>
      (i=a ∧ k=2 ∧ t.Occupied 2) ∨ (i=b ∧ k=3 ∧ t.Occupied 3)
  | .out _, .out _ => False

def stepToCut {n : ℕ} (_p : Pairing n) (a b : Fin n) : StepVertex n → Sum (Fin 6) (Fin n)
  | .old i => if i=a then .inl 0 else if i=b then .inl 1 else .inr i
  | .box k => .inl (CutPatch.tilePort k)
  | .out i => .inr i

def cutToStep {n : ℕ} (p : Pairing n) (a b : Fin n) : Sum (Fin 6) (Fin n) → StepVertex n
  | .inl i => ![.box 0,.box 1,.box 2,.box 3,.old (p.partnerOrSelf a),.old (p.partnerOrSelf b)] i
  | .inr i => .out i

theorem stepWiring_symm {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    {v w : StepVertex n} (h : p.stepWiring a b t v w) : p.stepWiring a b t w v := by
  cases v <;> cases w <;> try exact h
  · exact adj_symm h
  · exact h.elim Or.inr Or.inl

instance stepWiring_isSymm {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) :
    Std.Symm (p.stepWiring a b t) := ⟨fun _ _ => stepWiring_symm p a b t⟩

theorem cutGraph_symm {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile)
    {v w : Sum (Fin 6) (Fin n)} (h : p.cutGraph a b t v w) : p.cutGraph a b t w v := by
  cases v with
  | inl v =>
    cases w with
    | inl w => exact (CutPatch.adj_symmetric _ _).symm _ _ h
    | inr w => obtain ⟨i,hi,rfl,rfl⟩ := h; exact ⟨i,hi,rfl,rfl⟩
  | inr v =>
    cases w with
    | inl w => obtain ⟨i,hi,rfl,rfl⟩ := h; exact ⟨i,hi,rfl,rfl⟩
    | inr w => exact adj_symm h

instance cutGraph_isSymm {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) :
    Std.Symm (p.cutGraph a b t) := ⟨fun _ _ => cutGraph_symm p a b t⟩

end Pairing

namespace CutPatch

theorem active_zero (s : Shape) (t : Tile) : active s t 0 ↔ t.Occupied 2 := by
  cases s <;> cases t <;> decide

theorem active_one (s : Shape) (t : Tile) : active s t 1 ↔ t.Occupied 3 := by
  cases s <;> cases t <;> decide

theorem active_two (s : Shape) (t : Tile) : active s t 2 ↔ s=.single₀ ∨ s=.separate := by
  cases s <;> cases t <;> decide

theorem active_three (s : Shape) (t : Tile) : active s t 3 ↔ s=.single₁ ∨ s=.separate := by
  cases s <;> cases t <;> decide

theorem input_occupied_zero (s : Shape) : inputOccupied s 0 ↔
    s=.single₀ ∨ s=.paired ∨ s=.separate := by cases s <;> decide

theorem input_occupied_one (s : Shape) : inputOccupied s 1 ↔
    s=.single₁ ∨ s=.paired ∨ s=.separate := by cases s <;> decide

end CutPatch

namespace Pairing

theorem cutShape_input_zero {n : ℕ} (p : Pairing n) (a b : Fin n) :
    CutPatch.inputOccupied (p.cutShape a b) 0 ↔ p.Occupied a := by
  rw [CutPatch.input_occupied_zero]
  by_cases ha : p.Occupied a <;> by_cases hb : p.Occupied b <;> by_cases hn : p.Adj a b <;>
    simp [cutShape,ha,hb,hn]

theorem cutShape_input_one {n : ℕ} (p : Pairing n) (a b : Fin n) :
    CutPatch.inputOccupied (p.cutShape a b) 1 ↔ p.Occupied b := by
  rw [CutPatch.input_occupied_one]
  by_cases ha : p.Occupied a <;> by_cases hb : p.Occupied b <;> by_cases hn : p.Adj a b <;>
    simp [cutShape,ha,hb,hn]

theorem cutShape_compatible {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) :
    CutPatch.Compatible (p.cutShape a b) t ↔
      (p.Occupied a ↔ t.Occupied 0) ∧ (p.Occupied b ↔ t.Occupied 1) := by
  simp only [CutPatch.Compatible,Fin.forall_fin_two,cutShape_input_zero,cutShape_input_one]
  rfl

theorem cutShape_active_two {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) :
    CutPatch.active (p.cutShape a b) t 2 ↔ p.Occupied a ∧ ¬ p.Adj a b := by
  rw [CutPatch.active_two]
  by_cases ha : p.Occupied a <;> by_cases hb : p.Occupied b <;> by_cases hn : p.Adj a b <;>
    simp [cutShape,ha,hb,hn]
  exact (hb ⟨a,adj_symm hn⟩).elim

theorem cutShape_active_three {n : ℕ} (p : Pairing n) (a b : Fin n) (t : Tile) :
    CutPatch.active (p.cutShape a b) t 3 ↔ p.Occupied b ∧ ¬ p.Adj a b := by
  rw [CutPatch.active_three]
  by_cases ha : p.Occupied a <;> by_cases hb : p.Occupied b <;> by_cases hn : p.Adj a b <;>
    simp [cutShape,ha,hb,hn]
  exact (ha ⟨b,hn⟩).elim

end Pairing
end
end CriticalStrip.Diagram

end OAI
