import Mathlib
import OAI.Combinatorics.StripMass.LaurentBox

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram.Patch
noncomputable section

variable {A B I : Type*}

 
def glued (r : A → A → Prop) (s : B → B → Prop) (a : I → A) (b : I → B)
    (active : I → Prop) : Sum A B → Sum A B → Prop
  | .inl x, .inl y => r x y
  | .inr x, .inr y => s x y
  | .inl x, .inr y => ∃ i, active i ∧ x = a i ∧ y = b i
  | .inr x, .inl y => ∃ i, active i ∧ x = b i ∧ y = a i

 

def compressed (r : A → A → Prop) (s : B → B → Prop) (a : I → A) (b : I → B)
    (active : I → Prop) (x y : B) : Prop :=
  s x y ∨ ∃ i j, active i ∧ active j ∧
    Relation.ReflTransGen r (a i) (a j) ∧ x = b i ∧ y = b j

variable (r : A → A → Prop) (s : B → B → Prop) (a : I → A) (b : I → B)
  (active : I → Prop)

theorem reach_to_exterior {x : Sum A B} {y : B}
    (h : Relation.ReflTransGen (glued r s a b active) x (.inr y)) :
    match x with
    | .inr x => Relation.ReflTransGen (compressed r s a b active) x y
    | .inl x => ∃ i, active i ∧ Relation.ReflTransGen r x (a i) ∧
        Relation.ReflTransGen (compressed r s a b active) (b i) y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head x w h hpath ih =>
    cases x with
    | inl x =>
      cases w with
      | inl w =>
        obtain ⟨i,hi,hr,hs⟩ := ih
        exact ⟨i,hi,hr.head h,hs⟩
      | inr w =>
        obtain ⟨i,hi,rfl,rfl⟩ := h
        exact ⟨i,hi,.refl,ih⟩
    | inr x =>
      cases w with
      | inl w =>
        obtain ⟨i,hi,rfl,rfl⟩ := h
        obtain ⟨j,hj,hr,hs⟩ := ih
        exact hs.head (Or.inr ⟨i,j,hi,hj,hr,rfl,rfl⟩)
      | inr w => exact ih.head (Or.inl h)

theorem lift_local_reach {x y : A} (h : Relation.ReflTransGen r x y) :
    Relation.ReflTransGen (glued r s a b active) (.inl x) (.inl y) :=
  h.lift Sum.inl (fun _ _ h => h)

theorem lift_compressed_reach {x y : B}
    (h : Relation.ReflTransGen (compressed r s a b active) x y) :
    Relation.ReflTransGen (glued r s a b active) (.inr x) (.inr y) := by
  apply h.lift' Sum.inr
  intro x y he
  rcases he with he | ⟨i,j,hi,hj,hr,rfl,rfl⟩
  · exact .single he
  · exact ((lift_local_reach r s a b active hr).head ⟨i,hi,rfl,rfl⟩).tail
      ⟨j,hj,rfl,rfl⟩

theorem exterior_reach_iff {x y : B} :
    Relation.ReflTransGen (glued r s a b active) (.inr x) (.inr y) ↔
      Relation.ReflTransGen (compressed r s a b active) x y :=
  ⟨reach_to_exterior r s a b active, lift_compressed_reach r s a b active⟩

theorem interior_reach_iff {x : A} {y : B} :
    Relation.ReflTransGen (glued r s a b active) (.inl x) (.inr y) ↔
      ∃ i, active i ∧ Relation.ReflTransGen r x (a i) ∧
        Relation.ReflTransGen (compressed r s a b active) (b i) y := by
  refine ⟨reach_to_exterior r s a b active, ?_⟩
  rintro ⟨i,hi,hr,hs⟩
  have hc : Relation.ReflTransGen (glued r s a b active) (.inl x) (.inr (b i)) :=
    (lift_local_reach r s a b active hr).tail ⟨i,hi,rfl,rfl⟩
  exact hc.trans (lift_compressed_reach r s a b active hs)

 

def drains {V : Type*} (r : V → V → Prop) (out : V → Prop) : Prop :=
  ∀ v w, r v w → ∃ j, out j ∧ Relation.ReflTransGen r v j

def exteriorOutput (out : B → Prop) : Sum A B → Prop
  | .inl _ => False
  | .inr x => out x

 

theorem drains_glued_iff (out : B → Prop) :
    drains (glued r s a b active) (exteriorOutput out) ↔
      (∀ x y, r x y → ∃ i, active i ∧ Relation.ReflTransGen r x (a i)) ∧
      drains (compressed r s a b active) out := by
  constructor
  · intro h
    constructor
    · intro x y hxy
      obtain ⟨z,hz,hr⟩ := h (.inl x) (.inl y) hxy
      cases z with
      | inl z => exact hz.elim
      | inr z =>
        obtain ⟨i,hi,hr,_⟩ := reach_to_exterior r s a b active hr
        exact ⟨i,hi,hr⟩
    · intro x y hxy
      rcases hxy with hxy | ⟨i,j,hi,hj,hr,rfl,rfl⟩
      · obtain ⟨z,hz,hr⟩ := h (.inr x) (.inr y) hxy
        cases z with
        | inl z => exact hz.elim
        | inr z => exact ⟨z,hz,reach_to_exterior r s a b active hr⟩
      · obtain ⟨z,hz,hr⟩ := h (.inr (b i)) (.inl (a i)) ⟨i,hi,rfl,rfl⟩
        cases z with
        | inl z => exact hz.elim
        | inr z => exact ⟨z,hz,reach_to_exterior r s a b active hr⟩
  · rintro ⟨hl,he⟩ v w hvw
    cases v with
    | inl x =>
      have hx : ∃ i, active i ∧ Relation.ReflTransGen r x (a i) := by
        cases w with
        | inl y => exact hl x y hvw
        | inr y => obtain ⟨i,hi,rfl,rfl⟩ := hvw; exact ⟨i,hi,.refl⟩
      obtain ⟨i,hi,hr⟩ := hx
      obtain ⟨z,hz,hs⟩ := he (b i) (b i) (Or.inr ⟨i,i,hi,hi,.refl,rfl,rfl⟩)
      refine ⟨.inr z,hz,?_⟩
      exact (interior_reach_iff r s a b active).mpr ⟨i,hi,hr,hs⟩
    | inr x =>
      have hx : ∃ y, compressed r s a b active x y := by
        cases w with
        | inl y =>
          obtain ⟨i,hi,rfl,rfl⟩ := hvw
          exact ⟨b i,Or.inr ⟨i,i,hi,hi,.refl,rfl,rfl⟩⟩
        | inr y => exact ⟨y,Or.inl hvw⟩
      obtain ⟨y,hxy⟩ := hx
      obtain ⟨z,hz,hr⟩ := he x y hxy
      exact ⟨.inr z,hz,lift_compressed_reach r s a b active hr⟩

end
end CriticalStrip.Diagram.Patch

 

 

 

namespace CriticalStrip.Diagram
noncomputable section

structure ConnectivityCertificate {V : Type*} (r : V → V → Prop) where
  root : V → V
  parent : V → V
  rank : V → ℕ
  edge_root : ∀ x y, r x y → root x = root y
  parent_edge : ∀ x, x ≠ root x → r x (parent x)
  parent_rank : ∀ x, x ≠ root x → rank (parent x) < rank x

namespace ConnectivityCertificate
variable {V : Type*} {r : V → V → Prop} (c : ConnectivityCertificate r)

theorem reaches_root (x : V) : Relation.ReflTransGen r x (c.root x) := by
  classical
  generalize hk : c.rank x = k
  induction k using Nat.strong_induction_on generalizing x with
  | h k ih =>
    by_cases hx : x = c.root x
    · rw [← hx]
    · have hp := c.parent_edge x hx
      have hr := ih (c.rank (c.parent x)) (by rw [← hk]; exact c.parent_rank x hx)
        (c.parent x) rfl
      rw [← c.edge_root _ _ hp] at hr
      exact hr.head hp

theorem reach_root_eq {x y : V} (h : Relation.ReflTransGen r x y) : c.root x = c.root y := by
  induction h with
  | refl => rfl
  | @tail y z h he ih => exact ih.trans (c.edge_root _ _ he)

theorem reach_symm (hs : Std.Symm r) {x y : V} (h : Relation.ReflTransGen r x y) :
    Relation.ReflTransGen r y x := by
  induction h with
  | refl => exact .refl
  | tail hp he ih => exact ih.head (hs.symm _ _ he)

theorem reach_iff (hs : Std.Symm r) (x y : V) :
    Relation.ReflTransGen r x y ↔ c.root x = c.root y := by
  refine ⟨c.reach_root_eq, ?_⟩
  intro he
  have hx := c.reaches_root x
  rw [he] at hx
  exact hx.trans (reach_symm hs (c.reaches_root y))

end ConnectivityCertificate

instance tileAdjDecidable (t : Tile) : DecidableRel t.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∈ t.edges ∨ _ ∈ t.edges))

instance tileOccupiedDecidable (t : Tile) (i : Fin 4) : Decidable (t.Occupied i) :=
  inferInstanceAs (Decidable (∃ j, t.Adj i j))

@[simp] theorem Tile.adj_symm (t : Tile) {i j : Fin 4} : t.Adj i j ↔ t.Adj j i :=
  or_comm

end
end CriticalStrip.Diagram

 

 

 

namespace CriticalStrip.Diagram.ThreeBox
noncomputable section
open Finset

abbrev Config := Tile × Tile × Tile

def row (v : Fin 12) : Fin 3 := ⟨v.val/4, by have := v.isLt; omega⟩
def port (v : Fin 12) : Fin 4 := ⟨v.val%4, Nat.mod_lt _ (by decide)⟩
def atRow (t : Config) : Fin 3 → Tile := ![t.1,t.2.1,t.2.2]

def tileEdge (t : Config) (v w : Fin 12) : Prop :=
  row v = row w ∧ (atRow t (row v)).Adj (port v) (port w)

def wireEdge (a b v w : Fin 12) : Prop := (v=a ∧ w=b) ∨ (v=b ∧ w=a)

def Adj (t : Config) (v w : Fin 12) : Prop :=
  tileEdge t v w ∨
  (wireEdge 2 5 v w ∧ t.1.Occupied 2) ∨
  (wireEdge 3 9 v w ∧ t.1.Occupied 3) ∨
  (wireEdge 7 8 v w ∧ t.2.1.Occupied 3)

instance tileEdgeDecidable (t : Config) : DecidableRel (tileEdge t) := by
  intro v w; unfold tileEdge; infer_instance
instance wireEdgeDecidable (a b : Fin 12) : DecidableRel (wireEdge a b) := by
  intro v w; unfold wireEdge; infer_instance
instance adjDecidable (t : Config) : DecidableRel (Adj t) := by
  intro v w; unfold Adj; infer_instance

theorem tileEdge_symm (t : Config) {v w : Fin 12} (h : tileEdge t v w) : tileEdge t w v := by
  rcases h with ⟨he,he'⟩
  refine ⟨he.symm, ?_⟩
  rw [← he]
  exact (Tile.adj_symm _).mp he'

theorem wireEdge_symm {a b v w : Fin 12} (h : wireEdge a b v w) : wireEdge a b w v := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl⟩
  · exact Or.inl ⟨rfl,rfl⟩

theorem adj_symm (t : Config) : Std.Symm (Adj t) := by
  constructor
  intro v w h
  rcases h with h | ⟨h,ho⟩ | ⟨h,ho⟩ | ⟨h,ho⟩
  · exact Or.inl (tileEdge_symm t h)
  · exact Or.inr (Or.inl ⟨wireEdge_symm h,ho⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨wireEdge_symm h,ho⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨wireEdge_symm h,ho⟩))

 
def Compatible (t : Config) : Prop :=
  (t.1.Occupied 2 ↔ t.2.1.Occupied 1) ∧
  (t.1.Occupied 3 ↔ t.2.2.Occupied 1) ∧
  (t.2.1.Occupied 3 ↔ t.2.2.Occupied 0)
instance compatibleDecidable (t : Config) : Decidable (Compatible t) := by
  unfold Compatible; infer_instance

 
def boundary : Fin 6 → Fin 12 := ![4,0,1,6,10,11]
def boundaryOccupied (t : Config) (i : Fin 6) : Prop :=
  (atRow t (row (boundary i))).Occupied (port (boundary i))
instance boundaryOccupiedDecidable (t : Config) (i : Fin 6) : Decidable (boundaryOccupied t i) := by
  unfold boundaryOccupied; infer_instance

def boundaryAdj (d : Finset (Fin 6 × Fin 6)) (i j : Fin 6) : Prop :=
  (i,j) ∈ d ∨ (j,i) ∈ d

def boundarySupport (d : Finset (Fin 6 × Fin 6)) (i : Fin 6) : Prop :=
  ∃ j, boundaryAdj d i j

 

structure Realizes (t : Config) (d : Finset (Fin 6 × Fin 6)) : Prop where
  compatible : Compatible t
  occupied : ∀ i, boundaryOccupied t i ↔ boundarySupport d i
  no_loop : ∀ v w, Adj t v w → ∃ i, boundaryOccupied t i ∧
    Relation.ReflTransGen (Adj t) v (boundary i)
  output : ∀ i j, i ≠ j → (boundaryAdj d i j ↔
    Relation.ReflTransGen (Adj t) (boundary i) (boundary j))

end
end CriticalStrip.Diagram.ThreeBox

end OAI
