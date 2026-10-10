import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.PatchCycles

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace PortPatch.ParentPath
variable {m : ℕ} {V I A B : Fin (m+1) → Type} {k : (t : Fin (m+1)) → V t → Kind}
variable (P : (t : Fin (m+1)) → PortPatch (k t) (I t) (A t) (B t))
variable (e : ((t : Fin (m+1)) × A t) ≃ ((t : Fin (m+1)) × B t))
variable (he : ∀ a, (familyKind k ((family P).minus (.inr (e a))).val.1).arity
      ((family P).minus (.inr (e a))).val.2 =
      (familyKind k ((family P).plus (.inr a)).val.1).arity ((family P).plus (.inr a)).val.2)
variable {a : (t : Fin (m+1)) → A t} {b : (t : Fin (m+1)) → B t}
variable {n : Fin (m+1) → ℕ}
variable (C : (t : Fin (m+1)) → ParentPath (P t) (n t) (a t) (b t))
variable {F : Type}
variable (facet : Side ((family P).complete e he).Seam ((family P).complete e he).seamArity → F)
variable (hc : ∀ x, facet (((family P).complete e he).sideOf (localMate x))=
  facet (((family P).complete e he).sideOf x))
variable (route : ∀ t, e.symm ⟨t,b t⟩=⟨⟨(t.val+1)%(m+1),Nat.mod_lt _ (Nat.succ_pos _)⟩,
  a ⟨(t.val+1)%(m+1),Nat.mod_lt _ (Nat.succ_pos _)⟩⟩)

include route in
/-- Boundary connectedness for mixed replacement patches with different numbers of events. The only closure equation is exterior lane sewing. -/
theorem variable_connected (t : Fin (m+1)) (j : Fin (n t+1)) :
    (((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext.SameCycle
      (((family P).complete e he).sideOf (familyEnd k 0 ((C 0).node 0)))
      (((family P).complete e he).sideOf (familyEnd k t ((C t).node j))) := by
  apply IntegralCharacterVarieties.FiniteCycles.variableCyclic_sameCycle
    (((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext n
    (fun t j => ((family P).complete e he).sideOf (familyEnd k t ((C t).node j)))
    (fun t i => (C t).boundary_step P e he facet hc i)
    (fun t => ?_) t j
  rw [PortWiring.boundaryNext_local]
  · rw [familyEnd_mate,(C t).last_side P e he,route t]
    exact ((C _).first_side P e he).symm
  · change (k t ((C t).node (Fin.last (n t))).1).table.endpoint
        ((C t).node (Fin.last (n t))).2.1=((C t).node (Fin.last (n t))).2.2.isNone
    rw [(C t).parent,(C t).positive]
    rfl

variable [Finite ((family P).complete e he).Seam]
include route in
/-- Exhaustive local parent-germ coverage closes the whole named facet, not merely an embedded selected path. Coverage is a finite table proposition; it is deliberately not asserted for arbitrary unverified templates. -/
theorem variable_boundary_count (u : F)
    (hstart : facet (((family P).complete e he).sideOf (familyEnd k 0 ((C 0).node 0)))=u)
    (cover : ∀ z, facet z=u → ∃ t j,
      ((family P).complete e he).sideOf (familyEnd k t ((C t).node j))=z) :
    IntegralCharacterVarieties.FiniteCycles.componentCount
      (((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext facet u=1 := by
  apply IntegralCharacterVarieties.FiniteCycles.componentCount_of_connected
    (((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext facet
    (fun z => (((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext_facet z) u
    (((family P).complete e he).sideOf (familyEnd k 0 ((C 0).node 0))) hstart
  intro z hz
  obtain ⟨t,j,rfl⟩ := cover z hz
  exact variable_connected P e he C facet hc route t j
include route in
/-- The check needed on local templates is just exhaustion by parent corners. Both side-germ occurrences are allowed, and the corner permutation carries the input to its mate. Repeated facet names are not erased. -/
theorem variable_boundary_count_germs (u : F)
    (hstart : facet (((family P).complete e he).sideOf (familyEnd k 0 ((C 0).node 0)))=u)
    (cover : ∀ t (x : LocalEnd (V t) (k t)),
      facet (((family P).complete e he).sideOf (familyEnd k t x))=u →
      ∃ j, x=(C t).node j ∨ x=localMate ((C t).node j)) :
    IntegralCharacterVarieties.FiniteCycles.componentCount
      (((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext facet u=1 := by
  apply IntegralCharacterVarieties.FiniteCycles.componentCount_of_connected
    (((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext facet
    (fun z => (((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext_facet z) u
    (((family P).complete e he).sideOf (familyEnd k 0 ((C 0).node 0))) hstart
  intro z hz
  obtain ⟨⟨⟨t,v⟩,p,c⟩,rfl⟩ := ((family P).complete e he).sideOf_surjective z
  obtain ⟨j,hj|hj⟩ := cover t ⟨v,p,c⟩ hz
  · change (((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext.SameCycle _ (((family P).complete e he).sideOf (familyEnd k t ⟨v,p,c⟩))
    rw [hj]
    exact variable_connected P e he C facet hc route t j
  · change (((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext.SameCycle _ (((family P).complete e he).sideOf (familyEnd k t ⟨v,p,c⟩))
    rw [hj,← familyEnd_mate]
    have h := variable_connected P e he C facet hc route t j
    have hstep : (((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext
        (((family P).complete e he).sideOf (familyEnd k t ((C t).node j)))=
        ((family P).complete e he).sideOf (localMate (familyEnd k t ((C t).node j))) := by
      apply PortWiring.boundaryNext_local
      change (k t ((C t).node j).1).table.endpoint ((C t).node j).2.1=((C t).node j).2.2.isNone
      rw [(C t).parent,(C t).positive]
      rfl
    rw [← hstep]
    exact h.trans ⟨1,by simp⟩
end PortPatch.ParentPath
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type}

/-- All nonprincipal facet names remain explicit and may repeat. The new disk parent is a separate name, not a replacement or quotient of old facet names. -/
def Kind.SecondaryNames (F : Type) : Kind → Type
  | .passage m _ => Fin m → F
  | .splitting a b c _ => F × (Fin a → F) × (Fin b → F) × (Fin c → F)

def Kind.freshDecoration : (k : Kind) → k.SecondaryNames F → Decoration k (Option F)
  | .passage _ t, kids => passageDecoration t none (fun j => some (kids j))
  | .splitting _ _ _ r, labels =>
    splittingDecoration r none (some labels.1) (fun j => some (labels.2.1 j))
      (fun j => some (labels.2.2.1 j)) (fun j => some (labels.2.2.2 j))

/-- No lower facet, even a repeated one, can be mistaken for the fresh parent in any permitted passage, split, or merge table. -/
lemma Kind.fresh_color_none (k : Kind) (d : k.SecondaryNames F)
    (z : (p : k.table.Port) × Option (k.table.Child p)) :
    (k.freshDecoration d).color z=none ↔ z=⟨k.input,none⟩ ∨ z=⟨k.output,none⟩ := by
  cases k with
  | passage m t =>
    rcases z with ⟨p,c⟩
    cases p <;> cases c with
    | none => simp [Kind.freshDecoration,passageDecoration,Kind.input,Kind.output]
    | some j => exact ⟨fun h => (by cases h), fun h => by rcases h with h|h <;> cases h⟩
  | splitting a b c r =>
    cases r <;> rcases z with ⟨p,z⟩ <;> cases p <;> cases z with
    | none => first
      | exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
      | exact ⟨fun _ => Or.inr rfl, fun _ => rfl⟩
      | exact ⟨fun h => (by cases h), fun h => by rcases h with h|h <;> cases h⟩
    | some j =>
      first
      | exact ⟨fun h => (by cases h), fun h => by rcases h with h|h <;> cases h⟩
      | (rcases j with j|j|j <;>
          exact ⟨fun h => (by cases h), fun h => by rcases h with h|h <;> cases h⟩)
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

namespace IntegralCharacterVarieties.OccurrenceIncidence.VariableGallery
open scoped Classical
open VertexTable
namespace Cyclic
variable {m : ℕ} (n : Fin (m+1) → ℕ) (k : (t : Fin (m+1)) → Fin (n t+1) → Kind)
variable (ha : ∀ t (j : Fin (n t)), (k t j.castSucc).arity (k t j.castSucc).output=
  (k t j.succ).arity (k t j.succ).input)
abbrev patches := fun t => patch (k t) (ha t)
abbrev In (t : Fin (m+1)) := {p : PortAt (k t) true // p∉Set.range (internalPlus (k t))}
abbrev Out (t : Fin (m+1)) := {p : PortAt (k t) false // p∉Set.range (internalMinus (k t))}
variable (e : ((t : Fin (m+1)) × In n k t) ≃ ((t : Fin (m+1)) × Out n k t))
variable (he : ∀ a, (familyKind k ((PortPatch.family (patches n k ha)).minus (.inr (e a))).val.1).arity
      ((PortPatch.family (patches n k ha)).minus (.inr (e a))).val.2 =
      (familyKind k ((PortPatch.family (patches n k ha)).plus (.inr a)).val.1).arity
      ((PortPatch.family (patches n k ha)).plus (.inr a)).val.2)
abbrev wiring := (PortPatch.family (patches n k ha)).complete e he
variable {F : Type} (labels : ∀ t v, (k t v).SecondaryNames F)
abbrev colors := familyDecoration (fun t v => (k t v).freshDecoration (labels t v))
variable (hd : (wiring n k ha e he).ColorCompatible (colors n k labels))
abbrev assembly := (wiring n k ha e he).fromDecoration (colors n k labels) hd
include hd in
lemma color_mate (x) :
    (wiring n k ha e he).coloredFacet (colors n k labels) ( (wiring n k ha e he).sideOf (localMate x)) =
    (wiring n k ha e he).coloredFacet (colors n k labels) ( (wiring n k ha e he).sideOf x) := by
  rw [PortWiring.sideOf_color _ _ hd,PortWiring.sideOf_color _ _ hd]
  exact ((colors n k labels) x.1).corner x.2

variable (route : ∀ t, e.symm ⟨t,⟨output (k t) (Fin.last (n t)),last_exposed (k t)⟩⟩=
  ⟨⟨(t.val+1)%(m+1),Nat.mod_lt _ (Nat.succ_pos _)⟩,
   ⟨input (k ⟨(t.val+1)%(m+1),Nat.mod_lt _ (Nat.succ_pos _)⟩) 0,
      first_exposed (k ⟨(t.val+1)%(m+1),Nat.mod_lt _ (Nat.succ_pos _)⟩)⟩⟩)
include route in
/-- Unequal-length galleries of ANY permitted event kinds, with all explicit old child names and split branches retained, close to one fresh parent boundary. No local exhaustion hypothesis is left: it follows from the tables. -/
theorem parent_boundary_count : IntegralCharacterVarieties.FiniteCycles.componentCount
    (assembly n k ha e he labels hd).vertexAssembly.corners.boundaryNext
    ((wiring n k ha e he).coloredFacet (colors n k labels)) none=1 := by
  apply PortPatch.ParentPath.variable_boundary_count_germs (patches n k ha) e he
    (fun t => parentPath (k t) (ha t))
    ((wiring n k ha e he).coloredFacet (colors n k labels))
    (color_mate n k ha e he labels hd) route none
  · rw [PortWiring.sideOf_color _ _ hd]
    exact ((k 0 0).fresh_color_none (labels 0 0) _).2 (Or.inl rfl)
  · intro t x hx
    rw [PortWiring.sideOf_color _ _ hd] at hx
    rcases x with ⟨v,p,c⟩
    change ((k t v).freshDecoration (labels t v)).color ⟨p,c⟩=none at hx
    obtain h|h := ((k t v).fresh_color_none (labels t v) _).1 hx
    · refine ⟨v,Or.inl ?_⟩
      exact congrArg (fun z => (⟨v,z⟩ : LocalEnd _ (k t))) h
    · refine ⟨v,Or.inr ?_⟩
      change (⟨v,p,c⟩ : LocalEnd _ (k t))=localMate ⟨v,(k t v).input,none⟩
      rw [parent_corner (k t)]
      exact congrArg (fun z => (⟨v,z⟩ : LocalEnd _ (k t))) h
end Cyclic
end IntegralCharacterVarieties.OccurrenceIncidence.VariableGallery


namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable

/-- Verified local data, with port tables and parent corner exhaustion. -/
structure ParentTemplate (F : Type) where
  V : Type
  I : Type
  A : Type
  B : Type
  finiteV : Finite V
  kind : V → Kind
  patch : PortPatch kind I A B
  input : A
  output : B
  length : ℕ
  path : PortPatch.ParentPath patch length input output
  decoration : (v : V) → Decoration (kind v) (Option F)
  nodes : ∀ j, (decoration (path.node j).1).color (path.node j).2=none
  exhaustive : ∀ x : LocalEnd V kind, (decoration x.1).color x.2=none →
    ∃ j, x=path.node j ∨ x=localMate (path.node j)
attribute [instance] ParentTemplate.finiteV

namespace ParentTemplate
variable {F : Type}
/-- Full gallery; no side branches have been dropped. -/
noncomputable def gallery {l : ℕ} (k : Fin (l+1) → Kind)
    (ha : ∀ j : Fin l, (k j.castSucc).arity (k j.castSucc).output=
      (k j.succ).arity (k j.succ).input)
    (d : ∀ v, (k v).SecondaryNames F) : ParentTemplate F where
  V := Fin (l+1)
  I := Fin l
  A := {p : PortAt k true // p∉Set.range (VariableGallery.internalPlus k)}
  B := {p : PortAt k false // p∉Set.range (VariableGallery.internalMinus k)}
  finiteV := inferInstance
  kind := k
  patch := VariableGallery.patch k ha
  input := ⟨VariableGallery.input k 0,VariableGallery.first_exposed k⟩
  output := ⟨VariableGallery.output k (Fin.last l),VariableGallery.last_exposed k⟩
  length := l
  path := VariableGallery.parentPath k ha
  decoration v := (k v).freshDecoration (d v)
  nodes j := ((k j).fresh_color_none (d j) _).2 (Or.inl rfl)
  exhaustive x hx := by
    obtain ⟨v,p,c⟩ := x
    obtain h|h := ((k v).fresh_color_none (d v) _).1 hx
    · exact ⟨v,Or.inl (congrArg (fun z => (⟨v,z⟩ : LocalEnd _ k)) h)⟩
    · refine ⟨v,Or.inr ?_⟩
      change (⟨v,p,c⟩ : LocalEnd _ k)=localMate ⟨v,(k v).input,none⟩
      rw [VariableGallery.parent_corner k]
      exact congrArg (fun z => (⟨v,z⟩ : LocalEnd _ k)) h


def complementColor (d : ComplementaryPatch.Facet → F) (c : ComplementaryPatch.Facet) : Option F :=
  if c=.U then none else some (d c)

lemma complementColor_none (d : ComplementaryPatch.Facet → F) (c : ComplementaryPatch.Facet) :
    complementColor d c=none ↔ c=.U := by
  by_cases h : c=.U <;> simp [complementColor,h]

noncomputable def complementary (d : ComplementaryPatch.Facet → F) : ParentTemplate F where
  V := ComplementaryPatch.Vertex
  I := Fin 10
  A := Fin 4
  B := Fin 4
  finiteV := inferInstance
  kind := ComplementaryPatch.kind
  patch := ComplementaryPatch.patch
  input := 0
  output := 0
  length := 2
  path := ComplementaryPatch.uParentPath
  decoration v := (ComplementaryPatch.decoration v).map (complementColor d)
  nodes j := by
    change complementColor d _=none
    exact (complementColor_none d _).2 (ComplementaryPatch.parent_path_colors.1 j)
  exhaustive x hx :=
    ComplementaryPatch.u_parent_exhaustive x ((complementColor_none d _).1 hx)


inductive Recipe (F : Type) where
  | ordinary (l : ℕ) (k : Fin (l+1) → Kind)
      (ha : ∀ j : Fin l, (k j.castSucc).arity (k j.castSucc).output=
        (k j.succ).arity (k j.succ).input)
      (d : ∀ v, (k v).SecondaryNames F)
  | swap (d : ComplementaryPatch.Facet → F)

noncomputable def Recipe.template : Recipe F → ParentTemplate F
  | .ordinary _ k ha d => gallery k ha d
  | .swap d => complementary d
end ParentTemplate
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.OccurrenceIncidence.ParentTemplate
open scoped Classical
open VertexTable
namespace Cyclic
variable {F : Type} {m : ℕ} (R : Fin (m+1) → Recipe F)
abbrev templates := fun t => (R t).template
abbrev kinds := fun t => (templates R t).kind
abbrev patches := fun t => (templates R t).patch
abbrev colors := familyDecoration (fun t => (templates R t).decoration)
variable (e : ((t : Fin (m+1)) × (templates R t).A) ≃
  ((t : Fin (m+1)) × (templates R t).B))
variable (he : ∀ a, (familyKind (kinds R) ((PortPatch.family (patches R)).minus (.inr (e a))).val.1).arity
      ((PortPatch.family (patches R)).minus (.inr (e a))).val.2 =
      (familyKind (kinds R) ((PortPatch.family (patches R)).plus (.inr a)).val.1).arity
      ((PortPatch.family (patches R)).plus (.inr a)).val.2)
abbrev wiring := (PortPatch.family (patches R)).complete e he
variable (hd : (wiring R e he).ColorCompatible (colors R))
abbrev assembly := (wiring R e he).fromDecoration (colors R) hd
include hd in
lemma color_mate (x) :
    (wiring R e he).coloredFacet (colors R) ((wiring R e he).sideOf (localMate x))=
    (wiring R e he).coloredFacet (colors R) ((wiring R e he).sideOf x) := by
  rw [PortWiring.sideOf_color _ _ hd,PortWiring.sideOf_color _ _ hd]
  exact (colors R x.1).corner x.2
variable (route : ∀ t, e.symm ⟨t,(templates R t).output⟩=
  ⟨⟨(t.val+1)%(m+1),Nat.mod_lt _ (Nat.succ_pos _)⟩,
  (templates R ⟨(t.val+1)%(m+1),Nat.mod_lt _ (Nat.succ_pos _)⟩).input⟩)
include route in
/-- Every finite cyclic mixture of the ordinary/split/merge gallery and nonregular complementary templates has one full fresh-parent boundary. All other entire ports are still sewn by the original arbitrary exterior e; no side-germ or old facet label has been discarded by this theorem. -/
theorem parent_boundary_count : IntegralCharacterVarieties.FiniteCycles.componentCount
    (assembly R e he hd).vertexAssembly.corners.boundaryNext
    ((wiring R e he).coloredFacet (colors R)) none=1 := by
  apply PortPatch.ParentPath.variable_boundary_count_germs (patches R) e he
    (fun t => (templates R t).path) ((wiring R e he).coloredFacet (colors R))
    (color_mate R e he hd) route none
  · rw [PortWiring.sideOf_color _ _ hd]
    exact (templates R 0).nodes 0
  · intro t x hx
    rw [PortWiring.sideOf_color _ _ hd] at hx
    exact (templates R t).exhaustive x hx
end Cyclic
end IntegralCharacterVarieties.OccurrenceIncidence.ParentTemplate


namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
namespace CyclicInterface
variable {m : ℕ} {A B : Fin (m+1) → Type}
variable (a : (t : Fin (m+1)) → A t) (b : (t : Fin (m+1)) → B t)

def distinguished : Fin (m+1) ↪ ((t : Fin (m+1)) × A t) where
  toFun t := ⟨t,a t⟩
  inj' _ _ h := congrArg Sigma.fst h
abbrev OtherIn := {p : (t : Fin (m+1)) × A t // p∉Set.range (distinguished a)}
abbrev OtherOut := {p : (t : Fin (m+1)) × B t // p∉Set.range (distinguished b)}

/-- Sewing consumes exactly each designated parent interface once. -/
noncomputable def sew (rest : OtherIn a ≃ OtherOut b) :
    ((t : Fin (m+1)) × A t) ≃ ((t : Fin (m+1)) × B t) :=
  (includeComplement (distinguished a)).symm |>.trans
    ((Equiv.sumCongr (finRotate (m+1)).symm rest).trans (includeComplement (distinguished b)))

lemma sew_parent (rest : OtherIn a ≃ OtherOut b) (t : Fin (m+1)) :
    (sew a b rest).symm ⟨t,b t⟩=⟨finRotate (m+1) t,a (finRotate (m+1) t)⟩ := by
  change includeComplement (distinguished a)
    ((Equiv.sumCongr (finRotate (m+1)).symm rest).symm
      ((includeComplement (distinguished b)).symm
        ((includeComplement (distinguished b)) (.inl t))))=_
  rw [Equiv.symm_apply_apply]
  rfl

lemma sew_other (rest : OtherIn a ≃ OtherOut b) (p : OtherIn a) :
    sew a b rest p.val=(rest p).val := by
  change includeComplement (distinguished b)
    ((Equiv.sumCongr (finRotate (m+1)).symm rest)
      ((includeComplement (distinguished a)).symm
        ((includeComplement (distinguished a)) (.inr p))))=_
  rw [Equiv.symm_apply_apply]
  rfl

lemma rotate_mod (t : Fin (m+1)) : finRotate (m+1) t=
    ⟨(t.val+1)%(m+1),Nat.mod_lt _ (Nat.succ_pos _)⟩ := by
  by_cases h : t.val < m
  · have ht : t=⟨t.val,h.trans_le (Nat.le_succ _)⟩ := Fin.ext rfl
    rw [ht,finRotate_of_lt h]
    apply Fin.ext
    exact (Nat.mod_eq_of_lt (Nat.succ_lt_succ h)).symm
  · have ht : t=Fin.last m := by apply Fin.ext; have := t.isLt; dsimp; omega
    rw [ht,finRotate_last]
    apply Fin.ext
    simp

lemma sew_route (rest : OtherIn a ≃ OtherOut b) (t : Fin (m+1)) :
    (sew a b rest).symm ⟨t,b t⟩=
      ⟨⟨(t.val+1)%(m+1),Nat.mod_lt _ (Nat.succ_pos _)⟩,
        a ⟨(t.val+1)%(m+1),Nat.mod_lt _ (Nat.succ_pos _)⟩⟩ := by
  rw [sew_parent,rotate_mod]
end CyclicInterface
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.OccurrenceIncidence.ParentTemplate
open scoped Classical
open VertexTable
namespace Sewn
variable {F : Type} {m : ℕ} (R : Fin (m+1) → Recipe F)
abbrev input := fun t => (Cyclic.templates R t).input
abbrev output := fun t => (Cyclic.templates R t).output
variable (rest : CyclicInterface.OtherIn (input R) ≃ CyclicInterface.OtherOut (output R))
noncomputable abbrev exterior := CyclicInterface.sew (input R) (output R) rest
variable (he : ∀ a, (familyKind (Cyclic.kinds R)
      ((PortPatch.family (Cyclic.patches R)).minus (.inr (exterior R rest a))).val.1).arity
      ((PortPatch.family (Cyclic.patches R)).minus (.inr (exterior R rest a))).val.2 =
      (familyKind (Cyclic.kinds R) ((PortPatch.family (Cyclic.patches R)).plus (.inr a)).val.1).arity
      ((PortPatch.family (Cyclic.patches R)).plus (.inr a)).val.2)
variable (hd : (Cyclic.wiring R (exterior R rest) he).ColorCompatible (Cyclic.colors R))

/-- The exterior sewing is constructed, not hypothesized; cyclic closure of all mixed parent routes and exhaustion of this facet follow. `rest` retains every exposed old/branch port, as `CyclicInterface.sew_other` proves. -/
theorem parent_boundary_count : IntegralCharacterVarieties.FiniteCycles.componentCount
    (Cyclic.assembly R (exterior R rest) he hd).vertexAssembly.corners.boundaryNext
    ((Cyclic.wiring R (exterior R rest) he).coloredFacet (Cyclic.colors R)) none=1 :=
  Cyclic.parent_boundary_count R (exterior R rest) he hd
    (CyclicInterface.sew_route (input R) (output R) rest)
end Sewn
end IntegralCharacterVarieties.OccurrenceIncidence.ParentTemplate


namespace IntegralCharacterVarieties.OccurrenceIncidence.CyclicInterface
open scoped Classical
variable {m : ℕ} {A B : Fin (m+1) → Type}
variable (a : (t : Fin (m+1)) → A t) (b : (t : Fin (m+1)) → B t)
variable (e : ((t : Fin (m+1)) × A t) ≃ ((t : Fin (m+1)) × B t))
variable (route : ∀ t, e.symm (distinguished b t)=
    distinguished a (finRotate (m+1) t))
include route in
lemma forward (t : Fin (m+1)) : e (distinguished a t)=
    distinguished b ((finRotate (m+1)).symm t) := by
  have h := route ((finRotate (m+1)).symm t)
  rw [Equiv.apply_symm_apply] at h
  exact (congrArg e h).symm.trans (e.apply_symm_apply _)

include route in
lemma parent_range_iff (p : (t : Fin (m+1)) × A t) :
    e p ∈ Set.range (distinguished b) ↔ p ∈ Set.range (distinguished a) := by
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨finRotate (m+1) t, ?_⟩
    have h := congrArg e.symm ht
    rw [route,Equiv.symm_apply_apply] at h
    exact h
  · rintro ⟨t,rfl⟩
    exact ⟨(finRotate (m+1)).symm t,(forward a b e route t).symm⟩

/-- Restriction to all residual occurrences is an invertible matching, not a choice of matching with the right cardinality. -/
noncomputable def recover : OtherIn a ≃ OtherOut b where
  toFun p := ⟨e p,fun h => p.property ((parent_range_iff a b e route p).1 h)⟩
  invFun q := ⟨e.symm q,fun h => q.property (by
    have h' := (parent_range_iff a b e route (e.symm q)).2 h
    simpa only [Equiv.apply_symm_apply] using h')⟩
  left_inv p := Subtype.ext (e.symm_apply_apply p)
  right_inv q := Subtype.ext (e.apply_symm_apply q)

/-- Exhaustiveness of the concrete cyclic sewing: every original matching with the given parent route is returned literally, also off that route. -/
theorem sew_recover : sew a b (recover a b e route)=e := by
  apply Equiv.ext
  intro p
  by_cases hp : p∈Set.range (distinguished a)
  · rcases hp with ⟨t,rfl⟩
    rw [forward a b (sew a b (recover a b e route))
      (sew_parent a b (recover a b e route)), forward a b e route]
  · exact sew_other a b (recover a b e route) ⟨p,hp⟩

/-- No arbitrary complement choice survives in the data: the original old matching on every branch is recovered from its sewing. -/
theorem recover_sew (rest : OtherIn a ≃ OtherOut b) :
    recover a b (sew a b rest) (sew_parent a b rest)=rest := by
  apply Equiv.ext
  intro p
  apply Subtype.ext
  exact sew_other a b rest p
end IntegralCharacterVarieties.OccurrenceIncidence.CyclicInterface
namespace IntegralCharacterVarieties.OccurrenceIncidence.CyclicInterface
open scoped Classical
variable {m : ℕ} {A B : Fin (m+1) → Type}
variable (a : (t : Fin (m+1)) → A t) (b : (t : Fin (m+1)) → B t)
/-- All old exterior matchings with the matching parent cycle, including every separate branch occurrence. This is a subtype of finite interface data. -/
def Routed := {e : ((t : Fin (m+1)) × A t) ≃ ((t : Fin (m+1)) × B t) //
  ∀ t, e.symm (distinguished b t)=distinguished a (finRotate (m+1) t)}

/-- The concrete producer is exhaustive and has an explicit inverse. Neither surviving external side germs nor their previous matchings are quotient out. -/
noncomputable def parametrization : (OtherIn a ≃ OtherOut b) ≃ Routed a b where
  toFun rest := ⟨sew a b rest,sew_parent a b rest⟩
  invFun e := recover a b e.val e.property
  left_inv rest := recover_sew a b rest
  right_inv e := Subtype.ext (sew_recover a b e.val e.property)
end IntegralCharacterVarieties.OccurrenceIncidence.CyclicInterface
namespace IntegralCharacterVarieties.OccurrenceIncidence.CyclicInterface
open scoped Classical
variable {m : ℕ} {A B : Fin (m+1) → Type}
variable (a : (t : Fin (m+1)) → A t) (b : (t : Fin (m+1)) → B t)

/-- Literally all seam equations split into their cyclic parent interface and their unchanged old branch equations. The relation may encode arities, ordered graded names or equality of coefficient-ring transport matrices. -/
theorem compatible_iff (rest : OtherIn a ≃ OtherOut b)
    (R : ((t : Fin (m+1)) × A t) → ((t : Fin (m+1)) × B t) → Prop) :
    (∀ p, R p (sew a b rest p)) ↔
      (∀ t, R (distinguished a t) (distinguished b ((finRotate (m+1)).symm t))) ∧
      (∀ p : OtherIn a, R p.val (rest p).val) := by
  constructor
  · intro h
    constructor
    · intro t
      simpa only [forward a b (sew a b rest) (sew_parent a b rest)] using
        h (distinguished a t)
    · intro p
      simpa only [sew_other a b rest p] using h p.val
  · rintro ⟨hp,hr⟩ p
    by_cases h : p∈Set.range (distinguished a)
    · rcases h with ⟨t,rfl⟩
      rw [forward a b (sew a b rest) (sew_parent a b rest)]
      exact hp t
    · rw [sew_other a b rest (⟨p,h⟩ : OtherIn a)]
      exact hr ⟨p,h⟩
end IntegralCharacterVarieties.OccurrenceIncidence.CyclicInterface


namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
namespace ParentTemplate.Recipe
variable {F : Type}
instance finiteInput (r : Recipe F) : Finite r.template.A := by
  cases r <;> dsimp only [Recipe.template,gallery,complementary] <;> infer_instance
instance finiteOutput (r : Recipe F) : Finite r.template.B := by
  cases r <;> dsimp only [Recipe.template,gallery,complementary] <;> infer_instance
end ParentTemplate.Recipe

namespace FiniteRoutedFamily
variable {J F : Type} [Finite J] (m : J → ℕ)
variable (R : (j : J) → Fin (m j+1) → ParentTemplate.Recipe F)
abbrev In (j : J) := (t : Fin (m j+1)) × (ParentTemplate.Cyclic.templates (R j) t).A
abbrev Out (j : J) := (t : Fin (m j+1)) × (ParentTemplate.Cyclic.templates (R j) t).B
abbrev Residual (j : J) :=
  CyclicInterface.OtherIn (ParentTemplate.Sewn.input (R j)) ≃
    CyclicInterface.OtherOut (ParentTemplate.Sewn.output (R j))
/-- Finite rank-array choices and finite old-branch matchings together, with NO identification of occurrences sharing their facet name. -/
abbrev Index := (j : J) × Residual m R j
instance finiteIn (j : J) : Finite (In m R j) := by
  dsimp only [In,ParentTemplate.Cyclic.templates]
  infer_instance
instance finiteOut (j : J) : Finite (Out m R j) := by
  dsimp only [Out,ParentTemplate.Cyclic.templates]
  infer_instance
instance finiteResidual (j : J) : Finite (Residual m R j) := by
  let : Fintype (In m R j) := Fintype.ofFinite _
  let : Fintype (Out m R j) := Fintype.ofFinite _
  let : Fintype (CyclicInterface.OtherIn (ParentTemplate.Sewn.input (R j))) :=
    Fintype.ofFinite _
  let : Fintype (CyclicInterface.OtherOut (ParentTemplate.Sewn.output (R j))) :=
    Fintype.ofFinite _
  exact Finite.of_fintype _
instance finiteIndex : Finite (Index m R) := inferInstance

noncomputable def produce (i : Index m R) : (j : J) × (In m R j ≃ Out m R j) :=
  ⟨i.1,ParentTemplate.Sewn.exterior (R i.1) i.2⟩

omit [Finite J] in
/-- Every original routed matching appears LITERALLY in the finite family. -/
theorem exhaustive (j : J) (e : In m R j ≃ Out m R j)
    (route : ∀ t, e.symm (CyclicInterface.distinguished (ParentTemplate.Sewn.output (R j)) t)=
      CyclicInterface.distinguished (ParentTemplate.Sewn.input (R j))
        (finRotate (m j+1) t)) :
    ∃ i : Index m R, produce m R i=⟨j,e⟩ := by
  refine ⟨⟨j,CyclicInterface.recover (ParentTemplate.Sewn.input (R j))
    (ParentTemplate.Sewn.output (R j)) e route⟩, ?_⟩
  exact congrArg (fun z : In m R j ≃ Out m R j =>
    (⟨j,z⟩ : (j : J) × (In m R j ≃ Out m R j)))
    (CyclicInterface.sew_recover (ParentTemplate.Sewn.input (R j))
      (ParentTemplate.Sewn.output (R j)) e route)
end FiniteRoutedFamily
end IntegralCharacterVarieties.OccurrenceIncidence

end

end OAI
