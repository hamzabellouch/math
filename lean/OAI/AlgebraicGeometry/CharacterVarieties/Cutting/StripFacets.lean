import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.PortSurgery

namespace OAI

/-!
# Connected-strip facet labels and the refined atomic graft.

This formalizes the band reconstruction for filtered surface local systems in
*Integral points on character varieties of curves*.
-/

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace PortWiring
variable {V F : Type} {kind : V → Kind} (W : PortWiring kind)
noncomputable def boundaryPerm : Equiv.Perm (Side W.Seam W.seamArity) :=
  (W.assemble (fun _ => ()) (fun _ => rfl)).vertexAssembly.corners.boundaryNext
lemma boundaryPerm_local (x : LocalEnd V kind)
    (hx : (kind x.1).table.endpoint x.2.1=x.2.2.isNone) :
    W.boundaryPerm (W.sideOf x)=W.sideOf (localMate x) :=
  W.boundaryNext_local _ _ x hx

lemma cornerColor_of_boundary (f : Side W.Seam W.seamArity → F)
    (h : ∀ a,f (W.boundaryPerm a)=f a) (x : LocalEnd V kind) :
    f (W.sideOf (localMate x))=f (W.sideOf x) := by
  by_cases hx : (kind x.1).table.endpoint x.2.1=x.2.2.isNone
  · rw [←W.boundaryPerm_local x hx,h]
  · have hy := (kind x.1).table.orientation x.2 |>.mpr hx
    have hm := h (W.sideOf (localMate x))
    rw [W.boundaryPerm_local _ hy] at hm
    have hi : localMate (localMate x)=x := by
      rcases x with ⟨v,z⟩
      exact congrArg (Sigma.mk v) ((kind v).table.involutive z)
    rw [hi] at hm
    exact hm.symm

noncomputable def assembleBoundary (f : Side W.Seam W.seamArity → F)
    (h : ∀ a,f (W.boundaryPerm a)=f a) : PortAssembly F W.Seam V W.seamArity :=
  W.assemble f (W.cornerColor_of_boundary f h)

/-- Carry a cycle-constant facet assignment through the actual whole-port
surgery. The two invariances are finite combinatorial checks, not a solution,
coverage, or chart hypothesis. -/
noncomputable def rewireFacets (C : Equiv.Perm W.Seam)
    (hC : ∀ s,W.seamArity (C s)=W.seamArity s)
    (f : Side W.Seam W.seamArity → F)
    (hn : ∀ a,f (W.boundaryPerm a)=f a)
    (hq : ∀ a,f (W.cutAction C hC a)=f a) :
    PortAssembly F W.Seam V W.seamArity :=
  (W.rewire C hC).assembleBoundary (fun a => f ((W.positiveRelabel C hC).symm a)) (by
    intro a
    obtain ⟨a,rfl⟩ := (W.positiveRelabel C hC).surjective a
    change f ((W.positiveRelabel C hC).symm
      (((W.rewire C hC).assemble (fun _ => ()) (fun _ => rfl)).vertexAssembly.corners.boundaryNext
        (W.positiveRelabel C hC a)))=f _
    rw [W.rewire_boundary,Equiv.symm_apply_apply,Equiv.symm_apply_apply,hq]
    exact hn a)
end PortWiring
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
open scoped Classical
variable {F G : Type} {p : F} {a b : List F} (B : RealizedBand p a b)

/-- Root of the literal doubled strip containing this side, if any. Parent
sides receive none. Selection is unique by strip disjointness. -/
noncomputable def sideStripRoot (s : Side B.doubleWiring.Seam B.doubleWiring.seamArity) :
    Option B.StripRoot :=
  if h : ∃ r : B.StripRoot,s∈B.stripCycle r.val then some h.choose else none

lemma sideStripRoot_eq_some_iff (s) (r : B.StripRoot) :
    B.sideStripRoot s=some r ↔ s∈B.stripCycle r.val := by
  unfold sideStripRoot
  split_ifs with h
  · constructor
    · intro he
      have hr : h.choose=r := Option.some.inj he
      exact hr ▸ h.choose_spec
    · intro hs
      congr 1
      apply Subtype.ext
      by_contra he
      exact Set.disjoint_left.mp (B.stripCycle_disjoint he) h.choose_spec hs
  · simp only [false_iff]
    exact fun hs => h ⟨r,hs⟩

lemma sideStripRoot_of_orig (x : B.StripNode) :
    B.sideStripRoot (B.origStripSide x)=some ⟨B.stripForest.root x,B.stripForest.root_external x⟩ :=
  (B.sideStripRoot_eq_some_iff _ _).mpr (B.stripCycle_mem_orig x)
lemma sideStripRoot_of_mirror (x : B.StripNode) :
    B.sideStripRoot (B.mirrorStripSide x)=some ⟨B.stripForest.root x,B.stripForest.root_external x⟩ :=
  (B.sideStripRoot_eq_some_iff _ _).mpr (B.stripCycle_mem_mirror x)

lemma sideStripRoot_next (s) :
    B.sideStripRoot (B.doubleAssembly.vertexAssembly.corners.boundaryNext s)=B.sideStripRoot s := by
  apply Option.ext
  intro r
  rw [B.sideStripRoot_eq_some_iff,B.sideStripRoot_eq_some_iff]
  constructor
  · intro hs
    obtain ⟨t,ht,he⟩ := B.stripCycle_surj r.val hs
    exact B.doubleAssembly.vertexAssembly.corners.boundaryNext.injective he ▸ ht
  · intro hs
    exact B.stripCycle_next r.val hs

/-- Every contacted strip inherits precisely its old ordered-child facet;
every other strip is a separate new disk, even when ranks/colors coincide. -/
noncomputable def rootFacet (h : List.Disjoint a b) (contact : B.ShortChild → G) :
    B.StripRoot → G ⊕ B.FreshStrip := fun r =>
  match (B.stripDecomposition h).symm r with
  | .inl c => .inl (contact c)
  | .inr r => .inr r

noncomputable def doubleFacet (h : List.Disjoint a b) (parent : G)
    (contact : B.ShortChild → G) (s : Side B.doubleWiring.Seam B.doubleWiring.seamArity) :
    G ⊕ B.FreshStrip :=
  match B.sideStripRoot s with
  | none => .inl parent
  | some r => B.rootFacet h contact r

lemma doubleFacet_next (h : List.Disjoint a b) (parent : G) (contact : B.ShortChild → G) (s) :
    B.doubleFacet h parent contact (B.doubleAssembly.vertexAssembly.corners.boundaryNext s)=
      B.doubleFacet h parent contact s := by
  unfold doubleFacet
  rw [B.sideStripRoot_next]

@[simp] lemma stripDecomposition_inl (h : List.Disjoint a b) (c : B.ShortChild) :
    B.stripDecomposition h (.inl c)=B.shortRoot c := rfl
@[simp] lemma stripDecomposition_inr (h : List.Disjoint a b) (r : B.FreshStrip) :
    B.stripDecomposition h (.inr r)=r.val := rfl

@[simp] lemma rootFacet_contact (h : List.Disjoint a b) (contact : B.ShortChild → G) (c) :
    B.rootFacet h contact (B.shortRoot c)=.inl (contact c) := by
  unfold rootFacet
  rw [←B.stripDecomposition_inl h c,Equiv.symm_apply_apply]
@[simp] lemma rootFacet_fresh (h : List.Disjoint a b) (contact : B.ShortChild → G) (r : B.FreshStrip) :
    B.rootFacet h contact r.val=.inr r := by
  unfold rootFacet
  rw [←B.stripDecomposition_inr h r,Equiv.symm_apply_apply]

lemma doubleFacet_input (h : List.Disjoint a b) (parent : G) (contact : B.ShortChild → G) (c) :
    B.doubleFacet h parent contact (B.mirrorStripSide (B.inputStrip c))=.inl (contact (.inl c)) := by
  unfold doubleFacet
  rw [(B.sideStripRoot_eq_some_iff _ _).mpr (B.inputContact_cycle c)]
  exact B.rootFacet_contact h contact _
lemma doubleFacet_output (h : List.Disjoint a b) (parent : G) (contact : B.ShortChild → G) (c) :
    B.doubleFacet h parent contact (B.origStripSide (B.outputStrip c))=.inl (contact (.inr c)) := by
  unfold doubleFacet
  rw [(B.sideStripRoot_eq_some_iff _ _).mpr (B.outputContact_cycle c)]
  exact B.rootFacet_contact h contact _
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
open scoped Classical
variable {F G : Type} {p : F} {a b : List F} (B : RealizedBand p a b)

lemma origPrincipal_ne_origStrip (v : Fin (B.length+1)) (x : B.StripNode) :
    B.origPrincipal v≠B.origStripSide x := by
  intro he
  have hh := B.doubleWiring.oriented_side_injective
    (B.origEnd ⟨v,(B.kind v).input,none⟩)
    (B.origEnd ⟨x.1,(B.kind x.1).table.mate x.2.val⟩)
    ((B.kind v).input_endpoint)
    ((B.kind x.1).table.orientation x.2.val |>.mpr x.2.property.1) he
  have hv : v=x.1 := Sum.inl.inj (congrArg (fun z : B.DoubleEnd => z.1) hh)
  rcases x with ⟨w,x⟩
  change v=w at hv
  subst w
  have hc := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  have hmm := congrArg (B.kind v).table.mate hc
  rw [(B.kind v).principal_corner,(B.kind v).table.involutive] at hmm
  exact x.property.2 hmm.symm
lemma origPrincipal_ne_mirrorStrip (v : Fin (B.length+1)) (x : B.StripNode) :
    B.origPrincipal v≠B.mirrorStripSide x := by
  intro he
  have hh := B.doubleWiring.oriented_side_injective
    (B.origEnd ⟨v,(B.kind v).input,none⟩) (B.mirrorEnd ⟨x.1,x.2.val⟩)
    ((B.kind v).input_endpoint) ((B.kind x.1).mirror_negative x.2.val x.2.property.1) he
  have hh' : (Sum.inl v : Fin (B.length+1) ⊕ Fin (B.length+1))=Sum.inr x.1 :=
    congrArg (fun z : B.DoubleEnd => z.1) hh
  cases hh'
lemma mirrorPrincipal_ne_origStrip (v : Fin (B.length+1)) (x : B.StripNode) :
    B.mirrorPrincipal v≠B.origStripSide x := by
  intro he
  have hv : (sumKind B.kind (mirrorKind B.kind) (.inr v)).table.endpoint
      ((B.kind v).mirrorEnd ⟨(B.kind v).output,none⟩).1=
      ((B.kind v).mirrorEnd ⟨(B.kind v).output,none⟩).2.isNone := (B.kind v).mirror_negative ⟨(B.kind v).output,none⟩ (by
    change (B.kind v).table.endpoint (B.kind v).output≠true
    rw [Kind.output_endpoint]
    exact Bool.false_ne_true)
  have hh := B.doubleWiring.oriented_side_injective
    (B.mirrorEnd ⟨v,(B.kind v).output,none⟩)
    (B.origEnd ⟨x.1,(B.kind x.1).table.mate x.2.val⟩) hv
    ((B.kind x.1).table.orientation x.2.val |>.mpr x.2.property.1) he
  have hh' : (Sum.inr v : Fin (B.length+1) ⊕ Fin (B.length+1))=Sum.inl x.1 :=
    congrArg (fun z : B.DoubleEnd => z.1) hh
  cases hh'
lemma mirrorPrincipal_ne_mirrorStrip (v : Fin (B.length+1)) (x : B.StripNode) :
    B.mirrorPrincipal v≠B.mirrorStripSide x := by
  intro he
  have hv : (sumKind B.kind (mirrorKind B.kind) (.inr v)).table.endpoint
      ((B.kind v).mirrorEnd ⟨(B.kind v).output,none⟩).1=
      ((B.kind v).mirrorEnd ⟨(B.kind v).output,none⟩).2.isNone := (B.kind v).mirror_negative ⟨(B.kind v).output,none⟩ (by
    change (B.kind v).table.endpoint (B.kind v).output≠true
    rw [Kind.output_endpoint]
    exact Bool.false_ne_true)
  have hh := B.doubleWiring.oriented_side_injective
    (B.mirrorEnd ⟨v,(B.kind v).output,none⟩) (B.mirrorEnd ⟨x.1,x.2.val⟩)
    hv ((B.kind x.1).mirror_negative x.2.val x.2.property.1) he
  have hvw : v=x.1 := Sum.inr.inj (congrArg (fun z : B.DoubleEnd => z.1) hh)
  rcases x with ⟨w,x⟩
  change v=w at hvw
  subst w
  have hc := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  exact x.property.2 ((B.kind v).mirrorEnd.injective hc).symm

lemma sideStripRoot_origPrincipal (v : Fin (B.length+1)) :
    B.sideStripRoot (B.origPrincipal v)=none := by
  apply Option.eq_none_iff_forall_not_mem.mpr
  intro r hr
  have h := (B.sideStripRoot_eq_some_iff _ r).mp hr
  obtain ⟨x,_,he|he⟩ := h
  · exact B.origPrincipal_ne_origStrip v x he
  · exact B.origPrincipal_ne_mirrorStrip v x he
lemma sideStripRoot_mirrorPrincipal (v : Fin (B.length+1)) :
    B.sideStripRoot (B.mirrorPrincipal v)=none := by
  apply Option.eq_none_iff_forall_not_mem.mpr
  intro r hr
  have h := (B.sideStripRoot_eq_some_iff _ r).mp hr
  obtain ⟨x,_,he|he⟩ := h
  · exact B.mirrorPrincipal_ne_origStrip v x he
  · exact B.mirrorPrincipal_ne_mirrorStrip v x he

lemma doubleFacet_origPrincipal (h : List.Disjoint a b) (parent : G) (contact : B.ShortChild → G) (v) :
    B.doubleFacet h parent contact (B.origPrincipal v)=.inl parent := by
  unfold doubleFacet
  rw [B.sideStripRoot_origPrincipal]
lemma doubleFacet_mirrorPrincipal (h : List.Disjoint a b) (parent : G) (contact : B.ShortChild → G) (v) :
    B.doubleFacet h parent contact (B.mirrorPrincipal v)=.inl parent := by
  unfold doubleFacet
  rw [B.sideStripRoot_mirrorPrincipal]

lemma doubleAssembly_origStrip (x : B.StripNode) :
    B.doubleAssembly.facet (B.origStripSide x)=B.stripColor x := by
  dsimp only [origStripSide]
  rw [doubleAssembly_color]
  change (B.decoration x.1).color ((B.kind x.1).table.mate x.2.val)=_
  exact (B.decoration x.1).corner x.2.val
lemma doubleAssembly_mirrorStrip (x : B.StripNode) :
    B.doubleAssembly.facet (B.mirrorStripSide x)=B.stripColor x := by
  dsimp only [mirrorStripSide]
  rw [doubleAssembly_color]
  change (B.decoration x.1).color
    ((B.kind x.1).mirrorEnd.symm ((B.kind x.1).mirrorEnd x.2.val))=_
  rw [Equiv.symm_apply_apply]
  rfl
lemma input_parent_all (v : Fin (B.length+1)) :
    (B.decoration v).color ⟨(B.kind v).input,none⟩=p := by
  induction v using Fin.induction with
  | zero => exact B.input_parent
  | succ v ih =>
    have h := B.color_match v none
    have hc := (B.decoration v.castSucc).corner ⟨(B.kind v.castSucc).input,none⟩
    rw [Kind.principal_corner] at hc
    exact h.symm.trans (hc.trans ih)
lemma output_parent_all (v : Fin (B.length+1)) :
    (B.decoration v).color ⟨(B.kind v).output,none⟩=p := by
  have hc := (B.decoration v).corner ⟨(B.kind v).input,none⟩
  rw [Kind.principal_corner] at hc
  exact hc.trans (B.input_parent_all v)

lemma doubleAssembly_origPrincipal (v : Fin (B.length+1)) :
    B.doubleAssembly.facet (B.origPrincipal v)=p := by
  dsimp only [origPrincipal]
  rw [doubleAssembly_color]
  exact B.input_parent_all v
lemma doubleAssembly_mirrorPrincipal (v : Fin (B.length+1)) :
    B.doubleAssembly.facet (B.mirrorPrincipal v)=p := by
  dsimp only [mirrorPrincipal]
  rw [doubleAssembly_color]
  change (B.decoration v).color
    ((B.kind v).mirrorEnd.symm ((B.kind v).mirrorEnd ⟨(B.kind v).output,none⟩))=p
  rw [Equiv.symm_apply_apply]
  exact B.output_parent_all v

/-- Rank of a fresh connected strip, not a rank-only grouping of disks. -/
def refinedFacetRank (old : G → ℕ) (raw : F → ℕ) : G ⊕ B.FreshStrip → ℕ
  | .inl g => old g
  | .inr r => raw (B.stripColor r.val.val)

lemma rootFacet_rank (h : List.Disjoint a b) (old : G → ℕ) (raw : F → ℕ)
    (contact : B.ShortChild → G)
    (hc : ∀ c,old (contact c)=raw (B.stripColor (B.shortRoot c).val)) (r : B.StripRoot) :
    B.refinedFacetRank old raw (B.rootFacet h contact r)=raw (B.stripColor r.val) := by
  obtain ⟨c|r,rfl⟩ := (B.stripDecomposition h).surjective r
  · rw [B.stripDecomposition_inl,B.rootFacet_contact]
    exact hc c
  · rw [B.stripDecomposition_inr,B.rootFacet_fresh]
    rfl

lemma doubleFacet_rank (h : List.Disjoint a b) (old : G → ℕ) (raw : F → ℕ)
    (parent : G) (contact : B.ShortChild → G)
    (hp : old parent=raw p)
    (hc : ∀ c,old (contact c)=raw (B.stripColor (B.shortRoot c).val)) (s) :
    B.refinedFacetRank old raw (B.doubleFacet h parent contact s)=raw (B.doubleAssembly.facet s) := by
  obtain ⟨v,rfl⟩|⟨v,rfl⟩|⟨x,rfl|rfl⟩ := B.double_side_exhaustive s
  · rw [B.doubleFacet_origPrincipal,B.doubleAssembly_origPrincipal]
    exact hp
  · rw [B.doubleFacet_mirrorPrincipal,B.doubleAssembly_mirrorPrincipal]
    exact hp
  · unfold doubleFacet
    rw [B.sideStripRoot_of_orig,B.rootFacet_rank h old raw contact hc,B.doubleAssembly_origStrip]
    exact congrArg raw (B.stripColor_root x)
  · unfold doubleFacet
    rw [B.sideStripRoot_of_mirror,B.rootFacet_rank h old raw contact hc,B.doubleAssembly_mirrorStrip]
    exact congrArg raw (B.stripColor_root x)
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
open scoped Classical
variable {F G : Type} {p : F} {a b : List F} (B : RealizedBand p a b)

/-- Replace coarse atom colors by the actual connected strip roots on the SAME
band. Contacted strips inherit old facets; untouched strips are separate disks. -/
noncomputable def refinedDecoration (h : List.Disjoint a b) (parent : G)
    (contact : B.ShortChild → G) (v : Fin (B.length+1)) :
    Decoration (B.kind v) (G ⊕ B.FreshStrip) where
  color z := B.doubleFacet h parent contact (B.doubleWiring.sideOf (B.origEnd ⟨v,z⟩))
  corner z := B.doubleWiring.cornerColor_of_boundary
    (B.doubleFacet h parent contact) (B.doubleFacet_next h parent contact) (B.origEnd ⟨v,z⟩)

lemma refinedDecoration_input_parent (h : List.Disjoint a b) (parent : G)
    (contact : B.ShortChild → G) (v : Fin (B.length+1)) :
    (B.refinedDecoration h parent contact v).portColor (B.kind v).input none=.inl parent :=
  B.doubleFacet_origPrincipal h parent contact v
lemma refinedDecoration_output_parent (h : List.Disjoint a b) (parent : G)
    (contact : B.ShortChild → G) (v : Fin (B.length+1)) :
    (B.refinedDecoration h parent contact v).portColor (B.kind v).output none=.inl parent := by
  have hc := (B.refinedDecoration h parent contact v).corner ⟨(B.kind v).input,none⟩
  rw [Kind.principal_corner] at hc
  exact hc.trans (B.refinedDecoration_input_parent h parent contact v)

lemma refinedDecoration_chain (h : List.Disjoint a b) (parent : G)
    (contact : B.ShortChild → G) :
    VariableGallery.ColorChain B.kind B.arity_match (B.refinedDecoration h parent contact) := by
  intro j c
  apply congrArg (B.doubleFacet h parent contact)
  symm
  apply B.doubleWiring.sideOf_wired
    (sumPortAt B.kind (mirrorKind B.kind) true (.inl (VariableGallery.input B.kind j.succ)))
    (sumPortAt B.kind (mirrorKind B.kind) false (.inl (VariableGallery.output B.kind j.castSucc)))
    (B.patch.double_wire_original B.shortFirst B.shortLast j)
  cases c with
  | none => rfl
  | some i =>
    change some ((((B.kind j.succ).childEnumeration (B.kind j.succ).input)
      (((B.kind j.succ).childEnumeration (B.kind j.succ).input).symm
        (finCongr (B.arity_match j) i))).val)=
      some ((((B.kind j.castSucc).childEnumeration (B.kind j.castSucc).output)
      (((B.kind j.castSucc).childEnumeration (B.kind j.castSucc).output).symm i)).val)
    simp only [Equiv.apply_symm_apply]
    rfl

lemma refinedDecoration_input_child (h : List.Disjoint a b) (parent : G)
    (contact : B.ShortChild → G) (c : (B.kind 0).table.Child (B.kind 0).input) :
    (B.refinedDecoration h parent contact 0).color ⟨(B.kind 0).input,some c⟩=
      .inl (contact (.inl c)) := by
  change B.doubleFacet h parent contact
    (B.doubleWiring.sideOf (B.origEnd ⟨0,(B.kind 0).input,some c⟩))=_
  have he := B.double_exposed_side ⟨(B.inputStrip c).1,(B.inputStrip c).2.val⟩
    (B.root_plus_port _ (B.inputStrip_external c)) (B.root_minus_port _)
  change B.doubleWiring.sideOf (B.origEnd ⟨0,(B.kind 0).input,some c⟩)=_ at he
  rw [he]
  exact B.doubleFacet_input h parent contact c
lemma refinedDecoration_output_child (h : List.Disjoint a b) (parent : G)
    (contact : B.ShortChild → G) (c : (B.kind (Fin.last B.length)).table.Child (B.kind (Fin.last B.length)).output) :
    (B.refinedDecoration h parent contact (Fin.last B.length)).color
      ⟨(B.kind (Fin.last B.length)).output,some c⟩=.inl (contact (.inr c)) := by
  have hh := B.doubleFacet_output h parent contact c
  dsimp only [origStripSide,outputStrip,Kind.outputNode] at hh
  rw [(B.kind (Fin.last B.length)).table.involutive] at hh
  exact hh

noncomputable def refinedInput (contact : B.ShortChild → G) : List (G ⊕ B.FreshStrip) :=
  List.ofFn (fun i : Fin ((B.kind 0).arity (B.kind 0).input) =>
    .inl (contact (.inl (((B.kind 0).childEnumeration (B.kind 0).input).symm i))))
noncomputable def refinedOutput (contact : B.ShortChild → G) : List (G ⊕ B.FreshStrip) :=
  List.ofFn (fun i : Fin ((B.kind (Fin.last B.length)).arity (B.kind (Fin.last B.length)).output) =>
    .inl (contact (.inr (((B.kind (Fin.last B.length)).childEnumeration
      (B.kind (Fin.last B.length)).output).symm i))))

noncomputable def refinedBand (h : List.Disjoint a b) (parent : G) (contact : B.ShortChild → G) :
    RealizedBand (.inl parent : G ⊕ B.FreshStrip) (B.refinedInput contact) (B.refinedOutput contact) where
  length := B.length
  kind := B.kind
  decoration := B.refinedDecoration h parent contact
  arity_match := B.arity_match
  color_match := B.refinedDecoration_chain h parent contact
  input_parent := B.refinedDecoration_input_parent h parent contact 0
  output_parent := B.refinedDecoration_output_parent h parent contact (Fin.last B.length)
  input_children := by
    apply congrArg List.ofFn
    funext i
    exact B.refinedDecoration_input_child h parent contact _
  output_children := by
    apply congrArg List.ofFn
    funext i
    exact B.refinedDecoration_output_child h parent contact _

/-- The construction changes ONLY facet names; no chosen topology, ports,
transverse seam, or successor is replaced by a cyclic template. -/
theorem refinedBand_same_wiring (h : List.Disjoint a b) (parent : G) (contact : B.ShortChild → G) :
    (B.refinedBand h parent contact).doubleWiring=B.doubleWiring := rfl
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
open scoped Classical
variable {F G : Type} {p : F} {a b : List F} (B : RealizedBand p a b)
lemma refinedDecoration_rank (h : List.Disjoint a b) (old : G → ℕ) (raw : F → ℕ)
    (parent : G) (contact : B.ShortChild → G)
    (hp : old parent=raw p)
    (hc : ∀ c,old (contact c)=raw (B.stripColor (B.shortRoot c).val)) (v) (z) :
    B.refinedFacetRank old raw ((B.refinedDecoration h parent contact v).color z)=
      raw ((B.decoration v).color z) := by
  change B.refinedFacetRank old raw (B.doubleFacet h parent contact
    (B.doubleWiring.sideOf (B.origEnd ⟨v,z⟩)))=_
  rw [B.doubleFacet_rank h old raw parent contact hp hc,B.doubleAssembly_color]
  rfl

lemma refinedBand_conservative (h : List.Disjoint a b) (old : G → ℕ) (raw : F → ℕ)
    (parent : G) (contact : B.ShortChild → G)
    (hp : old parent=raw p)
    (hc : ∀ c,old (contact c)=raw (B.stripColor (B.shortRoot c).val))
    (hr : ∀ v,(B.decoration v).Conservative raw) (v : Fin (B.length+1)) :
    ((B.refinedBand h parent contact).decoration v).Conservative (B.refinedFacetRank old raw) := by
  change (B.refinedDecoration h parent contact v).Conservative (B.refinedFacetRank old raw)
  rw [Decoration.conservative_iff]
  intro t
  simp_rw [B.refinedDecoration_rank h old raw parent contact hp hc]
  exact (Decoration.conservative_iff _ _).mp (hr v) t
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand

namespace IntegralCharacterVarieties.TwoFlagBand.RankShape
open scoped Classical
open OccurrenceIncidence OccurrenceIncidence.VertexTable
variable {n m r : ℕ} (d : RankShape n m r)
lemma atomic_input_arity : (d.atomicBand.kind 0).arity (d.atomicBand.kind 0).input=n := by
  have h := congrArg List.length d.atomicBand.input_children
  simpa only [Decoration.children_length,List.length_map,List.length_ofFn] using h
lemma atomic_output_arity : (d.atomicBand.kind (Fin.last d.atomicBand.length)).arity
    (d.atomicBand.kind (Fin.last d.atomicBand.length)).output=m := by
  have h := congrArg List.length d.atomicBand.output_children
  simpa only [Decoration.children_length,List.length_map,List.length_ofFn] using h

noncomputable def inputIndex (c : (d.atomicBand.kind 0).table.Child (d.atomicBand.kind 0).input) : Fin n :=
  finCongr d.atomic_input_arity ((d.atomicBand.kind 0).childEnumeration (d.atomicBand.kind 0).input c)
noncomputable def outputIndex (c : (d.atomicBand.kind (Fin.last d.atomicBand.length)).table.Child
      (d.atomicBand.kind (Fin.last d.atomicBand.length)).output) : Fin m :=
  finCongr d.atomic_output_arity ((d.atomicBand.kind (Fin.last d.atomicBand.length)).childEnumeration
    (d.atomicBand.kind (Fin.last d.atomicBand.length)).output c)

variable {G : Type} (row : Fin n → G) (col : Fin m → G)
noncomputable def stripContact : d.atomicBand.ShortChild → G
  | .inl c => row (d.inputIndex c)
  | .inr c => col (d.outputIndex c)

lemma atomic_refinedInput : d.atomicBand.refinedInput (d.stripContact row col)=(List.ofFn row).map Sum.inl := by
  unfold RealizedBand.refinedInput stripContact inputIndex
  simp only [Equiv.apply_symm_apply,List.map_ofFn]
  rw [List.ofFn_congr d.atomic_input_arity]
  rfl
lemma atomic_refinedOutput : d.atomicBand.refinedOutput (d.stripContact row col)=(List.ofFn col).map Sum.inl := by
  unfold RealizedBand.refinedOutput stripContact outputIndex
  simp only [Equiv.apply_symm_apply,List.map_ofFn]
  rw [List.ofFn_congr d.atomic_output_arity]
  rfl

/-- This named-root recoloring is obtained from the exact common-atom gallery,
not existentially chosen from its rank and endpoint signature. -/
noncomputable def refinedAtomicBand (parent : G) :
    RealizedBand (Sum.inl parent : G ⊕ d.atomicBand.FreshStrip)
      ((List.ofFn row).map Sum.inl) ((List.ofFn col).map Sum.inl) :=
  { d.atomicBand.refinedBand (atomic_short_disjoint (n:=n) (m:=m)) parent (d.stripContact row col) with
    input_children := (d.atomicBand.refinedBand (atomic_short_disjoint (n:=n) (m:=m)) parent
      (d.stripContact row col)).input_children.trans (d.atomic_refinedInput row col)
    output_children := (d.atomicBand.refinedBand (atomic_short_disjoint (n:=n) (m:=m)) parent
      (d.stripContact row col)).output_children.trans (d.atomic_refinedOutput row col) }
end IntegralCharacterVarieties.TwoFlagBand.RankShape

namespace IntegralCharacterVarieties.TwoFlagBand.RankShape
open scoped Classical
open OccurrenceIncidence OccurrenceIncidence.VertexTable
variable {n m r : ℕ} (d : RankShape n m r)

lemma inputIndex_color (c) : d.atomicBand.stripColor (d.atomicBand.inputStrip c)=some (.row (d.inputIndex c)) := by
  have h := d.atomicBand.input_children
  change List.ofFn (fun i => (d.atomicBand.decoration 0).color
    ⟨(d.atomicBand.kind 0).input,some (((d.atomicBand.kind 0).childEnumeration
      (d.atomicBand.kind 0).input).symm i)⟩)=_ at h
  have h' := ((List.ofFn_congr d.atomic_input_arity _).symm).trans (h.trans (List.map_ofFn ..))
  have he := congrFun (List.ofFn_injective h') (d.inputIndex c)
  have hc : Fin.cast d.atomic_input_arity.symm (d.inputIndex c)=
      (d.atomicBand.kind 0).childEnumeration (d.atomicBand.kind 0).input c := Fin.ext rfl
  dsimp only [Function.comp_def] at he
  rw [hc,Equiv.symm_apply_apply] at he
  exact he
lemma outputIndex_color (c) : d.atomicBand.stripColor (d.atomicBand.outputStrip c)=some (.col (d.outputIndex c)) := by
  have h := d.atomicBand.output_children
  change List.ofFn (fun i => (d.atomicBand.decoration (Fin.last d.atomicBand.length)).color
    ⟨(d.atomicBand.kind (Fin.last d.atomicBand.length)).output,
      some (((d.atomicBand.kind (Fin.last d.atomicBand.length)).childEnumeration
        (d.atomicBand.kind (Fin.last d.atomicBand.length)).output).symm i)⟩)=_ at h
  have h' := ((List.ofFn_congr d.atomic_output_arity _).symm).trans (h.trans (List.map_ofFn ..))
  have he := congrFun (List.ofFn_injective h') (d.outputIndex c)
  have hc : Fin.cast d.atomic_output_arity.symm (d.outputIndex c)=
      (d.atomicBand.kind (Fin.last d.atomicBand.length)).childEnumeration
        (d.atomicBand.kind (Fin.last d.atomicBand.length)).output c := Fin.ext rfl
  dsimp only [Function.comp_def] at he
  rw [hc,Equiv.symm_apply_apply] at he
  exact ((d.atomicBand.decoration (Fin.last d.atomicBand.length)).corner _).trans he

lemma stripColor_ne_parent (x : d.atomicBand.StripNode) : d.atomicBand.stripColor x≠none := by
  intro he
  obtain ⟨s,hs⟩ := d.atomicBand_fresh x.1
  change (d.atomicBand.decoration x.1).color x.2.val=none at he
  rw [hs,(d.atomicBand.kind x.1).fresh_color_none] at he
  rcases he with he|he
  · have hh := x.2.property.1
    rw [he,Kind.input_endpoint] at hh
    exact hh rfl
  · exact x.2.property.2 he

lemma secondaryRank_lt (hr : ∀ i,d.secondaryRank (.row i)<r)
    (hc : ∀ j,d.secondaryRank (.col j)<r) (s : Secondary n m) : d.secondaryRank s<r := by
  cases s with
  | row i => exact hr i
  | col j => exact hc j
  | cell i j =>
    apply lt_of_le_of_lt _ (hr i)
    change (d.val (i,j)).val≤∑ k,(d.val (i,k)).val
    exact Finset.single_le_sum (f := fun k => (d.val (i,k)).val)
      (fun k _ => Nat.zero_le _) (Finset.mem_univ j)

/-- The actual connected strips produced by the common-array algorithm are
proper lower-rank facets, including its branch parents. Rank conservation alone
would not prove this; it follows from the retained fresh labels. -/
lemma stripRank_lt (hr : ∀ i,d.secondaryRank (.row i)<r)
    (hc : ∀ j,d.secondaryRank (.col j)<r) (x : d.atomicBand.StripNode) :
    freshRank r d.secondaryRank (d.atomicBand.stripColor x)<r := by
  cases he : d.atomicBand.stripColor x with
  | none => exact False.elim (d.stripColor_ne_parent x he)
  | some s => exact d.secondaryRank_lt hr hc s

variable {G : Type} (rank : G → ℕ) (parent : G) (row : Fin n → G) (col : Fin m → G)
lemma stripContact_rank
    (hr : ∀ i,rank (row i)=d.secondaryRank (.row i))
    (hc : ∀ j,rank (col j)=d.secondaryRank (.col j)) (c) :
    rank (d.stripContact row col c)=
      freshRank r d.secondaryRank (d.atomicBand.stripColor (d.atomicBand.shortRoot c).val) := by
  cases c with
  | inl c =>
    change rank (row (d.inputIndex c))=freshRank r d.secondaryRank
      (d.atomicBand.stripColor (d.atomicBand.inputStrip c))
    rw [d.inputIndex_color]
    exact hr _
  | inr c =>
    change rank (col (d.outputIndex c))=freshRank r d.secondaryRank
      (d.atomicBand.stripColor (d.atomicBand.stripForest.root (d.atomicBand.outputStrip c)))
    rw [d.atomicBand.stripColor_root,d.outputIndex_color]
    exact hc _

lemma refinedAtomicBand_conservative (hp : rank parent=r)
    (hr : ∀ i,rank (row i)=d.secondaryRank (.row i))
    (hc : ∀ j,rank (col j)=d.secondaryRank (.col j)) (v : Fin (d.atomicBand.length+1)) :
    ((d.refinedAtomicBand row col parent).decoration v).Conservative
      (d.atomicBand.refinedFacetRank rank (freshRank r d.secondaryRank)) :=
  d.atomicBand.refinedBand_conservative (atomic_short_disjoint (n:=n) (m:=m)) rank
    (freshRank r d.secondaryRank) parent (d.stripContact row col) hp
    (d.stripContact_rank rank row col hr hc) d.atomicBand_conservative v
end IntegralCharacterVarieties.TwoFlagBand.RankShape

namespace IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly
open scoped Classical
open VertexTable TwoFlagBand
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    {r : ℕ} (d : RankShape (arity q) (arity q) r)

abbrev RefinedBandFacet (_A : PortAssembly F S V arity) (q : S) {r : ℕ}
    (d : RankShape (arity q) (arity q) r) := F ⊕ d.atomicBand.FreshStrip

noncomputable def refinedBandForSeam :
    RealizedBand (.inl (A.facet ⟨q,none⟩) : A.RefinedBandFacet q d)
      ((A.mapFacet (Sum.inl : F → A.RefinedBandFacet q d)).seamChildren q)
      ((A.mapFacet (Sum.inl : F → A.RefinedBandFacet q d)).seamChildren q) :=
  let B := d.refinedAtomicBand (fun i => A.facet ⟨q,some i⟩) (fun i => A.facet ⟨q,some i⟩)
    (A.facet ⟨q,none⟩)
  { B with
    input_children := B.input_children.trans (List.map_ofFn ..)
    output_children := B.output_children.trans (List.map_ofFn ..) }

/-- Complete occurrence assembly, with every untouched component of the literal
band double a DISTINCT fresh strip disk. No new incidence is guessed. -/
noncomputable def refinedAtomicGraft :=
  (A.mapFacet (Sum.inl : F → A.RefinedBandFacet q d)).graftBand q (A.refinedBandForSeam q d)
end IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly

namespace IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly
open scoped Classical
open VertexTable TwoFlagBand
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
variable {r : ℕ} (d : RankShape (arity q) (arity q) r) (rank : F → ℕ)

noncomputable def refinedRank : A.RefinedBandFacet q d → ℕ :=
  d.atomicBand.refinedFacetRank rank (freshRank r d.secondaryRank)

lemma refinedBandForSeam_rank
    (hp : rank (A.facet ⟨q,none⟩)=r)
    (hc : ∀ i,rank (A.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,rank (A.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
    (v : Fin (d.atomicBand.length+1)) (z : (p : (d.atomicBand.kind v).table.Port) ×
      Option ((d.atomicBand.kind v).table.Child p)) :
    A.refinedRank q d rank (((A.refinedBandForSeam q d).decoration v).color z)=
      freshRank r d.secondaryRank ((d.atomicBand.decoration v).color z) :=
  d.atomicBand.refinedDecoration_rank (RankShape.atomic_short_disjoint (n:=arity q) (m:=arity q)) rank
    (freshRank r d.secondaryRank) (A.facet ⟨q,none⟩)
    (d.stripContact (fun i => A.facet ⟨q,some i⟩) (fun i => A.facet ⟨q,some i⟩)) hp
    (d.stripContact_rank rank _ _ hc hc') v z

lemma refinedBandForSeam_parent_germs
    (hp : rank (A.facet ⟨q,none⟩)=r)
    (hc : ∀ i,rank (A.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,rank (A.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
    (hlt : ∀ i,rank (A.facet ⟨q,some i⟩)<r)
    (v : Fin (d.atomicBand.length+1)) (z : (p : (d.atomicBand.kind v).table.Port) ×
      Option ((d.atomicBand.kind v).table.Child p)) :
    ((A.refinedBandForSeam q d).decoration v).color z=.inl (A.facet ⟨q,none⟩) ↔
      z=⟨(d.atomicBand.kind v).input,none⟩ ∨ z=⟨(d.atomicBand.kind v).output,none⟩ := by
  constructor
  · intro he
    have hh := A.refinedBandForSeam_rank q d rank hp hc hc' v z
    rw [he] at hh
    change rank (A.facet ⟨q,none⟩)=_ at hh
    rw [hp] at hh
    have hn : (d.atomicBand.decoration v).color z=none := by
      cases hz : (d.atomicBand.decoration v).color z with
      | none => rfl
      | some s =>
        rw [hz] at hh
        have hl := d.secondaryRank_lt (fun i => (hc i) ▸ hlt i)
          (fun i => (hc' i) ▸ hlt i) s
        change r=d.secondaryRank s at hh
        omega
    obtain ⟨s,hs⟩ := d.atomicBand_fresh v
    rw [hs,(d.atomicBand.kind v).fresh_color_none] at hn
    exact hn
  · rintro (rfl|rfl)
    · exact (A.refinedBandForSeam q d).input_parent_all v
    · exact (A.refinedBandForSeam q d).output_parent_all v

/-- This exhausts parent germs of the connected-strip refinement, not merely
of a coarsely labeled band with possibly merged disconnected child components. -/
theorem refinedAtomicGraft_parent_exhaustive
    (hp : rank (A.facet ⟨q,none⟩)=r)
    (hc : ∀ i,rank (A.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,rank (A.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
    (hlt : ∀ i,rank (A.facet ⟨q,some i⟩)<r)
    (hold : ∀ s i,A.facet ⟨s,some i⟩≠A.facet ⟨q,none⟩)
    (a : Side (BandGraft.wiring (A.mapFacet (Sum.inl : F → A.RefinedBandFacet q d)) q
      (A.refinedBandForSeam q d)).Seam
      (BandGraft.wiring (A.mapFacet (Sum.inl : F → A.RefinedBandFacet q d)) q
      (A.refinedBandForSeam q d)).seamArity)
    (ha : (A.refinedAtomicGraft q d).facet a=.inl (A.facet ⟨q,none⟩)) :
    (∃ s,A.facet ⟨s,none⟩=A.facet ⟨q,none⟩ ∧
      a=BandGraft.oldSide (A.mapFacet (Sum.inl : F → A.RefinedBandFacet q d)) q (A.refinedBandForSeam q d) s) ∨
    (∃ v,a=BandGraft.originalSide (A.mapFacet (Sum.inl : F → A.RefinedBandFacet q d)) q (A.refinedBandForSeam q d) v) ∨
    (∃ v,a=BandGraft.mirrorSide (A.mapFacet (Sum.inl : F → A.RefinedBandFacet q d)) q (A.refinedBandForSeam q d) v) := by
  let A' := A.mapFacet (Sum.inl : F → A.RefinedBandFacet q d)
  have hh : ∀ s i,A'.facet ⟨s,some i⟩≠A'.facet ⟨q,none⟩ := by
    intro s i h
    exact hold s i (Sum.inl.inj h)
  have hg := BandGraft.parent_exhaustive A' q (A.refinedBandForSeam q d) hh
    (A.refinedBandForSeam_parent_germs q d rank hp hc hc' hlt) a ha
  rcases hg with ⟨s,hs,ha⟩|h|h
  · exact Or.inl ⟨s,Sum.inl.inj hs,ha⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

lemma refinedRank_fresh_lt
    (hr : ∀ i,d.secondaryRank (.row i)<r) (hc : ∀ i,d.secondaryRank (.col i)<r)
    (x : d.atomicBand.FreshStrip) : A.refinedRank q d rank (.inr x)<r :=
  d.stripRank_lt hr hc x.val.val
end IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace PortAssembly
variable {F G S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (rank : F → ℕ)
lemma decoration_conservative
    (h : ∀ s,rank (A.facet ⟨s,none⟩)=∑ i,rank (A.facet ⟨s,some i⟩)) (v) :
    (A.decoration v).Conservative rank := by
  intro p
  have hh := A.decoration_signature ⟨v,p⟩
  have hp := congrArg Prod.fst hh
  have hc := congrArg Prod.snd hh
  change (A.decoration v).portColor p none=A.facet ⟨(A.attach ⟨v,p⟩).1,none⟩ at hp
  change (A.decoration v).children p=List.ofFn (fun i => A.facet ⟨(A.attach ⟨v,p⟩).1,some i⟩) at hc
  rw [hp,hc,listRank_ofFn]
  exact h _
end PortAssembly
namespace VertexTable
variable {F : Type} (rank : F → ℕ) {k : Kind} (d : Decoration k F)
lemma Decoration.mirror_conservative (hd : d.Conservative rank) : d.mirror.Conservative rank := by
  intro p
  obtain ⟨p,rfl⟩ := k.mirrorPort.surjective p
  have h := d.mirror_signature p
  have hp := congrArg Prod.fst h
  have hc := congrArg Prod.snd h
  change d.mirror.portColor (k.mirrorPort p) none=d.portColor p none at hp
  change d.mirror.children (k.mirrorPort p)=d.children p at hc
  rw [hp,hc]
  exact hd p
end VertexTable
namespace PortWiring
variable {F V : Type} {kind : V → Kind} (W : PortWiring kind)
    (d : (v : V) → Decoration (kind v) F) (h : W.ColorMatch d) (rank : F → ℕ)
lemma colored_seamRank (hd : ∀ v,(d v).Conservative rank) (s) :
    rank ((W.colored d h).facet ⟨s,none⟩)=∑ i,rank ((W.colored d h).facet ⟨s,some i⟩) := by
  change rank ((d s.val.1).portColor s.val.2 none)=
    ∑ i,rank ((d s.val.1).portColor s.val.2 (some i))
  simpa only [Decoration.children,listRank_ofFn] using hd s.val.1 s.val.2
end PortWiring
namespace PortAssembly
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q)) (rank : F → ℕ)
lemma graftBand_seamRank
    (hold : ∀ s,rank (A.facet ⟨s,none⟩)=∑ i,rank (A.facet ⟨s,some i⟩))
    (hband : ∀ v,(B.decoration v).Conservative rank) (s) :
    rank ((A.graftBand q B).facet ⟨s,none⟩)=∑ i,rank ((A.graftBand q B).facet ⟨s,some i⟩) := by
  apply (BandGraft.wiring A q B).colored_seamRank (BandGraft.decoration A q B)
    (BandGraft.colorMatch A q B) rank
  rintro (v|v|v)
  · exact A.decoration_conservative rank hold v
  · exact hband v
  · exact (B.decoration v).mirror_conservative rank (hband v)
end PortAssembly
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly
open scoped Classical
open VertexTable TwoFlagBand
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
variable {r : ℕ} (d : RankShape (arity q) (arity q) r)
/-- Injection is proved from the uncoloured atomic row/column topology. The
actual two endpoint lists can be identical; no false disjointness assumption
on their old facet colours is used. -/
lemma refinedBandForSeam_shortRoot_injective :
    Function.Injective (A.refinedBandForSeam q d).shortRoot := by
  have hforest : (A.refinedBandForSeam q d).stripForest=d.atomicBand.stripForest := rfl
  have he (c : (A.refinedBandForSeam q d).ShortChild) :
      ((A.refinedBandForSeam q d).shortRoot c).val=(d.atomicBand.shortRoot c).val := by
    cases c with
    | inl c => rfl
    | inr c =>
      change (A.refinedBandForSeam q d).stripForest.root _=d.atomicBand.stripForest.root _
      rw [hforest]
      rfl
  intro c e hce
  apply d.atomicBand.shortRoot_injective (RankShape.atomic_short_disjoint (n:=arity q) (m:=arity q))
  apply Subtype.ext
  exact (he c).symm.trans ((congrArg Subtype.val hce).trans (he e))
end IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly

namespace IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly
open scoped Classical
open VertexTable TwoFlagBand
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
variable {r : ℕ} (d : RankShape (arity q) (arity q) r)
lemma refinedBandForSeam_shortRoot_eq :
    (A.refinedBandForSeam q d).shortRoot=d.atomicBand.shortRoot := by
  funext c
  apply Subtype.ext
  cases c with
  | inl c => rfl
  | inr c => rfl
lemma refinedBandForSeam_fresh_eq :
    (A.refinedBandForSeam q d).FreshStrip=d.atomicBand.FreshStrip := by
  change {z : d.atomicBand.StripRoot // z∉Set.range (A.refinedBandForSeam q d).shortRoot} = _
  rw [A.refinedBandForSeam_shortRoot_eq q d]
  rfl
end IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly

end OAI
