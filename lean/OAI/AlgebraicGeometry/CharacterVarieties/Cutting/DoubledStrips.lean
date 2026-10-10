import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.StripForest

namespace OAI

/-!
# Boundary circuits and germ exhaustion of doubled secondary strips.

This formalizes the band reconstruction for filtered surface local systems in
*Integral points on character varieties of curves*.
-/

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace PortWiring
variable {V : Type} {k : V → Kind} (W : PortWiring k)
lemma endOf_positive (p : PortAt k true) : W.endOf p.val=(p,true) :=
  W.endOf_portAt (p,true)
lemma endOf_negative (p : PortAt k false) : W.endOf p.val=(W.wire.symm p,false) := by
  have h := W.endOf_portAt (W.wire.symm p,false)
  change W.endOf (W.wire (W.wire.symm p)).val=_ at h
  rw [Equiv.apply_symm_apply] at h
  exact h
lemma sideOf_wired (p : PortAt k true) (q : PortAt k false) (hw : W.wire p=q)
    (c : Option ((k p.val.1).table.Child p.val.2))
    (d : Option ((k q.val.1).table.Child q.val.2))
    (hc : c.map (fun i => ((k p.val.1).childEnumeration p.val.2 i).val)=
      d.map (fun i => ((k q.val.1).childEnumeration q.val.2 i).val)) :
    W.sideOf ⟨p.val.1,p.val.2,c⟩=W.sideOf ⟨q.val.1,q.val.2,d⟩ := by
  apply W.sideOf_eq _ _ _ hc
  change (W.endOf p.val).1=(W.endOf q.val).1
  rw [W.endOf_positive,W.endOf_negative,←hw,Equiv.symm_apply_apply]

end PortWiring
namespace PortPatch
variable {V I A B : Type} {k : V → Kind} (P : PortPatch k I A B) (a₀ : A) (b₀ : B)
lemma double_wire_original (i : I) :
    (P.doubledWiring a₀ b₀).wire
      (sumPortAt k (mirrorKind k) true (.inl (P.plus (.inl i))))=
      sumPortAt k (mirrorKind k) false (.inl (P.minus (.inl i))) :=
  (P.double a₀ b₀).complete_internal (Equiv.refl Bool) _ (.inl (.inl i))
lemma double_wire_mirror (i : I) :
    (P.doubledWiring a₀ b₀).wire
      (sumPortAt k (mirrorKind k) true (.inr (mirrorPortAt k false (P.minus (.inl i)))))=
      sumPortAt k (mirrorKind k) false (.inr (mirrorPortAt k true (P.plus (.inl i)))) :=
  (P.double a₀ b₀).complete_internal (Equiv.refl Bool) _ (.inl (.inr i))
lemma double_wire_exposed_plus (a : A) :
    (P.doubledWiring a₀ b₀).wire
      (sumPortAt k (mirrorKind k) true (.inl (P.plus (.inr a))))=
      sumPortAt k (mirrorKind k) false (.inr (mirrorPortAt k true (P.plus (.inr a)))) := by
  by_cases h : a=a₀
  · subst a
    exact (P.double a₀ b₀).complete_external (Equiv.refl Bool) _ false
  · exact (P.double a₀ b₀).complete_internal (Equiv.refl Bool) _ (.inr (.inl ⟨a,h⟩))
lemma double_wire_exposed_minus (b : B) :
    (P.doubledWiring a₀ b₀).wire
      (sumPortAt k (mirrorKind k) true (.inr (mirrorPortAt k false (P.minus (.inr b)))))=
      sumPortAt k (mirrorKind k) false (.inl (P.minus (.inr b))) := by
  by_cases h : b=b₀
  · subst b
    exact (P.double a₀ b₀).complete_external (Equiv.refl Bool) _ true
  · exact (P.double a₀ b₀).complete_internal (Equiv.refl Bool) _ (.inr (.inr ⟨b,h⟩))
end PortPatch
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
lemma Kind.mirror_isNone (k : Kind) (z : (p : k.table.Port) × Option (k.table.Child p)) :
    (k.mirrorEnd z).2.isNone=z.2.isNone := by
  rcases z with ⟨p,c⟩
  cases c <;> rfl
lemma Kind.mirror_negative (k : Kind) (z : (p : k.table.Port) × Option (k.table.Child p))
    (h : k.table.endpoint z.1≠z.2.isNone) :
    k.mirror.table.endpoint (k.mirrorEnd z).1=(k.mirrorEnd z).2.isNone := by
  change k.mirror.table.endpoint (k.mirrorPort z.1)=_
  rw [Kind.mirror_endpoint,Kind.mirror_isNone]
  cases he : k.table.endpoint z.1 <;> cases hn : z.2.isNone <;> simp_all
namespace RealizedBand
variable {F : Type} {p : F} {a b : List F} (B : RealizedBand p a b)
abbrev DoubleEnd := LocalEnd (Fin (B.length+1) ⊕ Fin (B.length+1)) (sumKind B.kind (mirrorKind B.kind))
def origEnd (x : LocalEnd (Fin (B.length+1)) B.kind) : B.DoubleEnd := ⟨.inl x.1,x.2⟩
def mirrorEnd (x : LocalEnd (Fin (B.length+1)) B.kind) : B.DoubleEnd :=
  ⟨.inr x.1,(B.kind x.1).mirrorEnd x.2⟩
noncomputable def origStripSide (x : B.StripNode) :=
  B.doubleWiring.sideOf (B.origEnd ⟨x.1,(B.kind x.1).table.mate x.2.val⟩)
noncomputable def mirrorStripSide (x : B.StripNode) :=
  B.doubleWiring.sideOf (B.mirrorEnd ⟨x.1,x.2.val⟩)
lemma origStrip_next (x : B.StripNode) :
    B.doubleAssembly.vertexAssembly.corners.boundaryNext (B.origStripSide x)=
      B.doubleWiring.sideOf (B.origEnd ⟨x.1,x.2.val⟩) := by
  change (B.doubleWiring.assemble _ _).vertexAssembly.corners.boundaryNext _=_
  rw [origStripSide,B.doubleWiring.boundaryNext_local _ _
    (B.origEnd ⟨x.1,(B.kind x.1).table.mate x.2.val⟩)
    (by exact (B.kind x.1).table.orientation x.2.val |>.mpr x.2.property.1)]
  change B.doubleWiring.sideOf ⟨.inl x.1,(B.kind x.1).table.mate ((B.kind x.1).table.mate x.2.val)⟩=_
  rw [(B.kind x.1).table.involutive]
  rfl
lemma mirrorStrip_next (x : B.StripNode) :
    B.doubleAssembly.vertexAssembly.corners.boundaryNext (B.mirrorStripSide x)=
      B.doubleWiring.sideOf (B.mirrorEnd ⟨x.1,(B.kind x.1).table.mate x.2.val⟩) := by
  change (B.doubleWiring.assemble _ _).vertexAssembly.corners.boundaryNext _=_
  rw [mirrorStripSide,B.doubleWiring.boundaryNext_local _ _ (B.mirrorEnd ⟨x.1,x.2.val⟩)
    (by exact (B.kind x.1).mirror_negative x.2.val x.2.property.1)]
  change B.doubleWiring.sideOf ⟨.inr x.1,(B.kind x.1).mirror.table.mate ((B.kind x.1).mirrorEnd x.2.val)⟩=_
  rw [←(B.kind x.1).mirror_mate]
  rfl

lemma origStrip_edge (e : B.StripEdge) :
    B.doubleAssembly.vertexAssembly.corners.boundaryNext (B.origStripSide (B.stripTarget e))=
      B.origStripSide (B.stripSource e) := by
  rw [B.origStrip_next]
  change B.doubleWiring.sideOf ⟨.inl e.1.succ,_,some _⟩=
    B.doubleWiring.sideOf ⟨.inl e.1.castSucc,(B.kind e.1.castSucc).table.mate ((B.kind e.1.castSucc).table.mate ⟨_,some _⟩)⟩
  rw [(B.kind e.1.castSucc).table.involutive]
  apply B.doubleWiring.sideOf_wired
    (sumPortAt B.kind (mirrorKind B.kind) true (.inl (VariableGallery.input B.kind e.1.succ)))
    (sumPortAt B.kind (mirrorKind B.kind) false (.inl (VariableGallery.output B.kind e.1.castSucc)))
    (B.patch.double_wire_original B.shortFirst B.shortLast e.1)
  change some ((((B.kind e.1.succ).childEnumeration (B.kind e.1.succ).input)
      (((B.kind e.1.succ).childEnumeration (B.kind e.1.succ).input).symm
        (finCongr (B.arity_match e.1) e.2))).val)=
    some ((((B.kind e.1.castSucc).childEnumeration (B.kind e.1.castSucc).output)
      (((B.kind e.1.castSucc).childEnumeration (B.kind e.1.castSucc).output).symm e.2)).val)
  simp only [Equiv.apply_symm_apply]
  rfl

lemma mirrorStrip_edge (e : B.StripEdge) :
    B.doubleAssembly.vertexAssembly.corners.boundaryNext (B.mirrorStripSide (B.stripSource e))=
      B.mirrorStripSide (B.stripTarget e) := by
  rw [B.mirrorStrip_next]
  change B.doubleWiring.sideOf (B.mirrorEnd ⟨e.1.castSucc,(B.kind e.1.castSucc).table.mate
    ((B.kind e.1.castSucc).table.mate ⟨_,some _⟩)⟩)=_
  rw [(B.kind e.1.castSucc).table.involutive]
  apply B.doubleWiring.sideOf_wired
    (sumPortAt B.kind (mirrorKind B.kind) true (.inr (mirrorPortAt B.kind false (VariableGallery.output B.kind e.1.castSucc))))
    (sumPortAt B.kind (mirrorKind B.kind) false (.inr (mirrorPortAt B.kind true (VariableGallery.input B.kind e.1.succ))))
    (B.patch.double_wire_mirror B.shortFirst B.shortLast e.1)
  dsimp only [sumPortAt,mirrorPortAt,VariableGallery.input,VariableGallery.output,sumKind,mirrorKind]
  change some (((B.kind e.1.castSucc).mirror.childEnumeration _ ((B.kind e.1.castSucc).mirrorChild _ _)).val)=
    some (((B.kind e.1.succ).mirror.childEnumeration _ ((B.kind e.1.succ).mirrorChild _ _)).val)
  rw [Kind.mirror_childEnumeration,Kind.mirror_childEnumeration]
  simp only [Equiv.apply_symm_apply]
  rfl
end RealizedBand
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
open scoped Classical
variable {F : Type} {p : F} {a b : List F} (B : RealizedBand p a b)
lemma root_plus_port (x : B.StripNode) (he : ¬∃ e,B.stripTarget e=x) :
    ¬ ∃ j : Fin B.length,(⟨x.1,x.2.val.1⟩ : LocalPort _ B.kind)=(VariableGallery.internalPlus B.kind j).val := by
  rcases x with ⟨v,z⟩
  rintro ⟨j,h⟩
  have hv : v=j.succ := congrArg Sigma.fst h
  subst v
  have hp : z.val.1=(B.kind j.succ).input := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  obtain ⟨c,rfl⟩ := (B.kind j.succ).node_at_input z hp
  exact he (B.input_predecessor j c)
lemma root_minus_port (x : B.StripNode) :
    ¬ ∃ j : Fin B.length,(⟨x.1,x.2.val.1⟩ : LocalPort _ B.kind)=(VariableGallery.internalMinus B.kind j).val := by
  rcases x with ⟨v,z⟩
  rintro ⟨j,h⟩
  have hv : v=j.castSucc := congrArg Sigma.fst h
  subst v
  have hp : z.val.1=(B.kind j.castSucc).output := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact (B.kind j.castSucc).node_not_output z hp
lemma tip_plus_port (x : B.StripNode) :
    ¬ ∃ j : Fin B.length,(⟨x.1,((B.kind x.1).table.mate x.2.val).1⟩ : LocalPort _ B.kind)=
      (VariableGallery.internalPlus B.kind j).val := by
  rcases x with ⟨v,z⟩
  rintro ⟨j,h⟩
  have hv : v=j.succ := congrArg Sigma.fst h
  subst v
  have hp : ((B.kind j.succ).table.mate z.val).1=(B.kind j.succ).input := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact (B.kind j.succ).node_mate_not_input z hp
lemma tip_minus_port (x : B.StripNode) (he : ¬∃ e,B.stripSource e=x) :
    ¬ ∃ j : Fin B.length,(⟨x.1,((B.kind x.1).table.mate x.2.val).1⟩ : LocalPort _ B.kind)=
      (VariableGallery.internalMinus B.kind j).val := by
  rcases x with ⟨v,z⟩
  rintro ⟨j,h⟩
  have hv : v=j.castSucc := congrArg Sigma.fst h
  subst v
  have hp : ((B.kind j.castSucc).table.mate z.val).1=(B.kind j.castSucc).output := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  obtain ⟨c,rfl⟩ := (B.kind j.castSucc).node_at_output z hp
  exact he (B.output_successor j c)
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
open scoped Classical
variable {F : Type} {p : F} {a b : List F} (B : RealizedBand p a b)
lemma double_exposed_side (x : LocalEnd (Fin (B.length+1)) B.kind)
    (hp : ¬∃ j : Fin B.length,(⟨x.1,x.2.1⟩ : LocalPort _ B.kind)=(VariableGallery.internalPlus B.kind j).val)
    (hm : ¬∃ j : Fin B.length,(⟨x.1,x.2.1⟩ : LocalPort _ B.kind)=(VariableGallery.internalMinus B.kind j).val) :
    B.doubleWiring.sideOf (B.origEnd x)=B.doubleWiring.sideOf (B.mirrorEnd x) := by
  cases hh : (B.kind x.1).table.endpoint x.2.1 with
  | true =>
    let q : PortAt B.kind true := ⟨⟨x.1,x.2.1⟩,hh⟩
    have hq : q∉Set.range (VariableGallery.internalPlus B.kind) := by
      rintro ⟨j,hj⟩
      exact hp ⟨j,(congrArg Subtype.val hj).symm⟩
    have hw := B.patch.double_wire_exposed_plus B.shortFirst B.shortLast ⟨q,hq⟩
    apply B.doubleWiring.sideOf_wired
      (sumPortAt B.kind (mirrorKind B.kind) true (.inl q))
      (sumPortAt B.kind (mirrorKind B.kind) false (.inr (mirrorPortAt B.kind true q))) hw
    change x.2.2.map (fun i => ((B.kind x.1).childEnumeration x.2.1 i).val)=
      (x.2.2.map ((B.kind x.1).mirrorChild x.2.1)).map
        (fun i => ((B.kind x.1).mirror.childEnumeration ((B.kind x.1).mirrorPort x.2.1) i).val)
    cases x.2.2 with
    | none => rfl
    | some c => simp only [Option.map_some,Kind.mirror_childEnumeration]; rfl
  | false =>
    let q : PortAt B.kind false := ⟨⟨x.1,x.2.1⟩,hh⟩
    have hq : q∉Set.range (VariableGallery.internalMinus B.kind) := by
      rintro ⟨j,hj⟩
      exact hm ⟨j,(congrArg Subtype.val hj).symm⟩
    have hw := B.patch.double_wire_exposed_minus B.shortFirst B.shortLast ⟨q,hq⟩
    symm
    apply B.doubleWiring.sideOf_wired
      (sumPortAt B.kind (mirrorKind B.kind) true (.inr (mirrorPortAt B.kind false q)))
      (sumPortAt B.kind (mirrorKind B.kind) false (.inl q)) hw
    change (x.2.2.map ((B.kind x.1).mirrorChild x.2.1)).map
        (fun i => ((B.kind x.1).mirror.childEnumeration ((B.kind x.1).mirrorPort x.2.1) i).val)=
      x.2.2.map (fun i => ((B.kind x.1).childEnumeration x.2.1 i).val)
    cases x.2.2 with
    | none => rfl
    | some c => simp only [Option.map_some,Kind.mirror_childEnumeration]; rfl
lemma origStrip_root (x : B.StripNode) (he : ¬∃ e,B.stripTarget e=x) :
    B.doubleAssembly.vertexAssembly.corners.boundaryNext (B.origStripSide x)=B.mirrorStripSide x := by
  rw [B.origStrip_next]
  exact B.double_exposed_side ⟨x.1,x.2.val⟩ (B.root_plus_port x he) (B.root_minus_port x)
lemma mirrorStrip_tip (x : B.StripNode) (he : ¬∃ e,B.stripSource e=x) :
    B.doubleAssembly.vertexAssembly.corners.boundaryNext (B.mirrorStripSide x)=B.origStripSide x := by
  rw [B.mirrorStrip_next]
  exact (B.double_exposed_side ⟨x.1,(B.kind x.1).table.mate x.2.val⟩
    (B.tip_plus_port x) (B.tip_minus_port x he)).symm
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
open scoped Classical
variable {F : Type} {p : F} {a b : List F} (B : RealizedBand p a b)
lemma origStrip_sameRoot (x : B.StripNode) :
    B.doubleAssembly.vertexAssembly.corners.boundaryNext.SameCycle
      (B.origStripSide x) (B.origStripSide (B.stripForest.root x)) := by
  induction h : x.1.val using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases he : ∃ e,B.stripTarget e=x
    · obtain ⟨e,rfl⟩ := he
      change B.doubleAssembly.vertexAssembly.corners.boundaryNext.SameCycle (B.origStripSide (B.stripForest.target e)) (B.origStripSide (B.stripForest.root (B.stripForest.target e)))
      rw [B.stripForest.root_of_edge]
      have hh := ih e.1.val (by change e.1.val+1=n at h; omega) (B.stripSource e) rfl
      exact ((B.origStrip_edge e).sameCycle _).of_apply_left.trans hh
    · rw [B.stripForest.root_of_source x he]
lemma mirrorStrip_sameRoot (x : B.StripNode) :
    B.doubleAssembly.vertexAssembly.corners.boundaryNext.SameCycle
      (B.mirrorStripSide x) (B.mirrorStripSide (B.stripForest.root x)) := by
  induction h : x.1.val using Nat.strong_induction_on generalizing x with
  | h n ih =>
    by_cases he : ∃ e,B.stripTarget e=x
    · obtain ⟨e,rfl⟩ := he
      change B.doubleAssembly.vertexAssembly.corners.boundaryNext.SameCycle (B.mirrorStripSide (B.stripForest.target e)) (B.mirrorStripSide (B.stripForest.root (B.stripForest.target e)))
      rw [B.stripForest.root_of_edge]
      have hh := ih e.1.val (by change e.1.val+1=n at h; omega) (B.stripSource e) rfl
      exact ((B.mirrorStrip_edge e).sameCycle _).of_apply_left.symm.trans hh
    · rw [B.stripForest.root_of_source x he]

def stripCycle (r : B.StripNode) : Set (Side B.doubleWiring.Seam B.doubleWiring.seamArity) :=
  {s | ∃ x,B.stripForest.root x=r ∧ (s=B.origStripSide x ∨ s=B.mirrorStripSide x)}

lemma stripCycle_next (r : B.StripNode) : Set.MapsTo
    B.doubleAssembly.vertexAssembly.corners.boundaryNext (B.stripCycle r) (B.stripCycle r) := by
  rintro s ⟨x,hx,rfl|rfl⟩
  · by_cases he : ∃ e,B.stripTarget e=x
    · obtain ⟨e,rfl⟩ := he
      have hr : B.stripForest.root (B.stripSource e)=r := (B.stripForest.root_of_edge e).symm.trans hx
      exact ⟨B.stripSource e,hr,Or.inl (B.origStrip_edge e)⟩
    · exact ⟨x,hx,Or.inr (B.origStrip_root x he)⟩
  · by_cases he : ∃ e,B.stripSource e=x
    · obtain ⟨e,rfl⟩ := he
      have hr : B.stripForest.root (B.stripTarget e)=r := (B.stripForest.root_of_edge e).trans hx
      exact ⟨B.stripTarget e,hr,Or.inr (B.mirrorStrip_edge e)⟩
    · exact ⟨x,hx,Or.inl (B.mirrorStrip_tip x he)⟩

lemma stripCycle_surj (r : B.StripNode) : Set.SurjOn
    B.doubleAssembly.vertexAssembly.corners.boundaryNext (B.stripCycle r) (B.stripCycle r) := by
  rintro s ⟨x,hx,rfl|rfl⟩
  · by_cases he : ∃ e,B.stripSource e=x
    · obtain ⟨e,rfl⟩ := he
      have hr : B.stripForest.root (B.stripTarget e)=r := (B.stripForest.root_of_edge e).trans hx
      exact ⟨B.origStripSide (B.stripTarget e),⟨B.stripTarget e,hr,Or.inl rfl⟩,B.origStrip_edge e⟩
    · exact ⟨B.mirrorStripSide x,⟨x,hx,Or.inr rfl⟩,B.mirrorStrip_tip x he⟩
  · by_cases he : ∃ e,B.stripTarget e=x
    · obtain ⟨e,rfl⟩ := he
      have hr : B.stripForest.root (B.stripSource e)=r := (B.stripForest.root_of_edge e).symm.trans hx
      exact ⟨B.mirrorStripSide (B.stripSource e),⟨B.stripSource e,hr,Or.inr rfl⟩,B.mirrorStrip_edge e⟩
    · exact ⟨B.origStripSide x,⟨x,hx,Or.inl rfl⟩,B.origStrip_root x he⟩

lemma stripCycle_sameRoot {r : B.StripNode} {s : Side B.doubleWiring.Seam B.doubleWiring.seamArity}
    (hs : s∈B.stripCycle r) : B.doubleAssembly.vertexAssembly.corners.boundaryNext.SameCycle s (B.origStripSide r) := by
  obtain ⟨x,hx,rfl|rfl⟩ := hs
  · simpa only [hx] using B.origStrip_sameRoot x
  · have h1 := B.mirrorStrip_sameRoot x
    have he : ¬∃ e,B.stripTarget e=r := hx ▸ B.stripForest.root_external x
    rw [hx] at h1
    exact h1.trans (((B.origStrip_root r he).sameCycle _).of_apply_left.symm)

/-- Each actual secondary run doubles to EXACTLY one boundary circuit. The
successors are those of the literal whole-port double, including every
transverse split/merge seam; there is no postulated replacement permutation. -/
theorem stripCycle_isCycle (r : B.StripNode) :
    B.doubleAssembly.vertexAssembly.corners.boundaryNext.IsCycleOn (B.stripCycle r) := by
  refine ⟨⟨B.stripCycle_next r,?_,B.stripCycle_surj r⟩,?_⟩
  · exact B.doubleAssembly.vertexAssembly.corners.boundaryNext.injective.injOn
  · intro x hx y hy
    exact (B.stripCycle_sameRoot hx).trans (B.stripCycle_sameRoot hy).symm
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace PortWiring
variable {V : Type} {kind : V → Kind} (W : PortWiring kind)
lemma sideOf_isNone (x : LocalEnd V kind) : (W.sideOf x).2.isNone=x.2.2.isNone := by
  rcases x with ⟨v,p,c⟩
  cases c <;> rfl

/-- Every actual side has one and only one positively oriented local germ,
not merely one endpoint at a positive port. -/
lemma oriented_side_injective (x y : LocalEnd V kind)
    (hx : (kind x.1).table.endpoint x.2.1=x.2.2.isNone)
    (hy : (kind y.1).table.endpoint y.2.1=y.2.2.isNone)
    (h : W.sideOf x=W.sideOf y) : x=y := by
  apply (W.assemble (fun _ => ()) (fun _ => rfl)).realize.injective
  rw [W.realize_assemble,W.realize_assemble]
  apply Prod.ext h
  rw [hx,hy,←W.sideOf_isNone x,←W.sideOf_isNone y,h]

lemma oriented_side_exists (a : Side W.Seam W.seamArity) :
    ∃ x : LocalEnd V kind,(kind x.1).table.endpoint x.2.1=x.2.2.isNone ∧ W.sideOf x=a := by
  let A := W.assemble (fun _ => ()) (fun _ => rfl)
  let x : LocalEnd V kind := A.realize.symm (finish a)
  have h := W.realize_assemble (fun _ => ()) (fun _ => rfl) x
  have hx : A.realize x=finish a := A.realize.apply_symm_apply _
  change A.realize x=_ at h
  have he := hx.symm.trans h
  have hs : W.sideOf x=a := (congrArg Prod.fst he).symm
  refine ⟨x,?_,hs⟩
  have hb : (kind x.1).table.endpoint x.2.1=a.2.isNone := (congrArg Prod.snd he).symm
  rw [hb,←hs,W.sideOf_isNone]
end PortWiring
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
open scoped Classical
variable {F : Type} {p : F} {a b : List F} (B : RealizedBand p a b)
lemma origStripSide_injective : Function.Injective B.origStripSide := by
  rintro ⟨v,x⟩ ⟨w,y⟩ h
  have hh := B.doubleWiring.oriented_side_injective
    (B.origEnd ⟨v,(B.kind v).table.mate x.val⟩)
    (B.origEnd ⟨w,(B.kind w).table.mate y.val⟩)
    ((B.kind v).table.orientation x.val |>.mpr x.property.1)
    ((B.kind w).table.orientation y.val |>.mpr y.property.1) h
  have hv : v=w := Sum.inl.inj (congrArg Sigma.fst hh)
  subst w
  have hc := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  have hx : x.val=y.val := (B.kind v).table.involutive.injective hc
  exact congrArg (Sigma.mk v) (Subtype.ext hx)
lemma mirrorStripSide_injective : Function.Injective B.mirrorStripSide := by
  rintro ⟨v,x⟩ ⟨w,y⟩ h
  have hh := B.doubleWiring.oriented_side_injective
    (B.mirrorEnd ⟨v,x.val⟩) (B.mirrorEnd ⟨w,y.val⟩)
    ((B.kind v).mirror_negative x.val x.property.1)
    ((B.kind w).mirror_negative y.val y.property.1) h
  have hv : v=w := Sum.inr.inj (congrArg Sigma.fst hh)
  subst w
  have hc := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  have hx : x.val=y.val := (B.kind v).mirrorEnd.injective hc
  exact congrArg (Sigma.mk v) (Subtype.ext hx)
lemma origStrip_ne_mirror (x y : B.StripNode) : B.origStripSide x≠B.mirrorStripSide y := by
  intro h
  have hh := B.doubleWiring.oriented_side_injective
    (B.origEnd ⟨x.1,(B.kind x.1).table.mate x.2.val⟩) (B.mirrorEnd ⟨y.1,y.2.val⟩)
    ((B.kind x.1).table.orientation x.2.val |>.mpr x.2.property.1)
    ((B.kind y.1).mirror_negative y.2.val y.2.property.1) h
  have hv : (Sum.inl x.1 : Fin (B.length+1) ⊕ Fin (B.length+1))=Sum.inr y.1 :=
    congrArg (fun z : B.DoubleEnd => z.1) hh
  cases hv

/-- Even when old facet labels repeat, distinct strip roots give disjoint
actual boundary circuits. They may therefore be assigned distinct fresh disk
facets rather than silently joining unrelated components. -/
lemma stripCycle_disjoint {r t : B.StripNode} (h : r≠t) : Disjoint (B.stripCycle r) (B.stripCycle t) := by
  apply Set.disjoint_left.mpr
  rintro s ⟨x,hx,hsx⟩ ⟨y,hy,hsy⟩
  rcases hsx with rfl|rfl <;> rcases hsy with hs|hs
  · have he := B.origStripSide_injective hs
    exact h (hx.symm.trans ((congrArg B.stripForest.root he).trans hy))
  · exact B.origStrip_ne_mirror x y hs
  · exact B.origStrip_ne_mirror y x hs.symm
  · have he := B.mirrorStripSide_injective hs
    exact h (hx.symm.trans ((congrArg B.stripForest.root he).trans hy))
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
open scoped Classical
variable {F : Type} {p : F} {a b : List F} (B : RealizedBand p a b)
noncomputable def origPrincipal (v : Fin (B.length+1)) :=
  B.doubleWiring.sideOf (B.origEnd ⟨v,(B.kind v).input,none⟩)
noncomputable def mirrorPrincipal (v : Fin (B.length+1)) :=
  B.doubleWiring.sideOf (B.mirrorEnd ⟨v,(B.kind v).output,none⟩)
lemma positive_classification (v : Fin (B.length+1))
    (z : (p : (B.kind v).table.Port) × Option ((B.kind v).table.Child p))
    (h : (B.kind v).table.endpoint z.1=z.2.isNone) :
    z=⟨(B.kind v).input,none⟩ ∨ ∃ x : (B.kind v).SecondaryNode,
      z=(B.kind v).table.mate x.val := by
  by_cases hz : z=⟨(B.kind v).input,none⟩
  · exact Or.inl hz
  · right
    have hn : (B.kind v).table.endpoint ((B.kind v).table.mate z).1≠
        ((B.kind v).table.mate z).2.isNone := by
      intro he
      exact (B.kind v).table.orientation z |>.mp he <| h
    have hp : (B.kind v).table.mate z≠⟨(B.kind v).output,none⟩ := by
      intro hh
      have hc := congrArg (B.kind v).table.mate hh
      rw [(B.kind v).table.involutive] at hc
      have hi := (B.kind v).table.involutive ⟨(B.kind v).input,none⟩
      rw [Kind.principal_corner] at hi
      exact hz (hc.trans hi)
    exact ⟨⟨(B.kind v).table.mate z,hn,hp⟩,((B.kind v).table.involutive z).symm⟩

/-- Exhaustion of every literal side of the doubled cut band. All facets of
lower rank arise from the enumerated secondary strips; transverse seams do not
leave hidden boundary germs. -/
theorem double_side_exhaustive (s : Side B.doubleWiring.Seam B.doubleWiring.seamArity) :
    (∃ v,s=B.origPrincipal v) ∨ (∃ v,s=B.mirrorPrincipal v) ∨
    ∃ x : B.StripNode,s=B.origStripSide x ∨ s=B.mirrorStripSide x := by
  obtain ⟨⟨v,z⟩,he,rfl⟩ := B.doubleWiring.oriented_side_exists s
  rcases v with v|v
  · obtain hz|⟨x,hx⟩ := B.positive_classification v z he
    · left; exact ⟨v,congrArg (fun z => B.doubleWiring.sideOf (B.origEnd ⟨v,z⟩)) hz⟩
    · right; right; exact ⟨⟨v,x⟩,Or.inl (congrArg (fun z => B.doubleWiring.sideOf (B.origEnd ⟨v,z⟩)) hx)⟩
  · let y := (B.kind v).mirrorEnd.symm z
    have hy : (B.kind v).mirrorEnd y=z := (B.kind v).mirrorEnd.apply_symm_apply z
    have hn : (B.kind v).table.endpoint y.1≠y.2.isNone := by
      have hi := (B.kind v).mirror_isNone y
      have hh := (B.kind v).mirror_endpoint y.1
      change (B.kind v).mirror.table.endpoint ((B.kind v).mirrorEnd y).1=!(B.kind v).table.endpoint y.1 at hh
      rw [hy] at hh hi
      change (B.kind v).mirror.table.endpoint z.1=z.2.isNone at he
      intro H
      have hnot : (!(B.kind v).table.endpoint y.1)=(B.kind v).table.endpoint y.1 := hh.symm.trans (he.trans (hi.trans H.symm))
      exact (Bool.not_eq_self _).mp hnot
    by_cases hp : y=⟨(B.kind v).output,none⟩
    · right; left; refine ⟨v,?_⟩
      exact congrArg (fun z => B.doubleWiring.sideOf (⟨.inr v,z⟩ : B.DoubleEnd))
        (hy.symm.trans (congrArg (B.kind v).mirrorEnd hp))
    · right; right; refine ⟨⟨v,⟨y,hn,hp⟩⟩,Or.inr ?_⟩
      exact congrArg (fun z => B.doubleWiring.sideOf (⟨.inr v,z⟩ : B.DoubleEnd)) hy.symm
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand

end OAI
