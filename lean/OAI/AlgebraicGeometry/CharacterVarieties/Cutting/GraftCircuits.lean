import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.BoundarySurgery

namespace OAI

/-!
# The principal and secondary boundary circuits of an inverse-band graft.

This formalizes the band reconstruction for filtered surface local systems in
*Integral points on character varieties of curves*.
-/

namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical
open VertexTable BoundarySurgery
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))

noncomputable abbrev base := A.toWiring.sum B.doubleWiring
noncomputable def oldEmbedding : Side S arity ↪ Side (base A q B).Seam (base A q B).seamArity where
  toFun a := A.toWiring.sumSides B.doubleWiring (.inl (A.wiringSides a))
  inj' := by
    intro a b h
    exact A.wiringSides.injective (Sum.inl.inj ((A.toWiring.sumSides B.doubleWiring).injective h))
noncomputable def bandEmbedding : Side B.doubleWiring.Seam B.doubleWiring.seamArity ↪
    Side (base A q B).Seam (base A q B).seamArity where
  toFun a := A.toWiring.sumSides B.doubleWiring (.inr a)
  inj' := by
    intro a b h
    exact Sum.inr.inj ((A.toWiring.sumSides B.doubleWiring).injective h)

lemma base_old_next (a : Side S arity) :
    (base A q B).boundaryPerm (oldEmbedding A q B a)=
      oldEmbedding A q B (A.vertexAssembly.corners.boundaryNext a) := by
  exact (A.toWiring.sum_boundary_left B.doubleWiring (A.wiringSides a)).trans
    (congrArg (fun z => A.toWiring.sumSides B.doubleWiring (.inl z)) (A.toWiring_boundary a))
lemma base_band_next (a : Side B.doubleWiring.Seam B.doubleWiring.seamArity) :
    (base A q B).boundaryPerm (bandEmbedding A q B a)=
      bandEmbedding A q B (B.doubleWiring.boundaryPerm a) :=
  A.toWiring.sum_boundary_right B.doubleWiring a

lemma base_old_cycle (s : Finset (Side S arity))
    (hs : A.vertexAssembly.corners.boundaryNext.IsCycleOn (s : Set (Side S arity))) :
    (base A q B).boundaryPerm.IsCycleOn (s.map (oldEmbedding A q B) : Set _) :=
  embedding_isCycle _ _ _ (base_old_next A q B) s hs
lemma base_band_cycle (s : Finset (Side B.doubleWiring.Seam B.doubleWiring.seamArity))
    (hs : B.doubleWiring.boundaryPerm.IsCycleOn (s : Set _)) :
    (base A q B).boundaryPerm.IsCycleOn (s.map (bandEmbedding A q B) : Set _) :=
  embedding_isCycle _ _ _ (base_band_next A q B) s hs

lemma old_band_ne (a : Side S arity) (b : Side B.doubleWiring.Seam B.doubleWiring.seamArity) :
    oldEmbedding A q B a≠bandEmbedding A q B b := by
  intro h
  have hh := (A.toWiring.sumSides B.doubleWiring).injective h
  cases hh
lemma old_band_disjoint (s : Finset (Side S arity))
    (t : Finset (Side B.doubleWiring.Seam B.doubleWiring.seamArity)) :
    Disjoint (s.map (oldEmbedding A q B)) (t.map (bandEmbedding A q B)) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨y,hy,he⟩ := Finset.mem_map.mp hb
  exact old_band_ne A q B x y he.symm

lemma base_eq : base A q B=graftBase A B.doublePatch (doubleDecoration B.decoration) q
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl) := rfl

lemma graft_arity (s : (base A q B).Seam) :
    (base A q B).seamArity (graftPerm A B.doublePatch q s)=(base A q B).seamArity s :=
  graftPerm_arity A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl) s

lemma wiring_eq_base_rewire : wiring A q B=
    (base A q B).rewire (graftPerm A B.doublePatch q) (graft_arity A q B) :=
  graftWiring_eq_rewire A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)

lemma next_base (a : Side (base A q B).Seam (base A q B).seamArity) :
    next A q B a=(base A q B).parentSurgery (graftPerm A B.doublePatch q)
      ((base A q B).boundaryPerm ((base A q B).childSurgery (graftPerm A B.doublePatch q)
        (graft_arity A q B) a)) := by
  have he := wiring_eq_base_rewire A q B
  have hn : (wiring A q B).boundaryPerm=
      ((base A q B).rewire (graftPerm A B.doublePatch q) (graft_arity A q B)).boundaryPerm := by
    rw [he]
  change (wiring A q B).boundaryPerm a=_
  rw [hn]
  exact (base A q B).rewire_boundary_unchanged _ _ a
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
open scoped Classical
variable {F : Type} {p : F} {a b : List F} (B : RealizedBand p a b)
noncomputable def stripFinset (r : B.StripNode) :
    Finset (Side B.doubleWiring.Seam B.doubleWiring.seamArity) :=
  (B.stripCycle r).toFinite.toFinset
@[simp] lemma mem_stripFinset (s) (r : B.StripNode) : s∈B.stripFinset r ↔ s∈B.stripCycle r :=
  Set.Finite.mem_toFinset _
@[simp] lemma coe_stripFinset (r : B.StripNode) : (B.stripFinset r : Set _)=B.stripCycle r := by
  ext s
  exact B.mem_stripFinset s r
lemma stripFinset_cycle (r : B.StripNode) :
    B.doubleWiring.boundaryPerm.IsCycleOn (B.stripFinset r : Set _) := by
  rw [B.coe_stripFinset]
  exact B.stripCycle_isCycle r
lemma stripFinset_disjoint {r t : B.StripNode} (h : r≠t) :
    Disjoint (B.stripFinset r) (B.stripFinset t) := by
  apply Finset.disjoint_left.mpr
  intro s hs ht
  exact Set.disjoint_left.mp (B.stripCycle_disjoint h)
    ((B.mem_stripFinset _ _).mp hs) ((B.mem_stripFinset _ _).mp ht)
lemma shortFinsets_disjoint (hinj : Function.Injective B.shortRoot) {x y : B.ShortChild} (h : x≠y) :
    Disjoint (B.stripFinset (B.shortRoot x).val) (B.stripFinset (B.shortRoot y).val) :=
  B.stripFinset_disjoint (fun he => h (hinj (Subtype.ext he)))
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand
open scoped Classical
variable {F : Type} {p : F} {a b : List F} (B : RealizedBand p a b)
lemma inputContact_number (c) :
    sideNumber (B.mirrorStripSide (B.inputStrip c))=
      (B.doublePatch.plus (.inr false),some (((B.kind 0).childEnumeration (B.kind 0).input c).val)) := by
  rw [mirrorStripSide,B.doubleWiring.sideOf_number]
  change ((B.doubleWiring.endOf (B.doublePatch.minus (.inr false)).val).1,
    some (((B.kind 0).mirror.childEnumeration ((B.kind 0).mirrorPort ((B.kind 0).input))
      ((B.kind 0).mirrorChild (B.kind 0).input c)).val))=_
  rw [B.doubleWiring.endOf_negative]
  have hw : B.doubleWiring.wire (B.doublePatch.plus (.inr false))=B.doublePatch.minus (.inr false) :=
    by
      exact B.patch.double_wire_exposed_plus B.shortFirst B.shortLast B.shortFirst
  rw [←hw,Equiv.symm_apply_apply,Kind.mirror_childEnumeration]
  rfl
lemma outputContact_number (c) :
    sideNumber (B.origStripSide (B.outputStrip c))=
      (B.doublePatch.plus (.inr true),
        some (((B.kind (Fin.last B.length)).childEnumeration (B.kind (Fin.last B.length)).output c).val)) := by
  rw [origStripSide]
  change sideNumber (B.doubleWiring.sideOf (B.origEnd ⟨Fin.last B.length,
    (B.kind (Fin.last B.length)).table.mate ((B.kind (Fin.last B.length)).table.mate ⟨_,some c⟩)⟩))=_
  rw [(B.kind (Fin.last B.length)).table.involutive,B.doubleWiring.sideOf_number]
  change ((B.doubleWiring.endOf (B.doublePatch.minus (.inr true)).val).1,
    some (((B.kind (Fin.last B.length)).childEnumeration (B.kind (Fin.last B.length)).output c).val))=_
  rw [B.doubleWiring.endOf_negative]
  have hw : B.doubleWiring.wire (B.doublePatch.plus (.inr true))=B.doublePatch.minus (.inr true) :=
    by
      exact B.patch.double_wire_exposed_minus B.shortFirst B.shortLast B.shortLast
  rw [←hw,Equiv.symm_apply_apply]
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable.RealizedBand

namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical
open VertexTable BoundarySurgery
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
noncomputable abbrev cutPort := graftPlus A B.doublePatch (.inl q)
noncomputable abbrev shortPort (b : Bool) := graftPlus A B.doublePatch (.inr (.inr b))
lemma cutPort_arity : (base A q B).seamArity (cutPort A q B)=arity q := A.portAt_arity q true
lemma input_arity : (B.kind 0).arity (B.kind 0).input=arity q := by
  have h := congrArg List.length B.input_children
  simpa only [Decoration.children_length,PortAssembly.seamChildren,List.length_ofFn] using h
lemma output_arity : (B.kind (Fin.last B.length)).arity (B.kind (Fin.last B.length)).output=arity q := by
  have h := congrArg List.length B.output_children
  simpa only [Decoration.children_length,PortAssembly.seamChildren,List.length_ofFn] using h
lemma shortPort_arity (b : Bool) :
    (base A q B).seamArity (shortPort A q B b)=(base A q B).seamArity (cutPort A q B) := by
  rw [cutPort_arity]
  cases b
  · exact input_arity A q B
  · exact ((B.kind (Fin.last B.length)).mirror_arity _).trans (output_arity A q B)
lemma cutPort_ne_short (b : Bool) : cutPort A q B≠shortPort A q B b := by
  intro he
  have h := (graftPlus A B.doublePatch).injective he
  cases h
noncomputable def shortChildAt (z : Fin ((base A q B).seamArity (cutPort A q B)) × Bool) : B.ShortChild :=
  match z.2 with
  | false => .inl (((B.kind 0).childEnumeration (B.kind 0).input).symm
      (finCongr ((cutPort_arity A q B).trans (input_arity A q B).symm) z.1))
  | true => .inr (((B.kind (Fin.last B.length)).childEnumeration (B.kind (Fin.last B.length)).output).symm
      (finCongr ((cutPort_arity A q B).trans (output_arity A q B).symm) z.1))
lemma shortChildAt_injective : Function.Injective (shortChildAt A q B) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  cases b <;> cases c
  · exact Prod.ext ((finCongr _).injective (((B.kind 0).childEnumeration _).symm.injective (Sum.inl.inj h))) rfl
  · cases h
  · cases h
  · exact Prod.ext ((finCongr _).injective (((B.kind (Fin.last B.length)).childEnumeration _).symm.injective (Sum.inr.inj h))) rfl
noncomputable def shortCycle (z : Fin ((base A q B).seamArity (cutPort A q B)) × Bool) :=
  (B.stripFinset (B.shortRoot (shortChildAt A q B z)).val).map (bandEmbedding A q B)
lemma shortCycle_cycle (z) : (base A q B).boundaryPerm.IsCycleOn (shortCycle A q B z : Set _) :=
  base_band_cycle A q B _ (B.stripFinset_cycle _)
lemma shortCycles_disjoint (hinj : Function.Injective B.shortRoot) {z w} (hne : z≠w) :
    Disjoint (shortCycle A q B z) (shortCycle A q B w) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨y,hy,he⟩ := Finset.mem_map.mp hb
  have hxy := (bandEmbedding A q B).injective he
  subst y
  exact Finset.disjoint_left.mp (B.shortFinsets_disjoint hinj
    (fun h=>hne (shortChildAt_injective A q B h))) hx hy
lemma tripleNew_mem_shortCycle (z) :
    (base A q B).tripleNew (cutPort A q B) (shortPort A q B false) (shortPort A q B true)
      (shortPort_arity A q B false) (shortPort_arity A q B true) z∈shortCycle A q B z := by
  rcases z with ⟨i,b⟩
  cases b
  · let c := ((B.kind 0).childEnumeration (B.kind 0).input).symm
      (finCongr ((cutPort_arity A q B).trans (input_arity A q B).symm) i)
    apply Finset.mem_map.mpr
    refine ⟨B.mirrorStripSide (B.inputStrip c),(B.mem_stripFinset _ _).mpr (B.inputContact_cycle c),?_⟩
    apply sideNumber_injective
    change sideNumber (A.toWiring.sumSides B.doubleWiring (.inr (B.mirrorStripSide (B.inputStrip c))))=_
    rw [A.toWiring.sumSides_number_right]
    have h := B.inputContact_number c
    have hh := congrArg (fun x => (sumPortAt A.kind (sumKind B.kind (mirrorKind B.kind)) true (.inr x.1),x.2)) h
    refine hh.trans ?_
    change (_,some (((B.kind 0).childEnumeration _ c).val))=(_,some i.val)
    rw [Equiv.apply_symm_apply]
    rfl
  · let c := ((B.kind (Fin.last B.length)).childEnumeration (B.kind (Fin.last B.length)).output).symm
      (finCongr ((cutPort_arity A q B).trans (output_arity A q B).symm) i)
    apply Finset.mem_map.mpr
    refine ⟨B.origStripSide (B.outputStrip c),(B.mem_stripFinset _ _).mpr (B.outputContact_cycle c),?_⟩
    apply sideNumber_injective
    change sideNumber (A.toWiring.sumSides B.doubleWiring (.inr (B.origStripSide (B.outputStrip c))))=_
    rw [A.toWiring.sumSides_number_right]
    have h := B.outputContact_number c
    have hh := congrArg (fun x => (sumPortAt A.kind (sumKind B.kind (mirrorKind B.kind)) true (.inr x.1),x.2)) h
    refine hh.trans ?_
    change (_,some (((B.kind (Fin.last B.length)).childEnumeration _ c).val))=(_,some i.val)
    rw [Equiv.apply_symm_apply]
    rfl
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft

namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical
open VertexTable BoundarySurgery
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
noncomputable abbrev contacts := (base A q B).tripleContacts (cutPort A q B)
noncomputable abbrev oldContact := (base A q B).tripleOld (cutPort A q B)
noncomputable abbrev newContact := (base A q B).tripleNew (cutPort A q B) (shortPort A q B false)
  (shortPort A q B true) (shortPort_arity A q B false) (shortPort_arity A q B true)
noncomputable abbrev childNext := (base A q B).boundaryPerm *
  (base A q B).childSurgery (graftPerm A B.doublePatch q) (graft_arity A q B)
noncomputable def secondaryCircle (s : Finset (Side S arity)) :=
  attachedCircleOn (s.map (oldEmbedding A q B)) (oldContact A q B) (shortCycle A q B) (contacts A q B)
lemma oldContact_eq (z) : oldContact A q B z=
    oldEmbedding A q B ⟨q,some (finCongr (cutPort_arity A q B) z.1)⟩ := by
  apply sideNumber_injective
  change (_,some z.1.val)=sideNumber (A.toWiring.sumSides B.doubleWiring (.inl _))
  rw [A.toWiring.sumSides_number_left]
  exact (congrArg (fun w => (sumPortAt A.kind (sumKind B.kind (mirrorKind B.kind)) true (.inl w.1),w.2))
    (A.wiringSides_number ⟨q,some (finCongr (cutPort_arity A q B) z.1)⟩)).symm
lemma childNext_eq_family : childNext A q B=
    preSpliceFamily (base A q B).boundaryPerm (oldContact A q B) (newContact A q B) (contacts A q B) := by
  have he := (base A q B).triple_preSplice (cutPort A q B) (shortPort A q B false)
    (shortPort A q B true) (cutPort_ne_short A q B false) (cutPort_ne_short A q B true)
    (shortPort_arity A q B false) (shortPort_arity A q B true) (base A q B).boundaryPerm
    (fun s => by
      calc
        _ = (base A q B).seamArity ((graftPerm A B.doublePatch q) s) := by
          congr 1
          exact congrArg (fun C : Equiv.Perm _ => C s)
            ((congrArg₂ (fun x y : Equiv.Perm _ => x*y) (swap_irrel _ _ _ _) (swap_irrel _ _ _ _)).trans
              (graftPerm_swaps A B.doublePatch q).symm)
        _ = _ := graft_arity A q B s)
  refine Eq.trans ?_ he
  unfold childNext
  congr 2
  exact (graftPerm_swaps A B.doublePatch q).trans
    (congrArg₂ (fun x y : Equiv.Perm _ => x*y) (swap_irrel _ _ _ _) (swap_irrel _ _ _ _))
lemma oldContact_not_shortCycle (i j) : oldContact A q B i∉shortCycle A q B j := by
  rw [oldContact_eq]
  intro h
  obtain ⟨a,ha,he⟩ := Finset.mem_map.mp h
  exact old_band_ne A q B _ a he.symm
lemma oldCircle_short_disjoint (s : Finset (Side S arity)) (j) :
    Disjoint (s.map (oldEmbedding A q B)) (shortCycle A q B j) :=
  old_band_disjoint A q B _ _
lemma actual_child_circle {G : Type*} [Group G]
    (s : Finset (Side S arity))
    (hs : A.vertexAssembly.corners.boundaryNext.IsCycleOn (s : Set (Side S arity)))
    (hinj : Function.Injective B.shortRoot)
    (u : Side (base A q B).Seam (base A q B).seamArity → G)
    (hu : ∀ j,∀ a∈shortCycle A q B j,u a=1) :
    (childNext A q B).IsCycleOn (secondaryCircle A q B s : Set _) ∧
    ∀ a∈s,cycleWord (childNext A q B) u (oldEmbedding A q B a) (secondaryCircle A q B s).card=
      cycleWord A.vertexAssembly.corners.boundaryNext (u ∘ oldEmbedding A q B) a s.card := by
  rw [childNext_eq_family]
  have hc := preSpliceFamily_cycleOn (base A q B).boundaryPerm (s.map (oldEmbedding A q B))
    (oldContact A q B) (newContact A q B) (shortCycle A q B) (contacts A q B)
    (base_old_cycle A q B s hs) (fun j _=>shortCycle_cycle A q B j)
    (fun j _=>tripleNew_mem_shortCycle A q B j) (fun j _=>oldCircle_short_disjoint A q B s j)
    (fun i _ j _=>oldContact_not_shortCycle A q B i j)
    ((List.pairwise_iff_getElem).mpr (by
      intro i j hi hj hij
      apply shortCycles_disjoint A q B hinj
      exact List.Nodup.getElem_inj_iff ((base A q B).tripleContacts_nodup (cutPort A q B)) |>.not.mpr (Nat.ne_of_lt hij)))
    u (fun j _=>hu j)
  refine ⟨hc.1,?_⟩
  intro a ha
  change cycleWord _ _ _ (attachedCircleOn _ _ _ _).card=_
  rw [hc.2 _ (Finset.mem_map.mpr ⟨a,ha,rfl⟩),Finset.card_map]
  exact embedding_cycleWord _ _ _ (base_old_next A q B) u a s.card
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft

namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
variable {α ι : Type}
lemma attachedCircleOn_all (s : Finset α) (x : ι → α) (t : ι → Finset α) (is : List ι)
    (P : α → Prop) (hs : ∀ a∈s,P a) (ht : ∀ i∈is,∀ a∈t i,P a) :
    ∀ a∈attachedCircleOn s x t is,P a := by
  induction is generalizing s with
  | nil => exact hs
  | cons i is ih =>
    apply ih
    · intro a ha
      split_ifs at ha with h
      · rcases Finset.mem_union.mp ha with ha|ha
        · exact hs a ha
        · exact ht i List.mem_cons_self a ha
      · exact hs a ha
    · exact fun j hj => ht j (List.mem_cons_of_mem i hj)
end IntegralCharacterVarieties.BoundarySurgery
namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical
open VertexTable BoundarySurgery
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
lemma oldEmbedding_parent : oldEmbedding A q B ⟨q,none⟩=⟨cutPort A q B,none⟩ := by
  apply sideNumber_injective
  change sideNumber (A.toWiring.sumSides B.doubleWiring (.inl (A.wiringSides ⟨q,none⟩)))=_
  rw [A.toWiring.sumSides_number_left]
  exact congrArg (fun x => (sumPortAt A.kind (sumKind B.kind (mirrorKind B.kind)) true (.inl x.1),x.2))
    (A.wiringSides_number ⟨q,none⟩)
lemma bandEmbedding_input_parent : bandEmbedding A q B (B.origPrincipal 0)=⟨shortPort A q B false,none⟩ := by
  apply sideNumber_injective
  change sideNumber (A.toWiring.sumSides B.doubleWiring (.inr (B.origPrincipal 0)))=_
  rw [A.toWiring.sumSides_number_right]
  have h : sideNumber (B.origPrincipal 0)=(B.doublePatch.plus (.inr false),none) := by
    rw [RealizedBand.origPrincipal,B.doubleWiring.sideOf_number]
    change ((B.doubleWiring.endOf (B.doublePatch.plus (.inr false)).val).1,none)=_
    rw [B.doubleWiring.endOf_positive]
  exact congrArg (fun x => (sumPortAt A.kind (sumKind B.kind (mirrorKind B.kind)) true (.inr x.1),x.2)) h
lemma bandEmbedding_output_parent : bandEmbedding A q B (B.mirrorPrincipal (Fin.last B.length))=
    ⟨shortPort A q B true,none⟩ := by
  apply sideNumber_injective
  change sideNumber (A.toWiring.sumSides B.doubleWiring (.inr (B.mirrorPrincipal (Fin.last B.length))))=_
  rw [A.toWiring.sumSides_number_right]
  have h : sideNumber (B.mirrorPrincipal (Fin.last B.length))=(B.doublePatch.plus (.inr true),none) := by
    rw [RealizedBand.mirrorPrincipal,B.doubleWiring.sideOf_number]
    change ((B.doubleWiring.endOf (B.doublePatch.plus (.inr true)).val).1,none)=_
    rw [B.doubleWiring.endOf_positive]
  exact congrArg (fun x => (sumPortAt A.kind (sumKind B.kind (mirrorKind B.kind)) true (.inr x.1),x.2)) h
lemma graftPerm_away (s : (base A q B).Seam) (hq : s≠cutPort A q B)
    (hf : s≠shortPort A q B false) (ht : s≠shortPort A q B true) :
    graftPerm A B.doublePatch q s=s := by
  rw [graftPerm_swaps,Equiv.Perm.mul_apply]
  simp only [cutPort,shortPort] at hq hf ht
  simp only [Equiv.swap_apply_def,ite_eq_right hq,ite_eq_right ht,ite_eq_right hf]
lemma parentSurgery_away (a : Side (base A q B).Seam (base A q B).seamArity)
    (hq : a≠⟨cutPort A q B,none⟩) (hf : a≠⟨shortPort A q B false,none⟩)
    (ht : a≠⟨shortPort A q B true,none⟩) :
    (base A q B).parentSurgery (graftPerm A B.doublePatch q) a=a := by
  apply PortWiring.parentSurgery_fixed
  intro ha
  have hea : a=⟨a.1,none⟩ := Sigma.ext rfl (heq_of_eq ha)
  apply graftPerm_away A q B
  · intro he
    exact hq (hea.trans
      (congrArg (fun s => (⟨s,none⟩ : Side (base A q B).Seam (base A q B).seamArity)) he))
  · intro he
    exact hf (hea.trans
      (congrArg (fun s => (⟨s,none⟩ : Side (base A q B).Seam (base A q B).seamArity)) he))
  · intro he
    exact ht (hea.trans
      (congrArg (fun s => (⟨s,none⟩ : Side (base A q B).Seam (base A q B).seamArity)) he))
lemma old_parentSurgery_away (a : Side S arity) (ha : a≠⟨q,none⟩) :
    (base A q B).parentSurgery (graftPerm A B.doublePatch q) (oldEmbedding A q B a)=oldEmbedding A q B a := by
  apply parentSurgery_away A q B
  · rw [←oldEmbedding_parent]
    exact fun h => ha ((oldEmbedding A q B).injective h)
  · rw [←bandEmbedding_input_parent]
    exact old_band_ne A q B _ _
  · rw [←bandEmbedding_output_parent]
    exact old_band_ne A q B _ _
lemma strip_parentSurgery_away (j) (a) (ha : a∈shortCycle A q B j) :
    (base A q B).parentSurgery (graftPerm A B.doublePatch q) a=a := by
  obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp ha
  have hr := (B.mem_stripFinset _ _).mp hb
  apply parentSurgery_away A q B
  · rw [←oldEmbedding_parent]
    exact fun h => old_band_ne A q B _ _ h.symm
  · rw [←bandEmbedding_input_parent]
    intro he
    have hh := (bandEmbedding A q B).injective he
    subst b
    have hn := (B.sideStripRoot_eq_some_iff _ _).mpr hr
    rw [B.sideStripRoot_origPrincipal] at hn
    cases hn
  · rw [←bandEmbedding_output_parent]
    intro he
    have hh := (bandEmbedding A q B).injective he
    subst b
    have hn := (B.sideStripRoot_eq_some_iff _ _).mpr hr
    rw [B.sideStripRoot_mirrorPrincipal] at hn
    cases hn
lemma secondary_parentSurgery_away (s : Finset (Side S arity)) (hq : (⟨q,none⟩ : Side S arity)∉s)
    (a) (ha : a∈secondaryCircle A q B s) :
    (base A q B).parentSurgery (graftPerm A B.doublePatch q) a=a := by
  apply attachedCircleOn_all _ _ _ _
    (fun a => (base A q B).parentSurgery (graftPerm A B.doublePatch q) a=a) ?_ ?_ a ha
  · intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_map.mp hb
    exact old_parentSurgery_away A q B c (fun he => hq (he ▸ hc))
  · exact fun j _ => strip_parentSurgery_away A q B j
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft

namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
variable {α ι : Type}
lemma attachedCircleOn_subset (s : Finset α) (x : ι → α) (t : ι → Finset α) (is : List ι) :
    s⊆attachedCircleOn s x t is := by
  induction is generalizing s with
  | nil => exact Finset.Subset.refl _
  | cons i is ih =>
    change s⊆attachedCircleOn (if x i∈s then s∪t i else s) x t is
    refine Finset.Subset.trans ?_ (ih _)
    split_ifs
    · exact Finset.subset_union_left
    · exact Finset.Subset.refl _
end IntegralCharacterVarieties.BoundarySurgery
namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical
open VertexTable BoundarySurgery
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
/-- Full ACTUAL three-port rewiring, not merely its child-side cyclic template:
every old circle away from the cut parent remains one cycle, and its based
noncommutative word is unchanged after inserting both strips at every contact. -/
theorem actual_secondary_circle {G : Type*} [Group G]
    (s : Finset (Side S arity))
    (hs : A.vertexAssembly.corners.boundaryNext.IsCycleOn (s : Set (Side S arity)))
    (hq : (⟨q,none⟩ : Side S arity)∉s)
    (hinj : Function.Injective B.shortRoot)
    (u : Side (base A q B).Seam (base A q B).seamArity → G)
    (hu : ∀ j,∀ a∈shortCycle A q B j,u a=1) :
    (next A q B).IsCycleOn (secondaryCircle A q B s : Set (Side (base A q B).Seam (base A q B).seamArity)) ∧
    ∀ a∈s,cycleWord (next A q B) u (oldEmbedding A q B a) (secondaryCircle A q B s).card=
      cycleWord A.vertexAssembly.corners.boundaryNext (u ∘ oldEmbedding A q B) a s.card := by
  have hc := actual_child_circle A q B s hs hinj u hu
  have he : Set.EqOn (next A q B) (childNext A q B) (secondaryCircle A q B s : Set (Side (base A q B).Seam (base A q B).seamArity)) := by
    intro a ha
    exact (next_base A q B a).trans
      (secondary_parentSurgery_away A q B s hq _ (hc.1.1.mapsTo ha))
  refine ⟨isCycleOn_eqOn hc.1 he,?_⟩
  intro a ha
  have ham : oldEmbedding A q B a∈secondaryCircle A q B s :=
    attachedCircleOn_subset _ _ _ _ (Finset.mem_map.mpr ⟨a,ha,rfl⟩)
  exact (cycleWord_eqOn hc.1.1.mapsTo he u ham _).trans (hc.2 a ha)
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft

namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
variable {α ι : Type}
lemma preSpliceFamily_at_away (N : Equiv.Perm α) (x y : ι → α) (is : List ι) (a : α)
    (hx : ∀ i∈is,a≠x i) (hy : ∀ i∈is,a≠y i) :
    preSpliceFamily N x y is a=N a := by
  induction is generalizing N with
  | nil => rfl
  | cons i is ih =>
    rw [preSpliceFamily,ih (N*Equiv.swap (x i) (y i))
      (fun j hj => hx j (List.mem_cons_of_mem i hj))
      (fun j hj => hy j (List.mem_cons_of_mem i hj))]
    exact congrArg N (Equiv.swap_apply_of_ne_of_ne (hx i List.mem_cons_self) (hy i List.mem_cons_self))
end IntegralCharacterVarieties.BoundarySurgery
namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical
open VertexTable BoundarySurgery
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))

lemma anyStrip_parentSurgery_away (r : B.StripRoot)
    (b : Side B.doubleWiring.Seam B.doubleWiring.seamArity) (hb : b∈B.stripCycle r.val) :
    (base A q B).parentSurgery (graftPerm A B.doublePatch q) (bandEmbedding A q B b)=bandEmbedding A q B b := by
  apply parentSurgery_away A q B
  · rw [←oldEmbedding_parent]
    exact fun h => old_band_ne A q B _ _ h.symm
  · rw [←bandEmbedding_input_parent]
    intro he
    have hh := (bandEmbedding A q B).injective he
    subst b
    have hn := (B.sideStripRoot_eq_some_iff _ _).mpr hb
    rw [B.sideStripRoot_origPrincipal] at hn
    cases hn
  · rw [←bandEmbedding_output_parent]
    intro he
    have hh := (bandEmbedding A q B).injective he
    subst b
    have hn := (B.sideStripRoot_eq_some_iff _ _).mpr hb
    rw [B.sideStripRoot_mirrorPrincipal] at hn
    cases hn

lemma freshStrip_newContact_ne (r : B.FreshStrip)
    (b : Side B.doubleWiring.Seam B.doubleWiring.seamArity) (hb : b∈B.stripCycle r.val.val) (j) :
    bandEmbedding A q B b≠newContact A q B j := by
  intro he
  have hh := tripleNew_mem_shortCycle A q B j
  change newContact A q B j ∈ shortCycle A q B j at hh
  rw [←he] at hh
  obtain ⟨c,hc,hcb⟩ := Finset.mem_map.mp hh
  have hcb' := (bandEmbedding A q B).injective hcb
  subst c
  have hx := (B.mem_stripFinset _ _).mp hc
  have hy := (B.sideStripRoot_eq_some_iff _ _).mpr hx
  have hz := (B.sideStripRoot_eq_some_iff _ _).mpr hb
  exact r.property ⟨shortChildAt A q B j,Option.some.inj (hy.symm.trans hz)⟩

lemma next_freshStrip (r : B.FreshStrip)
    (b : Side B.doubleWiring.Seam B.doubleWiring.seamArity) (hb : b∈B.stripCycle r.val.val) :
    next A q B (bandEmbedding A q B b)=bandEmbedding A q B (B.doubleWiring.boundaryPerm b) := by
  have hc : childNext A q B (bandEmbedding A q B b)=(base A q B).boundaryPerm (bandEmbedding A q B b) := by
    rw [childNext_eq_family]
    apply preSpliceFamily_at_away
    · intro j hj
      rw [oldContact_eq]
      exact fun h => old_band_ne A q B _ _ h.symm
    · intro j hj
      exact freshStrip_newContact_ne A q B r b hb j
  have hn := next_base A q B (bandEmbedding A q B b)
  change next A q B (bandEmbedding A q B b)=
    (base A q B).parentSurgery (graftPerm A B.doublePatch q)
      (childNext A q B (bandEmbedding A q B b)) at hn
  rw [hc,base_band_next] at hn
  refine hn.trans (anyStrip_parentSurgery_away A q B r.val _ ?_)
  exact B.stripCycle_next r.val.val hb

/-- Each untouched connected strip is STILL its literal single boundary
circle after all three-port sewings. No phantom fresh facet or additional
boundary component is inferred merely from ranks. -/
theorem freshStrip_actual_circle (r : B.FreshStrip) :
    (next A q B).IsCycleOn
      ((B.stripFinset r.val.val).map (bandEmbedding A q B) : Set (Side (base A q B).Seam (base A q B).seamArity)) := by
  have hs := base_band_cycle A q B (B.stripFinset r.val.val) (B.stripFinset_cycle r.val.val)
  apply isCycleOn_eqOn hs
  intro a ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp ha
  exact (next_freshStrip A q B r b ((B.mem_stripFinset _ _).mp hb)).trans
    (base_band_next A q B b).symm
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft

namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
variable {α ι : Type}
lemma attachedCircleOn_contact_subset (s : Finset α) (x : ι → α) (t : ι → Finset α)
    (is : List ι) {j : ι} (hj : j∈is) (hx : x j∈s) :
    t j⊆attachedCircleOn s x t is := by
  induction is generalizing s with
  | nil => cases hj
  | cons i is ih =>
    rcases List.mem_cons.mp hj with rfl|hj
    · simp only [attachedCircleOn,ite_eq_left hx]
      exact Finset.Subset.trans Finset.subset_union_right (attachedCircleOn_subset _ _ _ _)
    · apply ih _ hj
      split_ifs
      · exact Finset.mem_union_left _ hx
      · exact hx
end IntegralCharacterVarieties.BoundarySurgery
namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical
open VertexTable BoundarySurgery
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
lemma shortChildAt_surjective : Function.Surjective (shortChildAt A q B) := by
  intro c
  cases c with
  | inl c =>
    refine ⟨⟨(finCongr ((cutPort_arity A q B).trans (input_arity A q B).symm)).symm
      ((B.kind 0).childEnumeration (B.kind 0).input c),false⟩,?_⟩
    simp only [shortChildAt,Equiv.apply_symm_apply,Equiv.symm_apply_apply]
  | inr c =>
    refine ⟨⟨(finCongr ((cutPort_arity A q B).trans (output_arity A q B).symm)).symm
      ((B.kind (Fin.last B.length)).childEnumeration (B.kind (Fin.last B.length)).output c),true⟩,?_⟩
    simp only [shortChildAt,Equiv.apply_symm_apply,Equiv.symm_apply_apply]
lemma mem_contacts (j) : j∈contacts A q B := by
  rcases j with ⟨i,b⟩
  cases b <;> simp [contacts,PortWiring.tripleContacts]

/-- Exhaustion is on literal sides of the actual graft wiring. In particular,
an untouched strip is assigned its connected root, not a colour-label guess. -/
theorem literal_germ_exhaustion (a : Side (base A q B).Seam (base A q B).seamArity) :
    (∃ x : Side S arity,a=oldEmbedding A q B x) ∨
    (∃ v,a=bandEmbedding A q B (B.origPrincipal v)) ∨
    (∃ v,a=bandEmbedding A q B (B.mirrorPrincipal v)) ∨
    (∃ j,a∈shortCycle A q B j) ∨
    (∃ r : B.FreshStrip,a∈(B.stripFinset r.val.val).map (bandEmbedding A q B)) := by
  obtain ⟨c,rfl⟩ := (A.toWiring.sumSides B.doubleWiring).surjective a
  cases c with
  | inl c =>
    obtain ⟨x,rfl⟩ := A.wiringSides.surjective c
    exact Or.inl ⟨x,rfl⟩
  | inr c =>
    rcases B.double_side_exhaustive c with ⟨v,rfl⟩|⟨v,rfl⟩|⟨x,hx⟩
    · exact Or.inr (Or.inl ⟨v,rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨v,rfl⟩))
    · let r : B.StripRoot := ⟨B.stripForest.root x,B.stripForest.root_external x⟩
      have hc : c∈B.stripCycle r.val := by
        rcases hx with rfl|rfl
        · exact B.stripCycle_mem_orig x
        · exact B.stripCycle_mem_mirror x
      by_cases hr : ∃ z,B.shortRoot z=r
      · obtain ⟨z,hz⟩ := hr
        obtain ⟨j,rfl⟩ := shortChildAt_surjective A q B z
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
        refine ⟨j,Finset.mem_map.mpr ⟨c,?_,rfl⟩⟩
        rw [hz]
        exact (B.mem_stripFinset _ _).mpr hc
      · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        exact ⟨⟨r,hr⟩,Finset.mem_map.mpr ⟨c,(B.mem_stripFinset _ _).mpr hc,rfl⟩⟩

lemma shortCycle_in_secondary (s : Finset (Side S arity)) (j)
    (hj : (⟨q,some (finCongr (cutPort_arity A q B) j.1)⟩ : Side S arity)∈s) :
    shortCycle A q B j⊆secondaryCircle A q B s := by
  apply attachedCircleOn_contact_subset _ _ _ _ (mem_contacts A q B j)
  rw [oldContact_eq]
  exact Finset.mem_map.mpr ⟨_,hj,rfl⟩
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft

namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
open Equiv Equiv.Perm
variable {α : Type} (N : Equiv.Perm α) {n : ℕ} (e : Fin (n+1) → α)
    (he : ∀ i,N (e i)=e (finRotate (n+1) i))
include he in
lemma pow_cycleEntry (k : ℕ) (hk : k<n+1) :
    (N^k) (e 0)=e ⟨k,hk⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',mul_apply,ih (by omega),he,finRotate_of_lt (by omega)]

include he in
lemma isCycleOn_range : N.IsCycleOn (Set.range e) := by
  refine ⟨⟨?_,N.injective.injOn,?_⟩,?_⟩
  · rintro _ ⟨i,rfl⟩
    exact ⟨_,(he i).symm⟩
  · rintro _ ⟨i,rfl⟩
    exact ⟨e ((finRotate (n+1)).symm i),⟨_,rfl⟩,by rw [he,Equiv.apply_symm_apply]⟩
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    have hi : N.SameCycle (e 0) (e i) := ⟨(i.val : ℤ),by simpa using pow_cycleEntry N e he i.val i.isLt⟩
    have hj : N.SameCycle (e 0) (e j) := ⟨(j.val : ℤ),by simpa using pow_cycleEntry N e he j.val j.isLt⟩
    exact hi.symm.trans hj
end IntegralCharacterVarieties.BoundarySurgery
namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical
open VertexTable
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))

/-- Actual positive traversal of the new principal circle of the graft. -/
noncomputable def mirrorEntry (i : Fin (B.length+1)) := mirrorSide A q B i.rev

lemma mirrorEntry_next (i : Fin (B.length+1)) :
    next A q B (mirrorEntry A q B i)=mirrorEntry A q B (finRotate (B.length+1) i) := by
  unfold mirrorEntry
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.rev_last,finRotate_last,Fin.rev_zero,next_mirror_zero]
  · rw [Fin.rev_castSucc,next_mirror]
    have hr : finRotate (B.length+1) j.castSucc=j.succ := finRotate_of_lt j.isLt
    rw [hr,Fin.rev_succ]

lemma mirrorEntry_injective : Function.Injective (mirrorEntry A q B) := by
  intro i j h
  have hv := congrArg (fun a : Side (wiring A q B).Seam (wiring A q B).seamArity => a.1.val.1) h
  change Sum.inr (Sum.inr i.rev)=Sum.inr (Sum.inr j.rev) at hv
  exact Fin.rev_injective (Sum.inr.inj (Sum.inr.inj hv))

/-- The literal mirror sides form exactly one boundary orbit. No independent
cyclic template, no parent germ exhaustion assumption. -/
lemma mirror_isCycle : (next A q B).IsCycleOn (Set.range (mirrorEntry A q B)) :=
  BoundarySurgery.isCycleOn_range (next A q B) (mirrorEntry A q B) (mirrorEntry_next A q B)
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft

namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
open Equiv Equiv.Perm
variable {α β : Type} {G : Type*} [Group G]
    (N : Equiv.Perm α) (Z : Equiv.Perm β) (s : Finset α) (q : α)
    (hs : N.IsCycleOn (s : Set α)) (hq : q∈s)
    (f : α → β) {k : ℕ} (c : Fin (k+1) → β)
    (hold : ∀ a∈s,Z (f a)=if N a=q then c 0 else f (N a))
    (hstep : ∀ j : Fin k,Z (c j.castSucc)=c j.succ)
    (hlast : Z (c (Fin.last k))=f q)
include hs hq hold in
lemma chain_pow_old (j : ℕ) (hj : j<s.card) : (Z^j) (f q)=f ((N^j) q) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ',mul_apply,ih (by omega),hold ((N^j) q) (hs.1.mapsTo.iterate j hq)]
    have hne : N ((N^j) q)≠q := by
      rw [←mul_apply,←pow_succ']
      intro he
      have hd := (hs.pow_apply_eq hq).mp he
      exact (Nat.le_of_dvd (by omega) hd).not_gt hj
    rw [ite_eq_right hne,pow_succ',mul_apply]

include hs hq hold in
lemma chain_pow_old_card : (Z^s.card) (f q)=c 0 := by
  have hp : 0<s.card := Finset.card_pos.mpr ⟨q,hq⟩
  have hn : s.card=s.card-1+1 := by omega
  rw [hn,pow_succ',mul_apply,chain_pow_old N Z s q hs hq f c hold _ (by omega),
    hold ((N^(s.card-1)) q) (hs.1.mapsTo.iterate (s.card-1) hq)]
  have hret : N ((N^(s.card-1)) q)=q := by
    rw [←mul_apply,←pow_succ',←hn]
    exact hs.pow_card_apply hq
  rw [ite_eq_left hret]

include hstep in
lemma chain_pow_new (j : ℕ) (hj : j<k+1) : (Z^j) (c 0)=c ⟨j,hj⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ',mul_apply,ih (by omega)]
    exact hstep ⟨j,by omega⟩

include hs hq hold hstep hlast in
lemma chain_pow_full : (Z^(s.card+(k+1))) (f q)=f q := by
  rw [Nat.add_comm s.card (k+1),pow_add,mul_apply,chain_pow_old_card N Z s q hs hq f c hold,
    pow_succ',mul_apply,chain_pow_new Z c hstep k (by omega)]
  exact hlast

include hs hq hold hstep hlast in
/-- Full circuit exhaustion for the inserted chain, not just a rank or Euler
characteristic count. -/
lemma chain_isCycle : Z.IsCycleOn (f '' (s : Set α) ∪ Set.range c) := by
  have holdcycle : ∀ a∈s,Z.SameCycle (f q) (f a) := by
    intro a ha
    obtain ⟨j,hj,rfl⟩ := hs.exists_pow_eq hq ha
    exact ⟨(j : ℤ),by simpa using chain_pow_old N Z s q hs hq f c hold j hj⟩
  have hnewcycle : ∀ i,Z.SameCycle (f q) (c i) := by
    intro i
    refine ⟨((i.val+s.card : ℕ) : ℤ),?_⟩
    rw [zpow_natCast,pow_add,mul_apply,chain_pow_old_card N Z s q hs hq f c hold]
    exact chain_pow_new Z c hstep i.val i.isLt
  refine ⟨⟨?_,Z.injective.injOn,?_⟩,?_⟩
  · rintro b (⟨a,ha,rfl⟩|⟨i,rfl⟩)
    · rw [hold a ha]
      split_ifs
      · exact Or.inr ⟨_,rfl⟩
      · exact Or.inl ⟨_,hs.1.mapsTo ha,rfl⟩
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [hlast]
        exact Or.inl ⟨_,hq,rfl⟩
      · rw [hstep]
        exact Or.inr ⟨_,rfl⟩
  · rintro b (⟨a,ha,rfl⟩|⟨i,rfl⟩)
    · by_cases he : a=q
      · subst a
        exact ⟨c (Fin.last k),Or.inr ⟨_,rfl⟩,hlast⟩
      · have hm : N.symm a∈s := (hs.apply_mem_iff).mp (by simpa using ha)
        refine ⟨f (N.symm a),Or.inl ⟨_,hm,rfl⟩,?_⟩
        rw [hold _ hm,Equiv.apply_symm_apply,ite_eq_right he]
    · refine Fin.cases ?_ (fun j => ?_) i
      · have hm : N.symm q∈s := (hs.apply_mem_iff).mp (by simpa using hq)
        refine ⟨f (N.symm q),Or.inl ⟨_,hm,rfl⟩,?_⟩
        rw [hold _ hm,Equiv.apply_symm_apply,ite_eq_left rfl]
      · exact ⟨c j.castSucc,Or.inr ⟨_,rfl⟩,hstep j⟩
  · intro a ha b hb
    have hca : Z.SameCycle (f q) a := by
      rcases ha with ⟨a,ha,rfl⟩|⟨i,rfl⟩
      · exact holdcycle a ha
      · exact hnewcycle i
    have hcb : Z.SameCycle (f q) b := by
      rcases hb with ⟨b,hb,rfl⟩|⟨i,rfl⟩
      · exact holdcycle b hb
      · exact hnewcycle i
    exact hca.symm.trans hcb

include hs hq hold in
lemma chain_word_old (u : β → G) :
    cycleWord Z u (f q) s.card=cycleWord N (u ∘ f) q s.card := by
  unfold cycleWord
  congr 2
  apply List.map_congr_left
  intro i hi
  rw [chain_pow_old N Z s q hs hq f c hold i (List.mem_range.mp hi)]
  rfl

include hstep in
lemma chain_word_new (u : β → G) :
    cycleWord Z u (c 0) (k+1)=(List.ofFn (fun i => u (c i))).reverse.prod := by
  have hl : (List.range (k+1)).map (fun i => u ((Z^i) (c 0)))=List.ofFn (fun i => u (c i)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
      exact congrArg u (chain_pow_new Z c hstep i (by simpa using hi'))
  unfold cycleWord
  rw [hl]

include hs hq hold hstep in
/-- Exact NONCOMMUTATIVE monodromy for inserting a new literal band side into
an old boundary circuit. Old coefficients and starting occurrence are retained. -/
lemma chain_cycleWord (u : β → G) :
    cycleWord Z u (f q) (s.card+(k+1))=
      (List.ofFn (fun i => u (c i))).reverse.prod*cycleWord N (u ∘ f) q s.card := by
  rw [cycleWord_add,chain_pow_old_card N Z s q hs hq f c hold,
    chain_word_new Z c hstep,chain_word_old N Z s q hs hq f c hold]

include hs hq hold hstep in
lemma chain_cycleWord_identity (u : β → G) (hu : ∀ i,u (c i)=1) :
    cycleWord Z u (f q) (s.card+(k+1))=cycleWord N (u ∘ f) q s.card := by
  rw [chain_cycleWord N Z s q hs hq f c hold hstep u]
  have hh : (List.ofFn (fun i => u (c i))).reverse.prod=1 := by simp only [hu]; simp
  rw [hh,one_mul]
end IntegralCharacterVarieties.BoundarySurgery

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical
open VertexTable Equiv Equiv.Perm
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
    (s : Finset (Side S arity))
    (hs : A.vertexAssembly.corners.boundaryNext.IsCycleOn (s : Set (Side S arity)))
    (hq : (⟨q,none⟩ : Side S arity)∈s)
    (hno : ∀ z i,A.facet ⟨z,some i⟩≠A.facet ⟨q,none⟩)

include hs hq hno in
lemma oldPrincipal_parent (a : Side S arity) (ha : a∈s) : a.2=none := by
  have hf (j : ℕ) : A.facet ((A.vertexAssembly.corners.boundaryNext^j) ⟨q,none⟩)=A.facet ⟨q,none⟩ := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ',mul_apply]
      change A.vertexAssembly.corners.facet _=A.facet ⟨q,none⟩
      rw [A.vertexAssembly.corners.boundaryNext_facet]
      exact ih
  obtain ⟨j,hj,he⟩ := hs.exists_pow_eq hq ha
  have hc : A.facet a=A.facet ⟨q,none⟩ := he ▸ hf j
  rcases a with ⟨z,c⟩
  cases c with
  | none => rfl
  | some i => exact False.elim (hno z i hc)

include hs hq hno in
lemma next_oldPrincipal (a : Side S arity) (ha : a∈s) :
    next A q B (oldSide A q B a.1)=
      if A.vertexAssembly.corners.boundaryNext a=⟨q,none⟩ then originalSide A q B 0
      else oldSide A q B (A.vertexAssembly.corners.boundaryNext a).1 := by
  have ha0 := oldPrincipal_parent A q s hs hq hno a ha
  have hb0 := oldPrincipal_parent A q s hs hq hno (A.vertexAssembly.corners.boundaryNext a) (hs.1.mapsTo ha)
  rcases a with ⟨z,c⟩
  dsimp only at ha0
  subst c
  generalize hb : A.vertexAssembly.corners.boundaryNext (⟨z,none⟩ : Side S arity)=b at hb0 ⊢
  rcases b with ⟨w,c⟩
  dsimp only at hb0
  subst c
  by_cases he : w=q
  · subst w
    simpa only [ite_eq_left rfl,ite_true] using next_old_cut A q B z hb
  · have hn : (⟨w,none⟩ : Side S arity)≠⟨q,none⟩ := fun h => he (congrArg Sigma.fst h)
    simpa only [ite_eq_right hn] using next_old_not_cut A q B z w he hb

include hs hq hno in
/-- The selected actual old circuit acquires precisely the original band side;
all its old occurrences remain separate. The mirror circle is a different
literal orbit, proved separately by mirror_isCycle. -/
lemma principalChain_isCycle : (next A q B).IsCycleOn
    ((fun a : Side S arity => oldSide A q B a.1) '' (s : Set (Side S arity)) ∪
      Set.range (originalSide A q B)) := by
  classical
  apply BoundarySurgery.chain_isCycle A.vertexAssembly.corners.boundaryNext (next A q B) s
    ⟨q,none⟩ hs hq (fun a => oldSide A q B a.1)
    (c:=originalSide A q B)
  · intro a ha
    by_cases h : A.vertexAssembly.corners.boundaryNext a=⟨q,none⟩
    · simpa only [ite_eq_left h] using next_oldPrincipal A q B s hs hq hno a ha
    · simpa only [ite_eq_right h] using next_oldPrincipal A q B s hs hq hno a ha
  · exact next_original A q B
  · exact next_original_last A q B

include hs hq hno in
lemma principalChain_word {G : Type*} [Group G]
    (u : Side (wiring A q B).Seam (wiring A q B).seamArity → G)
    (hu : ∀ i,u (originalSide A q B i)=1) :
    BoundarySurgery.cycleWord (next A q B) u (oldSide A q B q) (s.card+(B.length+1))=
      BoundarySurgery.cycleWord A.vertexAssembly.corners.boundaryNext
        (fun a : Side S arity => u (oldSide A q B a.1)) ⟨q,none⟩ s.card := by
  classical
  apply BoundarySurgery.chain_cycleWord_identity A.vertexAssembly.corners.boundaryNext (next A q B) s
    ⟨q,none⟩ hs hq (fun a => oldSide A q B a.1) (originalSide A q B)
    (u:=u)
  · intro a ha
    by_cases h : A.vertexAssembly.corners.boundaryNext a=⟨q,none⟩
    · simpa only [ite_eq_left h] using next_oldPrincipal A q B s hs hq hno a ha
    · simpa only [ite_eq_right h] using next_oldPrincipal A q B s hs hq hno a ha
  · exact next_original A q B
  · exact hu
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
end

end OAI
