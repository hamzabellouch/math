import OAI.CategoryTheory.Thomason.Simplicial.FiniteRelativeRealizationLifting
import OAI.CategoryTheory.Thomason.Simplicial.KanBaseChangeExhaustion
import OAI.CategoryTheory.Thomason.Simplicial.SimplicialSpanFactorization
import OAI.CategoryTheory.Thomason.Simplicial.SkeletalWeakEquivalences
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionUnions
import OAI.CategoryTheory.Thomason.Transfer.HornAttachmentWeakEquivalences
import OAI.CategoryTheory.Thomason.Transfer.SimplicialRangeGluing
import OAI.CategoryTheory.Thomason.Transfer.ThomasonQuillenBridge

namespace OAI

section

/-! # Subdivision and extension preserve the Kan lifting classes

The explicit subdivided horn collapse proves preservation of Kan
lifting classes by subdivision and extension.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

noncomputable section

/-- Extension preserves the right lifting property against all actual horns. -/
theorem extension_kan_rlp {X Y : SSet.{0}} (p : X ⟶ Y) (hp : J.rlp p) :
    J.rlp (SSet.ex.map p) := by
  intro A B i hi
  simp only [J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  apply (SSet.sdExAdjunction.hasLiftingProperty_iff _ _).mp
  exact subdivision_horn_anodyne n k p hp

instance extension_fibration {X Y : SSet.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration p] : HomotopicalAlgebra.Fibration (SSet.ex.map p) := by
  apply (fibration_iff _).mpr
  exact extension_kan_rlp p ((fibration_iff p).mp inferInstance)

/-- In particular, extension of an actual Kan complex is again Kan. -/
instance extension_kan (K : SSet.{0}) [SSet.KanComplex K] :
    SSet.KanComplex (SSet.ex.obj K) := by
  apply (HomotopicalAlgebra.isFibrant_iff_of_isTerminal
    (SSet.ex.map (terminal.from K))
    (terminalIsTerminal.isTerminalObj SSet.ex)).mpr
  infer_instance

/-- Subdivision preserves the full horn-generated left lifting class. -/
theorem subdivision_anodyne {X Y : SSet.{0}} (f : X ⟶ Y)
    (hf : SSet.anodyneExtensions f) : SSet.anodyneExtensions (SSet.sd.map f) := by
  intro A B p hp
  apply (SSet.sdExAdjunction.hasLiftingProperty_iff _ _).mpr
  exact hf _ (extension_kan_rlp p hp)

end

end Thomason.Construction

end

section

/-! # Weak equivalences carried by the actual left adjoints in all dimensions

The model reduction and the proved finite-poset units suffice for this
compatibility theorem. The published Street-localization equivalence and
canonical-extension weak-equivalence hypotheses are not needed here.
-/

namespace Thomason.Construction

open CategoryTheory

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The constructed omega-dimensional left adjoint preserves every actual
Kan–Quillen weak equivalence, without using the localization conclusion. -/
theorem thomasonLeft_preserves_weakEquivalences
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0}) (transfer : PublishedThomasonReduction h)
    {X Y : SSet.{0}} (f : X ⟶ Y) (hf : realizationWeakEquivalences f) :
    h.streetWeakEquivalences (h.thomasonLeft.map f) :=
  ThomasonAdjunction.left_preserves_weakEquivalences h.thomasonAdjunction kq
    (h.conditional_model_axioms G (SimplexComplex.alexanderWhitneyInput h) s g kq
      (h.finitePosetUnitInput G t (SimplexComplex.alexanderWhitneyInput h) s g kq) transfer)
    f hf

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable {n : ℕ} (r : FiniteReflectionInput n)
  (h : NormalizedSimplexIdentities) [StrictColimitsInput]

/-- The same weak-equivalence bridge for each positive finite dimension. -/
theorem thomasonLeft_preserves_weakEquivalences
    (G : RightGrayInput h) (t : GrayTruncationInput G)
    (s : PublishedPosetSieveInput h) (g : PublishedSimplicialGluingInput)
    (kq : KanQuillenPublishedInput.{0}) (transfer : PublishedThomasonReduction h)
    {X Y : SSet.{0}} (f : X ⟶ Y) (hf : realizationWeakEquivalences f) :
    realizationWeakEquivalences ((h.finiteStreetNerve (n+1)).map
      ((r.thomasonLeft h).map f)) :=
  ThomasonAdjunction.left_preserves_weakEquivalences (r.thomasonAdjunction h) kq
    (r.conditional_model_axioms h G t (SimplexComplex.alexanderWhitneyInput h) s g kq
      (h.finitePosetUnitInput G t (SimplexComplex.alexanderWhitneyInput h) s g kq) transfer)
    f hf

end FiniteReflectionInput
end Thomason.Construction

end

section

/-! # Simplicial gluing from geometric deformation and boundary factorization

All weak-equivalence assertions use the actual realization. The construction
uses the proved algebraic boundary WFS and the constructed strong deformations,
without a Kan–Quillen model structure or the acyclic-Kan implication.
-/

namespace Thomason.Construction.SimplicialSpan

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

private theorem boundary_right_pair {X Y : SSet.{0}} (f : X ⟶ Y) (hf : I.rlp f) :
    (J.rlp ⊓ realizationWeakEquivalences) f := by
  have hm : (MorphismProperty.monomorphisms SSet.{0}).rlp f := by
    rwa [SSet.rlp_monomorphisms]
  exact ⟨MorphismProperty.antitone_rlp J_le_monomorphisms f hm, boundary_rlp_weak f hf⟩

noncomputable def factorPrefixUnconditional {X Y : Diagram} (f : X ⟶ Y) :
    Prefix f := by
  let T := I.rlp
  have := boundary_weakFactorizationSystem
  let c := MorphismProperty.factorizationData (MorphismProperty.monomorphisms SSet.{0}) T f.c
  let u : X.A ⟶ pullback Y.right c.p := pullback.lift f.a (X.right ≫ c.i) (by
    rw [Category.assoc, c.fac]
    exact f.right_w.symm)
  let a := MorphismProperty.factorizationData (MorphismProperty.monomorphisms SSet.{0}) T u
  refine
    { A := a.Z
      C := c.Z
      right := a.p ≫ pullback.snd Y.right c.p
      iA := a.i
      iC := c.i
      pA := a.p ≫ pullback.fst Y.right c.p
      pC := c.p
      i_right := ?_
      p_right := ?_
      facA := ?_
      facC := c.fac
      hiA := a.hi
      hiC := c.hi
      hpA := ?_
      hpC := boundary_right_pair _ c.hp }
  · rw [← Category.assoc, a.fac]
    exact (pullback.lift_snd _ _ _).symm
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  · rw [← Category.assoc, a.fac]
    exact pullback.lift_fst _ _ _
  · exact boundary_right_pair _ (T.comp_mem _ _ a.hp (T.pullback_fst Y.right c.p c.hp))


noncomputable def factorizationUnconditional {X Y : Diagram} (f : X ⟶ Y) : Factorization f := by
  have := boundary_weakFactorizationSystem
  let q := factorPrefixUnconditional f
  let u : Limits.pushout X.left q.iA ⟶ Y.B :=
    Limits.pushout.desc f.b (q.pA ≫ Y.left) (by
      rw [← Category.assoc, q.facA, f.left_w])
  let b := MorphismProperty.factorizationData
    (MorphismProperty.monomorphisms SSet.{0})
    I.rlp u
  let Z : Diagram := ⟨q.A, b.Z, q.C,
    Limits.pushout.inr X.left q.iA ≫ b.i, q.right⟩
  let i : X ⟶ Z :=
    ⟨q.iA, Limits.pushout.inl X.left q.iA ≫ b.i, q.iC,
      by dsimp [Z]; rw [← Category.assoc, Limits.pushout.condition, Category.assoc],
      q.i_right⟩
  let p : Z ⟶ Y :=
    ⟨q.pA, b.p, q.pC,
      by dsimp [Z]; rw [Category.assoc, b.fac]; exact Limits.pushout.inr_desc _ _ _,
      q.p_right⟩
  refine ⟨Z, i, p, ?_, ⟨q.hiA, q.hiC, ?_⟩, q.hpA, boundary_right_pair _ b.hp, q.hpC⟩
  · apply Hom.ext
    · exact q.facA
    · change (Limits.pushout.inl X.left q.iA ≫ b.i) ≫ b.p = f.b
      rw [Category.assoc, b.fac]
      exact Limits.pushout.inl_desc _ _ _
    · exact q.facC
  · have he : relativeB i = b.i := by
      apply Limits.pushout.hom_ext
      · exact Limits.pushout.inl_desc _ _ _
      · exact Limits.pushout.inr_desc _ _ _
    rw [he]
    exact b.hi


theorem Cofibration.compUnconditional {X Y Z : Diagram} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Cofibration f) (hg : Cofibration g) :
    Cofibration (f ≫ g) := by
  let M := MorphismProperty.monomorphisms SSet.{0}
  have := hf.monoA
  have := hf.monoC
  have := hg.monoA
  have := hg.monoC
  refine ⟨?_, ?_, ?_⟩
  · change Mono (f.a ≫ g.a)
    infer_instance
  · change Mono (f.c ≫ g.c)
    infer_instance
  · let X' : Diagram := ⟨X.A, X.B, Z.A, X.left, f.a ≫ g.a⟩
    let Y' : Diagram := ⟨Y.A, Y.B, Z.A, Y.left, g.a⟩
    let d : X' ⟶ Y' := ⟨f.a, f.b, 𝟙 _, f.left_w, by simp [X', Y']⟩
    have hm : Mono (fromMiddle d) :=
      M.of_isPushout (fromMiddle_isPushout d).flip hf.monoRelative
    have he : relativeB (f ≫ g) = fromMiddle d ≫ relativeB g := by
      change relativeB (Hom.comp f g) = _
      dsimp only [relativeB, Hom.comp, fromMiddle, d, X', Y']
      apply Limits.pushout.hom_ext <;> simp only [Category.assoc,
        Limits.pushout.inl_desc, Limits.pushout.inr_desc,
        Limits.pushout.inl_desc_assoc, Limits.pushout.inr_desc_assoc]
    rw [he]
    have := hg.monoRelative
    exact @mono_comp _ _ _ _ _ (fromMiddle d) hm (relativeB g) hg.monoRelative


theorem inl_cofibrationUnconditional (X Y : Diagram) [Mono Y.left] : Cofibration (inl X Y) := by
  let M := MorphismProperty.monomorphisms SSet.{0}
  refine ⟨?_, ?_, ?_⟩
  · exact M.of_isPushout (IsPushout.of_hasBinaryCoproduct' X.A Y.A) (by infer_instance)
  · exact M.of_isPushout (IsPushout.of_hasBinaryCoproduct' X.C Y.C) (by infer_instance)
  · exact M.of_isPushout (inl_relative_isPushout X Y).flip (by infer_instance)

theorem inr_cofibrationUnconditional (X Y : Diagram) [Mono X.left] : Cofibration (inr X Y) := by
  let M := MorphismProperty.monomorphisms SSet.{0}
  refine ⟨?_, ?_, ?_⟩
  · exact M.of_isPushout (IsPushout.of_hasBinaryCoproduct' X.A Y.A).flip (by infer_instance)
  · exact M.of_isPushout (IsPushout.of_hasBinaryCoproduct' X.C Y.C).flip (by infer_instance)
  · exact M.of_isPushout (inr_relative_isPushout X Y).flip (by infer_instance)


theorem relativeB_weakUnconditional {X Y : Diagram} (f : X ⟶ Y)
    (hi : Cofibration f)
    (ha : realizationWeakEquivalences f.a) (hb : realizationWeakEquivalences f.b) :
    realizationWeakEquivalences (relativeB f) := by
  let T := MorphismProperty.monomorphisms SSet.{0} ⊓ realizationWeakEquivalences
  have hleg := T.pushout_inl X.left f.a ⟨hi.monoA, ha⟩
  apply realizationWeakEquivalences.of_precomp (Limits.pushout.inl X.left f.a) _ hleg.2
  simpa using hb

/-- A span cofibration which is weak at each object induces a weak equivalence
of the actual simplicial pushouts. This derives the comparison from geometric deformation. -/
theorem pushoutMap_weak_of_cofibrationUnconditional {X Y : Diagram} (f : X ⟶ Y)
    (hi : Cofibration f)
    (ha : realizationWeakEquivalences f.a) (hb : realizationWeakEquivalences f.b)
    (hc : realizationWeakEquivalences f.c) : realizationWeakEquivalences (pushoutMap f) := by
  let T := MorphismProperty.monomorphisms SSet.{0} ⊓ realizationWeakEquivalences
  have hu := T.of_isPushout (toMiddle_isPushout f) ⟨hi.monoC, hc⟩
  have hv := T.of_isPushout (fromMiddle_isPushout f).flip
    ⟨hi.monoRelative, relativeB_weakUnconditional f hi ha hb⟩
  rw [← toMiddle_fromMiddle f]
  exact realizationWeakEquivalences.comp_mem _ _ hu.2 hv.2


theorem ObjectwiseWeak.of_comp_unconditional {X Y Z : Diagram} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : ObjectwiseWeak g) (hfg : ObjectwiseWeak (f ≫ g)) : ObjectwiseWeak f :=
  ⟨realizationWeakEquivalences.of_postcomp f.a g.a hg.1 hfg.1,
    realizationWeakEquivalences.of_postcomp f.b g.b hg.2.1 hfg.2.1,
    realizationWeakEquivalences.of_postcomp f.c g.c hg.2.2 hfg.2.2⟩

theorem pushoutMap_weakUnconditional {X Y : Diagram} (f : X ⟶ Y)
    [Mono X.left] [Mono Y.left]
    (hf : ObjectwiseWeak f) : realizationWeakEquivalences (pushoutMap f) := by
  let q := factorizationUnconditional (desc f (𝟙 Y))
  let i : X ⟶ q.Z := inl X Y ≫ q.i
  let s : Y ⟶ q.Z := inr X Y ≫ q.i
  have hip : i ≫ q.p = f := by
    dsimp [i]
    rw [Category.assoc, q.fac, inl_desc]
  have hsp : s ≫ q.p = 𝟙 Y := by
    dsimp [s]
    rw [Category.assoc, q.fac, inr_desc]
  have hp : ObjectwiseWeak q.p := ⟨q.hpA.2, q.hpB.2, q.hpC.2⟩
  have hiw : ObjectwiseWeak i := ObjectwiseWeak.of_comp_unconditional i q.p hp (by rw [hip]; exact hf)
  have hsw : ObjectwiseWeak s := ObjectwiseWeak.of_comp_unconditional s q.p hp (by
    rw [hsp]
    exact ⟨realizationWeakEquivalences.id_mem _, realizationWeakEquivalences.id_mem _,
      realizationWeakEquivalences.id_mem _⟩)
  have hi : Cofibration i := (inl_cofibrationUnconditional X Y).compUnconditional q.hi
  have hs : Cofibration s := (inr_cofibrationUnconditional X Y).compUnconditional q.hi
  have hi' := pushoutMap_weak_of_cofibrationUnconditional i hi hiw.1 hiw.2.1 hiw.2.2
  have hs' := pushoutMap_weak_of_cofibrationUnconditional s hs hsw.1 hsw.2.1 hsw.2.2
  have hsp' : pushoutMap s ≫ pushoutMap q.p = 𝟙 (pushout Y) := by
    change pushoutFunctor.map s ≫ pushoutFunctor.map q.p = _
    rw [← pushoutFunctor.map_comp, hsp, pushoutFunctor.map_id]
    rfl
  have hp' : realizationWeakEquivalences (pushoutMap q.p) := by
    apply realizationWeakEquivalences.of_precomp (pushoutMap s) _ hs'
    rw [hsp']
    exact realizationWeakEquivalences.id_mem _
  have hip' : pushoutMap i ≫ pushoutMap q.p = pushoutMap f := by
    change pushoutFunctor.map i ≫ pushoutFunctor.map q.p = pushoutFunctor.map f
    rw [← pushoutFunctor.map_comp, hip]
  rw [← hip']
  exact realizationWeakEquivalences.comp_mem _ _ hi' hp'


end Thomason.Construction.SimplicialSpan

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

theorem constructedSimplicialGluingUnconditional :
    PublishedSimplicialGluingInput where
  glue {A B C P A' B' C' P'} {i j b c i' j' b' c'} hp hp' _ _
      fA fB fC fP hi hj hb hc hA hB hC := by
    let X : SimplicialSpan.Diagram := ⟨A, B, C, i, j⟩
    let Y : SimplicialSpan.Diagram := ⟨A', B', C', i', j'⟩
    let f : X ⟶ Y := ⟨fA, fB, fC, hi, hj⟩
    have hw := SimplicialSpan.pushoutMap_weakUnconditional f ⟨hA, hB, hC⟩
    have hiso (U V : SSet.{0}) (e : U ≅ V) : realizationWeakEquivalences e.hom := by
      exact realizationWeakEquivalences.of_isIso _
    rw [← SimplicialSpan.pushoutMap_fac hp hp' f fP hb hc]
    exact realizationWeakEquivalences.comp_mem _ _ (hiso _ _ hp.isoPushout)
      (realizationWeakEquivalences.comp_mem _ _ hw (hiso _ _ hp'.isoPushout.symm))


end Thomason.Construction

end

section

/-! # Gluing the face-poset comparison along lower sets

Both squares are actual simplicial pushouts: the source is the nerve of
a union of lower sets, and the target is the union of the corresponding
subcomplexes of the original nonsingular simplicial set.
-/

namespace Thomason.Construction.NonsingularLastVertex

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {X : SSet.{0}}

instance faceSubset_nerve_mono {S T : Set X.N} (h : S ⊆ T) :
    Mono (nerveMap (faceSubset h).monotone.functor) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro s t he
  apply nerve.ext_of_isThin
  funext i
  apply Subtype.ext
  exact congrArg (fun z => (z.obj i).val) he

theorem faceSubset_range {S T : Set X.N} (h : S ⊆ T) :
    SSet.Subcomplex.range (nerveMap (faceSubset h).monotone.functor) =
      fullSubposetComplex {t : T | t.val ∈ S} := by
  ext d s
  constructor
  · rintro ⟨t, rfl⟩ i
    exact (t.obj i).property
  · intro hs
    let t : (nerve S).obj d := {
      obj i := ⟨(s.obj i).val, hs i⟩
      map f := homOfLE (leOfHom (s.map f)) }
    exact ⟨t, nerve.ext_of_isThin rfl⟩

theorem source_union_isPushout (S T : Set X.N)
    (hS : IsLowerSet S) (hT : IsLowerSet T) :
    IsPushout
      (nerveMap (faceSubset (Set.inter_subset_left : S ∩ T ⊆ S)).monotone.functor)
      (nerveMap (faceSubset (Set.inter_subset_right : S ∩ T ⊆ T)).monotone.functor)
      (nerveMap (faceSubset (Set.subset_union_left : S ⊆ S ∪ T)).monotone.functor)
      (nerveMap (faceSubset (Set.subset_union_right : T ⊆ S ∪ T)).monotone.functor) := by
  let hi : S ∩ T ⊆ S ∪ T := Set.inter_subset_left.trans Set.subset_union_left
  have eS : nerveMap (faceSubset (Set.inter_subset_left : S ∩ T ⊆ S)).monotone.functor ≫
      nerveMap (faceSubset (Set.subset_union_left : S ⊆ S ∪ T)).monotone.functor =
        nerveMap (faceSubset hi).monotone.functor := by
    rw [← orderNerveMap_comp]
    rfl
  have eT : nerveMap (faceSubset (Set.inter_subset_right : S ∩ T ⊆ T)).monotone.functor ≫
      nerveMap (faceSubset (Set.subset_union_right : T ⊆ S ∪ T)).monotone.functor =
        nerveMap (faceSubset hi).monotone.functor := by
    rw [← orderNerveMap_comp]
    rfl
  have : Mono (nerveMap (faceSubset (Set.inter_subset_left : S ∩ T ⊆ S)).monotone.functor ≫
      nerveMap (faceSubset (Set.subset_union_left : S ⊆ S ∪ T)).monotone.functor) := by
    rw [eS]
    infer_instance
  apply simplicial_isPushout_of_ranges _ _ _ _ (eS.trans eT.symm)
  · rw [faceSubset_range, faceSubset_range]
    apply sieve_nerve_cover
    · intro y x hxy hy
      exact hS hxy hy
    · intro y x hxy hy
      exact hT hxy hy
    · intro x
      exact x.property
  · rw [eS, faceSubset_range, faceSubset_range, faceSubset_range]
    exact fullSubposetComplex_inter {u : ↥(S ∪ T) | u.val ∈ S}
      {u : ↥(S ∪ T) | u.val ∈ T}

variable [X.Nonsingular]

/-- Three weak face comparisons glue to the union comparison. -/
theorem restrictedMap_weak_union (S T : Set X.N)
    (hS : IsLowerSet S) (hT : IsLowerSet T)
    (wS : realizationWeakEquivalences (restrictedMap S))
    (wT : realizationWeakEquivalences (restrictedMap T))
    (wI : realizationWeakEquivalences (restrictedMap (S ∩ T))) :
    realizationWeakEquivalences (restrictedMap (S ∪ T)) := by
  have sq : SSet.Subcomplex.BicartSq (faceUnion (S ∩ T))
      (faceUnion S) (faceUnion T) (faceUnion (S ∪ T)) :=
    ⟨(faceUnion_union S T).symm, (faceUnion_inter S T hS hT).symm⟩
  exact constructedSimplicialGluingUnconditional.glue
    (source_union_isPushout S T hS hT) sq.isPushout
    (restrictedMap (S ∩ T)) (restrictedMap S) (restrictedMap T) (restrictedMap (S ∪ T))
    (restrictedMap_naturality Set.inter_subset_left)
    (restrictedMap_naturality Set.inter_subset_right)
    (restrictedMap_naturality Set.subset_union_left)
    (restrictedMap_naturality Set.subset_union_right) wI wS wT

end

end Thomason.Construction.NonsingularLastVertex

end

end OAI
