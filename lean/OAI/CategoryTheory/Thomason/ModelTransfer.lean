import Mathlib
import OAI.CategoryTheory.Thomason.KanQuillen

namespace OAI

/-! Model Transfer. -/

noncomputable section
universe u v w z


namespace Thomason.SimplicialGluing
open CategoryTheory Limits MorphismProperty

lemma under_weak {C A B D P Q : SSet.{u}} (k : C ⟶ A) (i : C ⟶ B) (i' : C ⟶ D)
    [Mono i] [Mono i'] (f : B ⟶ D) (hf : simplicialWeakEquivalences f)
    (hif : i ≫ f = i') {a : A ⟶ P} {b : B ⟶ P} {a' : A ⟶ Q} {b' : D ⟶ Q}
    (s : IsPushout k i a b) (s' : IsPushout k i' a' b')
    (F : P ⟶ Q) (ha : a ≫ F = a') (hb : b ≫ F = f ≫ b') :
    simplicialWeakEquivalences F := by
  let E := pushout i i'
  let eB : B ⟶ E := pushout.inl i i'
  let eD : D ⟶ E := pushout.inr i i'
  let e : E ⟶ D := pushout.desc f (𝟙 D) (by simpa using hif)
  let := KanQuillen.boundary_weakFactorization.{u}
  let d := factorizationData (monomorphisms SSet) SSet.modelCategoryQuillen.I.rlp e
  have : Mono d.i := d.hi
  have hwp : simplicialWeakEquivalences d.p := KanQuillen.boundary_right_weak _ d.hp
  have : Mono eB := MorphismProperty.of_isPushout (IsPushout.of_hasPushout i i')
    (show (monomorphisms SSet) i' from inferInstance)
  have : Mono eD := MorphismProperty.of_isPushout (IsPushout.of_hasPushout i i').flip
    (show (monomorphisms SSet) i from inferInstance)
  let u : B ⟶ d.Z := eB ≫ d.i
  let v : D ⟶ d.Z := eD ≫ d.i
  have hup : u ≫ d.p = f := by
    rw [show u = eB ≫ d.i from rfl, Category.assoc, d.fac]
    exact pushout.inl_desc _ _ _
  have hvp : v ≫ d.p = 𝟙 D := by
    rw [show v = eD ≫ d.i from rfl, Category.assoc, d.fac]
    exact pushout.inr_desc _ _ _
  have hu : SSet.anodyneExtensions u := by
    rw [KanQuillen.anodyne_class]
    exact ⟨show Mono u from inferInstance, simplicialWeakEquivalences.of_postcomp u d.p hwp (hup ▸ hf)⟩
  have hv : SSet.anodyneExtensions v := by
    rw [KanQuillen.anodyne_class]
    exact ⟨show Mono v from inferInstance, simplicialWeakEquivalences.of_postcomp v d.p hwp
      (hvp ▸ simplicialWeakEquivalences.id_mem D)⟩
  let h := i ≫ u
  have hh : h = i' ≫ v := by
    dsimp [h,u,v,eB,eD]
    rw [← Category.assoc, pushout.condition, Category.assoc]
  let H := pushout k h
  let x : A ⟶ H := pushout.inl k h
  let z : d.Z ⟶ H := pushout.inr k h
  have sh : IsPushout k h x z := IsPushout.of_hasPushout k h
  let U : P ⟶ H := s.desc x (u ≫ z) (by
    rw [← Category.assoc]; exact sh.w)
  let V : Q ⟶ H := s'.desc x (v ≫ z) (by
    rw [← Category.assoc, ← hh]; exact sh.w)
  have hUa : a ≫ U = x := s.inl_desc _ _ _
  have hUb : b ≫ U = u ≫ z := s.inr_desc _ _ _
  have hVa : a' ≫ V = x := s'.inl_desc _ _ _
  have hVb : b' ≫ V = v ≫ z := s'.inr_desc _ _ _
  have su : IsPushout b u U z := by
    have st : IsPushout k (i ≫ u) (a ≫ U) z := by rw [hUa]; exact sh
    exact st.of_top hUb s
  have sv : IsPushout b' v V z := by
    have st : IsPushout k (i' ≫ v) (a' ≫ V) z := by rw [hVa, ← hh]; exact sh
    exact st.of_top hVb s'
  have hwU : simplicialWeakEquivalences U :=
    KanQuillen.anodyne_weak _ (SSet.anodyneExtensions.of_isPushout su hu)
  have hwV : simplicialWeakEquivalences V :=
    KanQuillen.anodyne_weak _ (SSet.anodyneExtensions.of_isPushout sv hv)
  let R : H ⟶ Q := sh.desc a' (d.p ≫ b') (by
    rw [← Category.assoc]
    change k ≫ a' = ((i ≫ u) ≫ d.p) ≫ b'
    rw [Category.assoc i, hup, hif]
    exact s'.w)
  have hxR : x ≫ R = a' := sh.inl_desc _ _ _
  have hzR : z ≫ R = d.p ≫ b' := sh.inr_desc _ _ _
  have hVR : V ≫ R = 𝟙 Q := by
    apply s'.hom_ext
    · rw [← Category.assoc, hVa, hxR, Category.comp_id]
    · rw [← Category.assoc, hVb, Category.assoc, hzR, ← Category.assoc, hvp,
        Category.id_comp, Category.comp_id]
  have hUR : U ≫ R = F := by
    apply s.hom_ext
    · rw [← Category.assoc, hUa, hxR, ha]
    · rw [← Category.assoc, hUb, Category.assoc, hzR, ← Category.assoc, hup, hb]
  have hwR : simplicialWeakEquivalences R :=
    simplicialWeakEquivalences.of_precomp V R hwV (hVR ▸ simplicialWeakEquivalences.id_mem Q)
  rw [← hUR]
  exact simplicialWeakEquivalences.comp_mem _ _ hwU hwR

lemma span_weak {C C' A A' B B' P Q : SSet.{u}}
    (k : C ⟶ A) (i : C ⟶ B) (k' : C' ⟶ A') (i' : C' ⟶ B')
    [Mono i] [Mono i'] (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (ha : simplicialWeakEquivalences a) (hb : simplicialWeakEquivalences b)
    (hc : simplicialWeakEquivalences c) (hk : k ≫ a = c ≫ k') (hi : i ≫ b = c ≫ i')
    {lA : A ⟶ P} {lB : B ⟶ P} {lA' : A' ⟶ Q} {lB' : B' ⟶ Q}
    (s : IsPushout k i lA lB) (s' : IsPushout k' i' lA' lB')
    (F : P ⟶ Q) (hFA : lA ≫ F = a ≫ lA') (hFB : lB ≫ F = b ≫ lB') :
    simplicialWeakEquivalences F := by
  let E := pushout i c
  let j : B ⟶ E := pushout.inl i c
  let e : C' ⟶ E := pushout.inr i c
  have se : IsPushout i c j e := IsPushout.of_hasPushout i c
  have : Mono e := MorphismProperty.of_isPushout se.flip
    (show (monomorphisms SSet) i from inferInstance)
  have hwj : simplicialWeakEquivalences j :=
    GeometricRecognition.left_proper _ _ _ _ se inferInstance hc
  let t : E ⟶ B' := se.desc b i' hi
  have htB : j ≫ t = b := se.inl_desc _ _ _
  have htC : e ≫ t = i' := se.inr_desc _ _ _
  have hwt : simplicialWeakEquivalences t :=
    simplicialWeakEquivalences.of_precomp j t hwj (htB ▸ hb)
  let H := pushout (k ≫ a) i
  let x : A' ⟶ H := pushout.inl (k ≫ a) i
  let y : B ⟶ H := pushout.inr (k ≫ a) i
  have sh : IsPushout (k ≫ a) i x y := IsPushout.of_hasPushout (k ≫ a) i
  let U : P ⟶ H := s.desc (a ≫ x) y (by rw [← Category.assoc]; exact sh.w)
  have hUA : lA ≫ U = a ≫ x := s.inl_desc _ _ _
  have hUB : lB ≫ U = y := s.inr_desc _ _ _
  have hwU : simplicialWeakEquivalences U := KanLocal.local_weak _
    (KanLocal.local_pushout_map k i a (GeometricRecognition.weak_local _ ha) s sh U hUA hUB)
  let z : E ⟶ H := se.desc y (k' ≫ x) (by
    rw [← sh.w, hk, Category.assoc])
  have hzB : j ≫ z = y := se.inl_desc _ _ _
  have hzC : e ≫ z = k' ≫ x := se.inr_desc _ _ _
  have sh' : IsPushout k' e x z := by
    have sr : IsPushout i (c ≫ k') (j ≫ z) x := by rw [← hk,hzB]; exact sh.flip
    exact (sr.of_top hzC se).flip
  let V : H ⟶ Q := sh'.desc lA' (t ≫ lB') (by rw [← Category.assoc, htC]; exact s'.w)
  have hVA : x ≫ V = lA' := sh'.inl_desc _ _ _
  have hVE : z ≫ V = t ≫ lB' := sh'.inr_desc _ _ _
  have hwV : simplicialWeakEquivalences V := under_weak k' e i' t hwt htC sh' s' V hVA hVE
  have hUV : U ≫ V = F := by
    apply s.hom_ext
    · rw [← Category.assoc, hUA, Category.assoc, hVA, hFA]
    · rw [← Category.assoc, hUB, ← hzB, Category.assoc, hVE, ← Category.assoc, htB, hFB]
  rw [← hUV]
  exact simplicialWeakEquivalences.comp_mem _ _ hwU hwV

end Thomason.SimplicialGluing

end

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer
open CategoryTheory Limits MorphismProperty Simplicial
open Attachments
open AttachmentComparison (upward nerve_mono_orderMap)

variable {C : Type v} [Category.{u} C]

abbrev posetObj (G : SSet.{u} ⥤ C) (P : Type u) [PartialOrder P] := G.obj (nerve P)
abbrev inc (G : SSet.{u} ⥤ C) {P : Type u} [PartialOrder P] (A : Set P) :
    posetObj G A ⟶ posetObj G P :=
  G.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor)
abbrev L (G : SSet.{u} ⥤ C) := SSet.sd ⋙ SSet.sd ⋙ G
abbrev R (N : C ⥤ SSet.{u}) := N ⋙ SSet.ex ⋙ SSet.ex
abbrev transferredAdjunction {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} (adj : G ⊣ N) :
    L G ⊣ R N :=
  (SSet.sdExAdjunction.comp SSet.sdExAdjunction).comp adj
abbrev W (N : C ⥤ SSet.{u}) := simplicialWeakEquivalences.inverseImage (R N)
abbrev Fib (N : C ⥤ SSet.{u}) := simplicialFibrations.inverseImage (R N)
abbrev Cof (N : C ⥤ SSet.{u}) := (Fib N ⊓ W N).llp

lemma weak_iff_nerve (N : C ⥤ SSet.{u}) {X Y : C} (f : X ⟶ Y) :
    W N f ↔ simplicialWeakEquivalences (N.map f) :=
  Subdivision.exSquared_map_weak_iff (N.map f)

structure PosetComparison (G : SSet.{u} ⥤ C) (N : C ⥤ SSet.{u}) (adj : G ⊣ N) : Prop where
  unit_weak : ∀ (P : Type u) [PartialOrder P],
    simplicialWeakEquivalences (adj.unit.app (nerve P))
  attachment_mono : ∀ {B : Type u} [PartialOrder B] (A : Set B) (_hA : IsLowerSet A)
    {X Y : C} (a : posetObj G A ⟶ X) (j : X ⟶ Y) (v : posetObj G B ⟶ Y),
    IsPushout a (inc G A) j v → Mono (N.map j)
  comparison : ∀ {B : Type u} [PartialOrder B] (A : Set B) (_hA : IsLowerSet A)
    (r : upward A →o A)
    (_hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ r z)
    {X Y : C} (a : posetObj G A ⟶ X) (j : X ⟶ Y) (v : posetObj G B ⟶ Y),
    IsPushout a (inc G A) j v →
    ∀ {P : SSet.{u}} {lX : N.obj X ⟶ P} {lB : N.obj (posetObj G B) ⟶ P},
    IsPushout (N.map a) (N.map (inc G A)) lX lB →
    ∀ F : P ⟶ N.obj Y, lX ≫ F = N.map j → lB ≫ F = N.map v →
      simplicialWeakEquivalences F

variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable (h : PosetComparison G N adj)
include h

lemma inc_mono {B : Type u} [PartialOrder B] (A : Set B) (hA : IsLowerSet A) :
    Mono (N.map (inc G A)) :=
  h.attachment_mono A hA (𝟙 _) (inc G A) (𝟙 _) IsPushout.of_id_fst

omit h in
lemma unit_local_of_iso {X Y : SSet.{u}} (e : X ≅ Y)
    (hX : KanLocal.Local (adj.unit.app X)) : KanLocal.Local (adj.unit.app Y) := by
  have he : adj.unit.app Y = e.inv ≫ adj.unit.app X ≫ N.map (G.map e.hom) := by
    have hn : e.hom ≫ adj.unit.app Y = adj.unit.app X ≫ N.map (G.map e.hom) :=
      adj.unit.naturality e.hom
    rw [← hn]
    simp
  rw [he]
  exact KanLocal.local_comp (KanLocal.local_iso e.inv)
    (KanLocal.local_comp hX (KanLocal.local_iso _))

lemma unit_local_initial {X : SSet.{u}} (hX : IsInitial X) : KanLocal.Local (adj.unit.app X) := by
  let P := ULift.{u} Empty
  have hP : IsInitial (nerve P) := SSet.isInitialOfNotNonempty (by
    rintro ⟨s⟩
    exact (s.obj 0).down.elim)
  exact unit_local_of_iso (hP.uniqueUpToIso hX)
    (GeometricRecognition.weak_local _ (h.unit_weak P))

variable [PreservesColimitsOfSize.{u,u} G]

lemma unit_local_attachment {B : Type u} [PartialOrder B]
    (A : Set B) (hA : IsLowerSet A) (r : upward A →o A)
    (hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ r z)
    {V Y : SSet.{u}} (a : nerve A ⟶ V) (j : V ⟶ Y) (v : nerve B ⟶ Y)
    (sc : IsPushout a (nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor) j v)
    (hV : KanLocal.Local (adj.unit.app V)) : KanLocal.Local (adj.unit.app Y) := by
  let i : nerve A ⟶ nerve B :=
    nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor
  have : Mono i := nerve_mono_orderMap (A := A) (E := B)
    (OrderEmbedding.subtype A).toOrderHom Subtype.val_injective
  let b := N.map (G.map a)
  let c := N.map (G.map i)
  have : Mono c := inc_mono h A hA
  let P := pushout b c
  let lV := pushout.inl b c
  let lB := pushout.inr b c
  have ss : IsPushout b c lV lB := IsPushout.of_hasPushout b c
  have hna : a ≫ adj.unit.app V = adj.unit.app (nerve A) ≫ b := adj.unit.naturality a
  have hni : i ≫ adj.unit.app (nerve B) = adj.unit.app (nerve A) ≫ c := adj.unit.naturality i
  let q : Y ⟶ P := sc.desc (adj.unit.app V ≫ lV) (adj.unit.app (nerve B) ≫ lB) (by
    change a ≫ adj.unit.app V ≫ lV = i ≫ adj.unit.app (nerve B) ≫ lB
    rw [← Category.assoc, hna, Category.assoc, ss.w,
      ← Category.assoc, ← hni, Category.assoc])
  have hqV : j ≫ q = adj.unit.app V ≫ lV := sc.inl_desc _ _ _
  have hqB : v ≫ q = adj.unit.app (nerve B) ≫ lB := sc.inr_desc _ _ _
  have hq : simplicialWeakEquivalences q := SimplicialGluing.span_weak a i b c
    (adj.unit.app V) (adj.unit.app (nerve B)) (adj.unit.app (nerve A))
    (KanLocal.local_weak _ hV) (h.unit_weak B) (h.unit_weak A)
    (adj.unit.naturality a) (adj.unit.naturality i) sc ss q hqV hqB
  have cs : IsPushout (G.map a) (inc G A) (G.map j) (G.map v) := sc.map G
  let t : P ⟶ N.obj (G.obj Y) := ss.desc (N.map (G.map j)) (N.map (G.map v)) (by
    dsimp [b,c]
    rw [← N.map_comp, ← N.map_comp]
    exact congrArg N.map cs.w)
  have htV : lV ≫ t = N.map (G.map j) := ss.inl_desc _ _ _
  have htB : lB ≫ t = N.map (G.map v) := ss.inr_desc _ _ _
  have ht : simplicialWeakEquivalences t := h.comparison A hA r hadj (G.map a)
    (G.map j) (G.map v) cs ss t htV htB
  have hqt : q ≫ t = adj.unit.app Y := by
    apply sc.hom_ext
    · rw [← Category.assoc,hqV,Category.assoc,htV]
      exact (adj.unit.naturality j).symm
    · rw [← Category.assoc,hqB,Category.assoc,htB]
      exact (adj.unit.naturality v).symm
  apply GeometricRecognition.weak_local
  rw [← hqt]
  exact simplicialWeakEquivalences.comp_mem _ _ hq ht

open PartialOrder HornAttachments KanLocal
open SubdividedUnit (D Flags BoundaryFlags boundaryCoprodIso simplexCoprodIso boundaryCoprodIso_naturality)

lemma boundary_unit_successor (I : Type u) (d : ℕ) {X Y : SSet.{u}}
    (a : (∐ fun _ : I => (∂Δ[d] : SSet)) ⟶ X) (j : X ⟶ Y)
    (v : (∐ fun _ : I => Δ[d]) ⟶ Y)
    (sc : IsPushout a (Limits.Sigma.map (fun _ : I => ∂Δ[d].ι)) j v)
    (hX : Local (adj.unit.app (D.obj X))) :
    Local (adj.unit.app (D.obj Y)) ∧ Mono (D.map j) ∧ Mono (N.map (G.map (D.map j))) := by
  let A := PosetCoproduct.old I (BoundaryFlags d)
  let rA := PosetCoproduct.oldRetraction I (BoundaryFlags d)
    (flagRetraction (simplexFaces (SSet.boundary d)))
  have hA : IsLowerSet A := PosetCoproduct.old_lower I _ (oldSet_lower _)
  have hrA : ∀ a : A, rA ⟨a.val,a.val,a.property,le_rfl⟩ = a :=
    PosetCoproduct.oldRetraction_retract I _ _ (flagRetraction_retract _)
  have hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ rA z :=
    PosetCoproduct.oldRetraction_adjunction I _ _ (flagRetraction_adjunction _)
  let a' := (boundaryCoprodIso I d).inv ≫ D.map a
  let v' := (simplexCoprodIso I d).inv ≫ D.map v
  let i : nerve A ⟶ nerve (PosetCoproduct.Piece I (Flags d)) :=
    nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor
  have sq : IsPushout a' i (D.map j) v' := by
    apply (sc.map D).of_iso (boundaryCoprodIso I d) (Iso.refl _)
      (simplexCoprodIso I d) (Iso.refl _)
    · simp [a']
    · exact boundaryCoprodIso_naturality I d
    · simp
    · simp [v']
  have : Mono i := nerve_mono_orderMap (A := A) (E := PosetCoproduct.Piece I (Flags d))
    (OrderEmbedding.subtype A).toOrderHom Subtype.val_injective
  refine ⟨unit_local_attachment h A hA rA hadj a' (D.map j) v' sq hX,
    Adhesive.mono_of_isPushout_of_mono_right sq, ?_⟩
  exact h.attachment_mono A hA (G.map a') (G.map (D.map j)) (G.map v') (sq.map G)

lemma unit_local_skeleton (K : SSet.{u}) (d : ℕ) :
    Local (adj.unit.app (D.obj ((SSet.relativeCellComplex K).F.obj d))) := by
  induction d with
  | zero =>
    apply unit_local_initial h
    apply IsInitial.isInitialObj
    have h₀ : IsInitial (⊥ : K.Subcomplex).toSSet :=
      SSet.isInitialOfNotNonempty (by rintro ⟨s⟩; exact s.property)
    exact h₀.ofIso (SSet.relativeCellComplex K).isoBot.symm
  | succ d ih =>
    exact (boundary_unit_successor h
      (SSet.relativeCellComplexOfMono.Cell (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) d) d
      (SSet.relativeCellComplexOfMono.t _ d) (SSet.relativeCellComplexOfMono.r _ d)
      (SSet.relativeCellComplexOfMono.b _ d) (SSet.relativeCellComplexOfMono.isPushout _ d)
      ih).1

lemma skeleton_monos (K : SSet.{u}) (d : ℕ) :
    Mono (D.map ((SSet.relativeCellComplex K).F.map (homOfLE (Nat.le_succ d)))) ∧
      Mono (N.map (G.map (D.map
        ((SSet.relativeCellComplex K).F.map (homOfLE (Nat.le_succ d)))))) :=
  (boundary_unit_successor h
    (SSet.relativeCellComplexOfMono.Cell (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) d) d
    (SSet.relativeCellComplexOfMono.t _ d) (SSet.relativeCellComplexOfMono.r _ d)
    (SSet.relativeCellComplexOfMono.b _ d) (SSet.relativeCellComplexOfMono.isPushout _ d)
    (unit_local_skeleton h K d)).2

variable [PreservesFilteredColimitsOfSize.{u,u} N]

theorem subdivided_unit_local (K : SSet.{u}) : Local (adj.unit.app (D.obj K)) := by
  let c := SSet.relativeCellComplex K
  let F := c.F ⋙ D
  let H := c.F ⋙ D ⋙ G ⋙ N
  let f : F ⟶ H := Functor.whiskerLeft F adj.unit
  have hf : Local (colim.map f) := local_colimit_nat F H f
    (fun d => (skeleton_monos h K d).1) (fun d => (skeleton_monos h K d).2)
    (unit_local_skeleton h K)
  have hcF : IsColimit (D.mapCocone { pt := K, ι := c.incl }) :=
    isColimitOfPreserves D c.isColimit
  let : PreservesFilteredColimitsOfSize.{0,0} N :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits N
  let : PreservesColimitsOfSize.{0,0} G := preservesSmallestColimits_of_preservesColimits G
  have hcG : IsColimit ((D ⋙ G ⋙ N).mapCocone { pt := K, ι := c.incl }) :=
    isColimitOfPreserves (D ⋙ G ⋙ N) c.isColimit
  let eF : D.obj K ≅ colimit F := hcF.coconePointUniqueUpToIso (colimit.isColimit F)
  let eG : N.obj (G.obj (D.obj K)) ≅ colimit H :=
    hcG.coconePointUniqueUpToIso (colimit.isColimit H)
  have hF (d : ℕ) : D.map (c.incl.app d) ≫ eF.hom = colimit.ι F d :=
    hcF.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) d
  have hG (d : ℕ) : colimit.ι H d ≫ eG.inv = N.map (G.map (D.map (c.incl.app d))) :=
    hcG.comp_coconePointUniqueUpToIso_inv (colimit.isColimit H) d
  have he : adj.unit.app (D.obj K) = eF.hom ≫ colim.map f ≫ eG.inv := by
    apply hcF.hom_ext
    intro d
    change D.map (c.incl.app d) ≫ adj.unit.app (D.obj K) =
      D.map (c.incl.app d) ≫ eF.hom ≫ colim.map f ≫ eG.inv
    rw [← Category.assoc, hF, ← Category.assoc, colimit.ι_map, Category.assoc, hG]
    exact adj.unit.naturality (D.map (c.incl.app d))
  rw [he]
  exact local_comp (local_iso _) (local_comp hf (local_iso _))

end Thomason.AbstractTransfer

end

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer.Horns
open CategoryTheory Limits Simplicial PartialOrder KanLocal
open AttachmentComparison (upward)
open HornAttachments
open AbstractTransfer
open TransferAcyclicity (PosetAttachment sumData)
attribute [-instance] CategoryTheory.Sigma.sigma

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u,u} C]
variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable [PreservesColimitsOfSize.{u,u} G]

abbrev arrow (G : SSet.{u} ⥤ C) (d : PosetAttachment.{u}) := Arrow.mk (inc G d.A)

def Admissible (G : SSet.{u} ⥤ C) : MorphismProperty (C) :=
  fun _ _ f => ∃ d : PosetAttachment.{u}, Nonempty (arrow G d ≅ Arrow.mk f)

instance : (Admissible G).RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ (by
    rintro _ _ e ⟨d,⟨a⟩⟩
    exact ⟨d,⟨a ≪≫ e⟩⟩)

omit [HasColimitsOfSize.{u,u} C] [PreservesColimitsOfSize.{u,u} G] in
lemma horn_admissible : hornImages (L G) ≤ Admissible G := by
  rintro X Y f hf
  simp only [hornImages, MorphismProperty.iSup_iff] at hf
  obtain ⟨m,⟨k⟩⟩ := hf
  let d : PosetAttachment := {
    B := NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (m+2))))
    order := inferInstance
    A := oldSet (simplexFaces (SSet.horn (m+1) k))
    lower := oldSet_lower _
    retraction := flagRetraction _
    retract := flagRetraction_retract _
    adjunction := flagRetraction_adjunction _
    anodyne := by
      exact (SSet.anodyneExtensions.arrow_mk_iso_iff (Arrow.isoMk
        (oldFlagsIso (SSet.horn (m+1) k)) (Subdivision.sdTwiceSimplexIso (m+1))
        (oldFlagsIso_naturality (SSet.horn (m+1) k)).symm)).mp
          (HornSubdivision.sdTwice_horn_anodyne (by omega) k) }
  refine ⟨d, ⟨(Arrow.isoMk (G.mapIso (oldFlagsIso (SSet.horn (m+1) k)))
    (G.mapIso (Subdivision.sdTwiceSimplexIso (m+1))) ?_).symm⟩⟩
  change G.map _ ≫ G.map _ =
    G.map _ ≫ G.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg G.map (oldFlagsIso_naturality (SSet.horn (m+1) k)).symm

section Coproducts
variable {I : Type u} (d : I → PosetAttachment.{u})

def posetCoprodIso (P : I → Type u) [∀ i, PartialOrder (P i)] :
    (∐ fun i => posetObj G (P i)) ≅ posetObj G (Σ i, P i) :=
  (PreservesCoproduct.iso G (fun i => nerve (P i))).symm ≪≫
    G.mapIso (DependentPosets.iso P)

def oldCoprodIso : (∐ fun i => posetObj G (d i).A) ≅ posetObj G (sumData d).A :=
  (PreservesCoproduct.iso G (fun i => nerve (d i).A)).symm ≪≫
    G.mapIso (DependentPosets.oldNerveIso (fun i => (d i).A))

@[reassoc] lemma posetCoprodIso_ι (P : I → Type u) [∀ i, PartialOrder (P i)] (i : I) :
    Sigma.ι (fun i => posetObj G (P i)) i ≫ (posetCoprodIso (G := G) P).hom =
      G.map (nerveMap (DependentPosets.incl P i).toFunctor) := by
  simp only [posetCoprodIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison, ← Functor.map_comp,
    DependentPosets.iso_hom_ι]

@[reassoc] lemma oldCoprodIso_ι (i : I) :
    Sigma.ι (fun i => posetObj G (d i).A) i ≫ (oldCoprodIso (G := G) d).hom =
      G.map (nerveMap
        ((DependentPosets.oldIso (fun i => (d i).A)).toOrderEmbedding.toOrderHom.comp
          (DependentPosets.incl (fun i => (d i).A) i)).toFunctor) := by
  change Sigma.ι (fun i => G.obj (nerve (d i).A)) i ≫
    ((PreservesCoproduct.iso G (fun i => nerve (d i).A)).inv ≫
      G.map (DependentPosets.oldNerveIso (fun i => (d i).A)).hom) = G.map _
  rw [← Category.assoc, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison, ← Functor.map_comp,
    DependentPosets.oldNerveIso_ι]

lemma coprod_inc : Limits.Sigma.map (fun i => inc G (d i).A) ≫
    (posetCoprodIso (G := G) (fun i => (d i).B)).hom =
    (oldCoprodIso (G := G) d).hom ≫ inc G (sumData d).A := by
  apply Sigma.hom_ext
  intro i
  erw [Sigma.ι_map_assoc, posetCoprodIso_ι]
  erw [← Category.assoc]
  erw [oldCoprodIso_ι]
  change G.map _ ≫ G.map _ =
    G.map _ ≫ G.map _
  erw [← Functor.map_comp, ← Functor.map_comp]
  rfl

end Coproducts

instance admissible_coproducts (I : Type u) : (Admissible G).IsStableUnderCoproductsOfShape I := by
  apply MorphismProperty.IsStableUnderCoproductsOfShape.mk
  intro X Y _ _ f hf
  choose d e using hf
  let a (i : I) : arrow G (d i) ≅ Arrow.mk (f i) := Classical.choice (e i)
  let eA := Limits.Sigma.mapIso (fun i => Arrow.leftFunc.mapIso (a i))
  let eB := Limits.Sigma.mapIso (fun i => Arrow.rightFunc.mapIso (a i))
  have h : (Limits.Sigma.map (fun i => inc G (d i).A)) ≫ eB.hom =
      eA.hom ≫ Limits.Sigma.map f := by
    change Limits.Sigma.map (fun i => inc G (d i).A) ≫
        Limits.Sigma.map (fun i => (a i).hom.right) =
      Limits.Sigma.map (fun i => (a i).hom.left) ≫ Limits.Sigma.map f
    rw [Sigma.map_comp_map, Sigma.map_comp_map]
    congr 1
    funext i
    exact (a i).hom.w.symm
  have e' : Arrow.mk (Limits.Sigma.map (fun i => inc G (d i).A)) ≅
      Arrow.mk (Limits.Sigma.map f) := Arrow.isoMk eA eB h.symm
  have e₀ : Arrow.mk (Limits.Sigma.map (fun i => inc G (d i).A)) ≅
      arrow G (sumData d) := Arrow.isoMk (oldCoprodIso (G := G) d)
        (posetCoprodIso (G := G) (fun i => (d i).B)) (coprod_inc d).symm
  exact ⟨sumData d, ⟨e₀.symm ≪≫ e'⟩⟩

instance : MorphismProperty.IsStableUnderCoproducts.{u} (Admissible G) where

variable (h : PosetComparison G N adj)
include h

omit [HasColimitsOfSize.{u,u} C] [PreservesColimitsOfSize.{u,u} G] in
lemma poset_attachment_local (d : PosetAttachment.{u})
    {X Y : C} (a : posetObj G d.A ⟶ X)
    (j : X ⟶ Y) (v : posetObj G d.B ⟶ Y) (sc : IsPushout a (inc G d.A) j v) :
    Local (N.map j) ∧ Mono (N.map j) := by
  let b := N.map a
  let i := N.map (inc G d.A)
  let ss := IsPushout.of_hasPushout b i
  let F : pushout b i ⟶ N.obj Y := ss.desc (N.map j) (N.map v) (by
    rw [← N.map_comp, ← N.map_comp, sc.w])
  have hFX : pushout.inl b i ≫ F = N.map j := ss.inl_desc _ _ _
  have hFB : pushout.inr b i ≫ F = N.map v := ss.inr_desc _ _ _
  have hF := GeometricRecognition.weak_local F
    (h.comparison d.A d.lower d.retraction d.adjunction a j v sc ss F hFX hFB)
  have hi : SSet.anodyneExtensions i := by
    have hmono : Mono i := inc_mono h d.A d.lower
    rw [KanQuillen.anodyne_class]
    refine ⟨hmono, ?_⟩
    refine simplicialWeakEquivalences.of_precomp (W' := simplicialWeakEquivalences)
      (adj.unit.app (nerve d.A)) i (h.unit_weak d.A) ?_
    let inclusion : nerve d.A ⟶ nerve d.B :=
      nerveMap (OrderEmbedding.subtype d.A).toOrderHom.toFunctor
    have naturality : inclusion ≫ adj.unit.app (nerve d.B) =
        adj.unit.app (nerve d.A) ≫ i := adj.unit.naturality inclusion
    rw [← naturality]
    exact simplicialWeakEquivalences.comp_mem _ _
      (KanQuillen.anodyne_weak _ d.anodyne) (h.unit_weak d.B)
  refine ⟨?_,h.attachment_mono d.A d.lower a j v sc⟩
  rw [← hFX]
  exact local_comp (local_anodyne _ (SSet.anodyneExtensions.of_isPushout ss hi)) hF

omit [HasColimitsOfSize.{u,u} C] [PreservesColimitsOfSize.{u,u} G] in
lemma admissible_pushout {A B X Y : C}
    (i : A ⟶ B) (hi : Admissible G i) (a : A ⟶ X) (j : X ⟶ Y) (v : B ⟶ Y)
    (sc : IsPushout a i j v) : Local (N.map j) ∧ Mono (N.map j) := by
  obtain ⟨d,⟨e⟩⟩ := hi
  let eA : posetObj G d.A ≅ A := Arrow.leftFunc.mapIso e
  let eB : posetObj G d.B ≅ B := Arrow.rightFunc.mapIso e
  have sq : IsPushout (eA.hom ≫ a) (inc G d.A) j (eB.hom ≫ v) := by
    apply sc.of_iso eA.symm (Iso.refl _) eB.symm (Iso.refl _)
    · simp
    · apply (cancel_epi eA.hom).mp
      simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
      have hw : eA.hom ≫ i = inc G d.A ≫ eB.hom := e.hom.w
      rw [← Category.assoc, hw, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp
    · simp
  exact poset_attachment_local h d _ _ _ sq

lemma coproduct_horn_pushout {X Y : C}
    (j : X ⟶ Y) (hj : (MorphismProperty.coproducts.{u}
      (hornImages (L G))).pushouts j) :
    Local (N.map j) ∧ Mono (N.map j) := by
  obtain ⟨A,B,i,a,v,hi,sc⟩ := hj
  exact admissible_pushout h i
    ((Admissible G).coproducts_le _ (MorphismProperty.coproducts_monotone horn_admissible _ hi))
    a j v sc

end Thomason.AbstractTransfer.Horns

end

noncomputable section
universe u v w z


namespace Thomason.AbstractTransfer
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open KanLocal SubdividedUnit Horns
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

variable {C : Type v} [Category.{u} C] [HasColimitsOfSize.{u,u} C]
variable {G : SSet.{u} ⥤ C} {N : C ⥤ SSet.{u}} {adj : G ⊣ N}
variable [PreservesColimitsOfSize.{u,u} G] [PreservesFilteredColimitsOfSize.{u,u} N]
variable (h : PosetComparison G N adj)
include h

lemma sequential_horn_weak {X Y : C} (f : X ⟶ Y)
    (ht : (MorphismProperty.coproducts.{u} (hornImages (L G))).pushouts.TransfiniteCompositionOfShape ℕ f) : W N f := by
  let G := ht.F ⋙ N
  let F := (Functor.const ℕ).obj (G.obj 0)
  let a : F ⟶ G := {
    app n := G.map (homOfLE (Nat.zero_le n))
    naturality i j u := by
      change 𝟙 (G.obj 0) ≫ G.map _ = G.map _ ≫ G.map u
      rw [Category.id_comp, ← G.map_comp]
      rfl }
  have hG (n : ℕ) : Local (G.map (homOfLE (Nat.le_succ n))) ∧
      Mono (G.map (homOfLE (Nat.le_succ n))) :=
    coproduct_horn_pushout h _ (ht.map_mem n (by simp))
  have ha (n : ℕ) : Local (a.app n) := by
    induction n with
    | zero =>
      change Local (G.map (𝟙 0))
      rw [G.map_id]
      exact local_iso _
    | succ n ih =>
      have he : a.app (n+1) = a.app n ≫ G.map (homOfLE (Nat.le_succ n)) := by
        change G.map _ = G.map _ ≫ G.map _
        rw [← G.map_comp]
        rfl
      rw [he]
      exact local_comp ih (hG n).1
  have hl := local_colimit_nat F G a (fun n => by dsimp [F]; infer_instance)
    (fun n => (hG n).2) ha
  have hcF : IsColimit (constCocone ℕ (G.obj 0)) := isColimitConstCocone _ _
  let : PreservesFilteredColimitsOfSize.{0,0} N :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits N
  have hcG : IsColimit (N.mapCocone { pt := Y, ι := ht.incl }) :=
    isColimitOfPreserves N ht.isColimit
  let eF : G.obj 0 ≅ colimit F := hcF.coconePointUniqueUpToIso (colimit.isColimit F)
  let eG : N.obj Y ≅ colimit G := hcG.coconePointUniqueUpToIso (colimit.isColimit G)
  have eFι : eF.hom = colimit.ι F 0 := by
    exact (Category.id_comp eF.hom).symm.trans
      (hcF.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) 0)
  have eGι : colimit.ι G 0 ≫ eG.inv = N.map (ht.incl.app 0) :=
    hcG.comp_coconePointUniqueUpToIso_inv (colimit.isColimit G) 0
  have he : N.map (ht.incl.app 0) = eF.hom ≫ colim.map a ≫ eG.inv := by
    rw [eFι, ← Category.assoc, colimit.ι_map, Category.assoc, eGι]
    change _ = G.map (𝟙 0) ≫ _
    rw [G.map_id, Category.id_comp]
  apply (weak_iff_nerve N f).mpr
  apply local_weak
  rw [← ht.fac, N.map_comp]
  change Local (N.map ht.isoBot.inv ≫ N.map (ht.incl.app 0))
  rw [he]
  exact local_comp (local_iso _) (local_comp (local_iso _) (local_comp hl (local_iso _)))

theorem horn_acyclicity [IsCardinalForSmallObjectArgument (hornImages (L G)) Cardinal.aleph0.{u}] :
    (hornImages (L G)).rlp.llp ≤ W N := by
  rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument_aleph0]
  rintro X Y f ⟨A,B,g,r,⟨hh⟩⟩
  exact (W N).of_retract r (sequential_horn_weak h g hh)

variable [IsLocallyPresentable.{u} C]
variable [IsCardinalForSmallObjectArgument (hornImages (L G)) Cardinal.aleph0.{u}]

omit h [PreservesColimitsOfSize.{u,u} G] [PreservesFilteredColimitsOfSize.{u,u} N]
  [IsCardinalForSmallObjectArgument (hornImages (L G)) Cardinal.aleph0.{u}] in
include adj in
lemma first_wfs_aux : IsWeakFactorizationSystem (Fib N).llp (Fib N) := by
  have hwfs := hornImages_weakFactorization (L G)
  rwa [hornImages_rlp (transferredAdjunction adj)] at hwfs

lemma first_left_class : (Fib N).llp = Cof N ⊓ W N := by
  have hc : (Fib N).llp ≤ Cof N := fun _ _ _ hi _ _ p hp => hi p hp.1
  have hw : (Fib N).llp ≤ W N := by
    have hh := horn_acyclicity h
    rwa [hornImages_rlp (transferredAdjunction adj)] at hh
  apply le_antisymm (le_inf hc hw)
  intro X Y f hf
  have := first_wfs_aux (G := G) (adj := adj)
  let d := factorizationData (Fib N).llp (Fib N) f
  have hpw : W N d.p := (W N).of_precomp d.i d.p (hw _ d.hi) (d.fac.symm ▸ hf.2)
  have : HasLiftingProperty f d.p := hf.1 d.p ⟨d.hp,hpw⟩
  exact (Fib N).llp.of_retract (RetractArrow.ofLeftLiftingProperty d.fac) d.hi

theorem first_wfs : IsWeakFactorizationSystem (Cof N ⊓ W N) (Fib N) := by
  rw [← first_left_class h]
  exact first_wfs_aux (G := G) (adj := adj)

variable [HasLimitsOfSize.{u,u} C]

@[instance_reducible] def model : ModelCategory C := by
  letI : CategoryWithWeakEquivalences C := ⟨W N⟩
  letI : CategoryWithFibrations C := ⟨Fib N⟩
  letI : CategoryWithCofibrations C := ⟨Cof N⟩
  letI : (weakEquivalences C).HasTwoOutOfThreeProperty :=
    show (W N).HasTwoOutOfThreeProperty from inferInstance
  letI : IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C) := first_wfs h
  letI : IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C) :=
    transferred_second_wfs (transferredAdjunction adj)
  exact ModelCategory.mk' _

end Thomason.AbstractTransfer

end

end OAI
