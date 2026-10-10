import OAI.CategoryTheory.Thomason.Simplicial.RealizationSubcomplexSemantics
import OAI.CategoryTheory.Thomason.Simplicial.SkeletalWeakEquivalences
import OAI.CategoryTheory.Thomason.Transfer.WeakFactorizationRecognition
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

namespace OAI

section

/-! # The simplicial gluing input, derived from Kan–Quillen

A Brown factorization in the one span shape reduces arbitrary objectwise
weak equivalences to the acyclic relative cofibrations proved above.
The only published hypothesis is the explicitly stated Kan–Quillen input.
-/

namespace Thomason.Construction.SimplicialSpan

open CategoryTheory CategoryTheory.Limits

/-- Weak equivalence at the three objects of this span. -/
def ObjectwiseWeak {X Y : Diagram} (f : X ⟶ Y) : Prop :=
  realizationWeakEquivalences f.a ∧ realizationWeakEquivalences f.b ∧
    realizationWeakEquivalences f.c

theorem ObjectwiseWeak.of_comp {X Y Z : Diagram} (f : X ⟶ Y) (g : Y ⟶ Z)
    (kq : KanQuillenPublishedInput.{0}) (hg : ObjectwiseWeak g)
    (hfg : ObjectwiseWeak (f ≫ g)) : ObjectwiseWeak f := by
  have := kq.twoOutOfThree
  exact ⟨realizationWeakEquivalences.of_postcomp f.a g.a hg.1 hfg.1,
    realizationWeakEquivalences.of_postcomp f.b g.b hg.2.1 hfg.2.1,
    realizationWeakEquivalences.of_postcomp f.c g.c hg.2.2 hfg.2.2⟩

/-- Actual realization weak equivalences are preserved by the pushout functor
on spans whose specified left legs are monomorphisms. -/
theorem pushoutMap_weak {X Y : Diagram} (f : X ⟶ Y)
    [Mono X.left] [Mono Y.left] (kq : KanQuillenPublishedInput.{0})
    (hf : ObjectwiseWeak f) : realizationWeakEquivalences (pushoutMap f) := by
  have := kq.twoOutOfThree
  let q := factorization (desc f (𝟙 Y)) kq
  let i : X ⟶ q.Z := inl X Y ≫ q.i
  let s : Y ⟶ q.Z := inr X Y ≫ q.i
  have hip : i ≫ q.p = f := by
    dsimp [i]
    rw [Category.assoc, q.fac, inl_desc]
  have hsp : s ≫ q.p = 𝟙 Y := by
    dsimp [s]
    rw [Category.assoc, q.fac, inr_desc]
  have hp : ObjectwiseWeak q.p := ⟨q.hpA.2, q.hpB.2, q.hpC.2⟩
  have hiw : ObjectwiseWeak i := ObjectwiseWeak.of_comp i q.p kq hp (by rw [hip]; exact hf)
  have hsw : ObjectwiseWeak s := ObjectwiseWeak.of_comp s q.p kq hp (by
    rw [hsp]
    exact ⟨realizationWeakEquivalences.id_mem _, realizationWeakEquivalences.id_mem _,
      realizationWeakEquivalences.id_mem _⟩)
  have hi : Cofibration i := (inl_cofibration X Y kq).comp q.hi kq
  have hs : Cofibration s := (inr_cofibration X Y kq).comp q.hi kq
  have hi' := pushoutMap_weak_of_cofibration i kq hi hiw.1 hiw.2.1 hiw.2.2
  have hs' := pushoutMap_weak_of_cofibration s kq hs hsw.1 hsw.2.1 hsw.2.2
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

/-- The classical gluing specialization used by the strict-category proof
follows from the Kan–Quillen model axioms. -/
theorem constructedSimplicialGluing (kq : KanQuillenPublishedInput.{0}) :
    PublishedSimplicialGluingInput where
  glue {A B C P A' B' C' P'} {i j b c i' j' b' c'} hp hp' _ _
      fA fB fC fP hi hj hb hc hA hB hC := by
    let X : SimplicialSpan.Diagram := ⟨A, B, C, i, j⟩
    let Y : SimplicialSpan.Diagram := ⟨A', B', C', i', j'⟩
    let f : X ⟶ Y := ⟨fA, fB, fC, hi, hj⟩
    have hw := SimplicialSpan.pushoutMap_weak f kq ⟨hA, hB, hC⟩
    let : HomotopicalAlgebra.ModelCategory SSet.{0} := kq.model
    have hiso (U V : SSet.{0}) (e : U ≅ V) : realizationWeakEquivalences e.hom := by
      exact (HomotopicalAlgebra.weakEquivalence_iff e.hom).mp inferInstance
    rw [← SimplicialSpan.pushoutMap_fac hp hp' f fP hb hc]
    exact realizationWeakEquivalences.comp_mem _ _ (hiso _ _ hp.isoPushout)
      (realizationWeakEquivalences.comp_mem _ _ hw (hiso _ _ hp'.isoPushout.symm))

end Thomason.Construction

end

section

/-! # Extending stationary deformations over pushouts

The interval product preserves the actual topological pushout. A deformation
stationary on the attaching subspace therefore glues to a deformation of
the pushout, with a strict retraction to the other summand.
-/

namespace Thomason.Construction.TopologicalDeformation

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- The precise deformation data needed for a horn attachment. -/
structure Data {A B : TopCat.{0}} (i : A ⟶ B) where
  retraction : B ⟶ A
  left_inv : i ≫ retraction = 𝟙 A
  homotopy : (retraction ≫ i).hom.HomotopyRel (ContinuousMap.id B) (Set.range i.hom)

/-- A homotopy with its time coordinate in the cylinder's second factor. -/
def Data.track {A B : TopCat.{0}} {i : A ⟶ B} (d : Data i) :
    TopologicalInterval.cylinder.obj B ⟶ B :=
  TopCat.ofHom ⟨fun p => d.homotopy (p.2, p.1),
    d.homotopy.continuous.comp (by fun_prop)⟩

@[simp]
theorem Data.track_zero {A B : TopCat.{0}} {i : A ⟶ B} (d : Data i) :
    TopologicalInterval.sectionAt B 0 ≫ d.track = d.retraction ≫ i := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact d.homotopy.map_zero_left x

@[simp]
theorem Data.track_one {A B : TopCat.{0}} {i : A ⟶ B} (d : Data i) :
    TopologicalInterval.sectionAt B 1 ≫ d.track = 𝟙 B := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact d.homotopy.map_one_left x

/-- The full track is stationary on the attaching subspace. -/
theorem Data.track_stationary {A B : TopCat.{0}} {i : A ⟶ B} (d : Data i) :
    TopologicalInterval.cylinder.map i ≫ d.track = TopologicalInterval.projection A ≫ i := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  have ht := d.homotopy.eq_fst p.2 (Set.mem_range_self p.1)
  have hl := congrArg (fun f => f.hom p.1) d.left_inv
  change d.homotopy (p.2, i.hom p.1) = i.hom p.1
  change _ = i.hom (d.retraction.hom (i.hom p.1)) at ht
  exact ht.trans (congrArg i.hom hl)

variable {A B X P : TopCat.{0}} {i : A ⟶ B} {f : A ⟶ X}
  {b : B ⟶ P} {j : X ⟶ P}

/-- Retraction on the actual pushout. -/
def pushoutRetraction (h : IsPushout i f b j) (d : Data i) : P ⟶ X :=
  h.desc (d.retraction ≫ f) (𝟙 X) (by rw [← Category.assoc, d.left_inv]; simp)

theorem pushoutRetraction_left (h : IsPushout i f b j) (d : Data i) :
    j ≫ pushoutRetraction h d = 𝟙 X := h.inr_desc _ _ _

theorem track_compatible (h : IsPushout i f b j) (d : Data i) :
    TopologicalInterval.cylinder.map i ≫ (d.track ≫ b) =
      TopologicalInterval.cylinder.map f ≫ (TopologicalInterval.projection X ≫ j) := by
  rw [← Category.assoc, d.track_stationary, Category.assoc, h.w]
  rfl

/-- Gluing the relative track uses preservation of pushouts by product with I. -/
def pushoutTrack (h : IsPushout i f b j) (d : Data i) :
    TopologicalInterval.cylinder.obj P ⟶ P :=
  (TopologicalInterval.cylinder.map_isPushout h).desc (d.track ≫ b)
    (TopologicalInterval.projection X ≫ j) (track_compatible h d)

@[reassoc]
theorem pushoutTrack_inl (h : IsPushout i f b j) (d : Data i) :
    TopologicalInterval.cylinder.map b ≫ pushoutTrack h d = d.track ≫ b :=
  (TopologicalInterval.cylinder.map_isPushout h).inl_desc _ _ _

@[reassoc]
theorem pushoutTrack_inr (h : IsPushout i f b j) (d : Data i) :
    TopologicalInterval.cylinder.map j ≫ pushoutTrack h d =
      TopologicalInterval.projection X ≫ j :=
  (TopologicalInterval.cylinder.map_isPushout h).inr_desc _ _ _

@[reassoc]
theorem pushoutRetraction_inl (h : IsPushout i f b j) (d : Data i) :
    b ≫ pushoutRetraction h d = d.retraction ≫ f := h.inl_desc _ _ _

theorem section_naturality {A B : TopCat.{0}} (f : A ⟶ B) (t : unitInterval) :
    f ≫ TopologicalInterval.sectionAt B t =
      TopologicalInterval.sectionAt A t ≫ TopologicalInterval.cylinder.map f := rfl

/-- The glued track starts at the retraction followed by the inclusion. -/
theorem pushoutTrack_zero (h : IsPushout i f b j) (d : Data i) :
    TopologicalInterval.sectionAt P 0 ≫ pushoutTrack h d = pushoutRetraction h d ≫ j := by
  apply h.hom_ext
  · calc
      b ≫ (TopologicalInterval.sectionAt P 0 ≫ pushoutTrack h d) =
          TopologicalInterval.sectionAt B 0 ≫
            (TopologicalInterval.cylinder.map b ≫ pushoutTrack h d) := by
              rw [← Category.assoc, section_naturality, Category.assoc]
      _ = (d.retraction ≫ i) ≫ b := by
        rw [pushoutTrack_inl, ← Category.assoc, d.track_zero]
      _ = (d.retraction ≫ f) ≫ j := by rw [Category.assoc, h.w, ← Category.assoc]
      _ = b ≫ (pushoutRetraction h d ≫ j) := by rw [← Category.assoc, pushoutRetraction_inl]
  · calc
      j ≫ (TopologicalInterval.sectionAt P 0 ≫ pushoutTrack h d) =
          TopologicalInterval.sectionAt X 0 ≫
            (TopologicalInterval.cylinder.map j ≫ pushoutTrack h d) := by
              rw [← Category.assoc, section_naturality, Category.assoc]
      _ = j := by rw [pushoutTrack_inr, ← Category.assoc, TopologicalInterval.section_projection,
        Category.id_comp]
      _ = j ≫ (pushoutRetraction h d ≫ j) := by
        rw [← Category.assoc, pushoutRetraction_left, Category.id_comp]

/-- The glued track ends at the identity of the pushout. -/
theorem pushoutTrack_one (h : IsPushout i f b j) (d : Data i) :
    TopologicalInterval.sectionAt P 1 ≫ pushoutTrack h d = 𝟙 P := by
  apply h.hom_ext
  · calc
      b ≫ (TopologicalInterval.sectionAt P 1 ≫ pushoutTrack h d) =
          TopologicalInterval.sectionAt B 1 ≫
            (TopologicalInterval.cylinder.map b ≫ pushoutTrack h d) := by
              rw [← Category.assoc, section_naturality, Category.assoc]
      _ = b := by rw [pushoutTrack_inl, ← Category.assoc, d.track_one, Category.id_comp]
      _ = b ≫ 𝟙 P := (Category.comp_id b).symm
  · calc
      j ≫ (TopologicalInterval.sectionAt P 1 ≫ pushoutTrack h d) =
          TopologicalInterval.sectionAt X 1 ≫
            (TopologicalInterval.cylinder.map j ≫ pushoutTrack h d) := by
              rw [← Category.assoc, section_naturality, Category.assoc]
      _ = j := by rw [pushoutTrack_inr, ← Category.assoc, TopologicalInterval.section_projection,
        Category.id_comp]
      _ = j ≫ 𝟙 P := (Category.comp_id j).symm

/-- The pushout of a stationary deformation is itself a stationary deformation. -/
def pushoutData (h : IsPushout i f b j) (d : Data i) : Data j where
  retraction := pushoutRetraction h d
  left_inv := pushoutRetraction_left h d
  homotopy := {
    toFun := fun p => (pushoutTrack h d).hom (p.2, p.1)
    continuous_toFun := (pushoutTrack h d).hom.continuous.comp (by fun_prop)
    map_zero_left := fun x => congrArg (fun f => f.hom x) (pushoutTrack_zero h d)
    map_one_left := fun x => congrArg (fun f => f.hom x) (pushoutTrack_one h d)
    prop' := by
      intro t y hy
      obtain ⟨x, rfl⟩ := hy
      have ht := congrArg (fun f => f.hom (x, t)) (pushoutTrack_inr h d)
      have hr := congrArg (fun f => f.hom x) (pushoutRetraction_left h d)
      exact ht.trans (congrArg j.hom hr).symm }

/-- The weak test for the pushout follows directly from the glued deformation. -/
theorem pushout_weak (h : IsPushout i f b j) (d : Data i) :
    topologicalWeakEquivalences j := by
  let e := pushoutData h d
  apply weakEquivalence_of_strongDeformationRetract j.hom e.retraction.hom _ e.homotopy
  exact congrArg TopCat.Hom.hom e.left_inv

end

end Thomason.Construction.TopologicalDeformation

end

section

/-! # Arbitrary horn attachments are actual realization weak equivalences

Realization preserves the simplicial pushout. The actual realized horn
inclusion has the constructed stationary deformation, which extends over
that pushout. No model category or anodyne identification is used.
-/

namespace Thomason.Construction

open CategoryTheory
open scoped Simplicial

noncomputable section

/-- The constructed strong deformation data for a realized horn inclusion. -/
def realizedHornData {n : ℕ} (i : Fin (n+2)) :
    TopologicalDeformation.Data (SSet.toTop.map (Λ[n+1, i].ι : _ ⟶ (Δ[n+1] : SSet.{0}))) where
  retraction := TopCat.ofHom (HornBarycentric.realizedRetraction i)
  left_inv := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    exact HornBarycentric.realizedRetraction_left i
  homotopy := HornBarycentric.realizedDeformation i

/-- Attaching any simplex along any horn gives an actual realization weak equivalence. -/
theorem horn_attachment_weak {n : ℕ} (i : Fin (n+2))
    {X P : SSet.{0}} {f : (Λ[n+1, i] : SSet.{0}) ⟶ X}
    {b : (Δ[n+1] : SSet.{0}) ⟶ P} {j : X ⟶ P}
    (h : IsPushout Λ[n+1, i].ι f b j) : realizationWeakEquivalences j :=
  TopologicalDeformation.pushout_weak (SSet.toTop.map_isPushout h) (realizedHornData i)

/-- The entire cobase-change closure of the generating horn family is weak. -/
theorem horn_pushouts_weak :
    SSet.modelCategoryQuillen.J.{0}.pushouts ≤ realizationWeakEquivalences := by
  intro X P j hj
  obtain ⟨A, B, q, f, b, hq, h⟩ := hj
  simp only [SSet.modelCategoryQuillen.J, CategoryTheory.MorphismProperty.iSup_iff] at hq
  obtain ⟨n, ⟨i⟩⟩ := hq
  exact horn_attachment_weak i h.flip

end

end Thomason.Construction

end

end OAI
