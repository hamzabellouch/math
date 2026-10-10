import Mathlib
import OAI.CategoryTheory.Thomason.HomotopyExtension

namespace OAI

/-! Subdivided Unit. -/

noncomputable section
universe u v w z


namespace Thomason.HornSubdivision
open CategoryTheory Simplicial PartialOrder Subdivision

noncomputable def sdSimplexSubcomplexIso {m : ℕ}
    (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    SSet.sd.obj (K : SSet.{u}) ≅ nerve (AllowedChains (orderedSimplexSubcomplex K)) :=
  SSet.sd.mapIso (orderedSimplexSubcomplexIso K) ≪≫ sdSubcomplexIso (orderedSimplexSubcomplex K)

noncomputable def sdSimplexIso (m : ℕ) :
    SSet.sd.obj (SSet.stdSimplex.{u}.obj ⦋m⦌) ≅
      nerve (NonemptyFiniteChains (ULift.{u} (Fin (m+1)))) :=
  SSet.sd.mapIso (SSet.stdSimplex.isoNerve.{u} m) ≪≫ sdNerveIso

lemma sdSimplexSubcomplexIso_naturality {m : ℕ}
    (K : (SSet.stdSimplex.{u}.obj ⦋m⦌).Subcomplex) :
    SSet.sd.map K.ι ≫ (sdSimplexIso m).hom =
      (sdSimplexSubcomplexIso K).hom ≫ allowedChainsForget (orderedSimplexSubcomplex K) := by
  change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
  simp only [Functor.mapIso_hom]
  erw [← Category.assoc, ← Functor.map_comp]
  have he : K.ι ≫ (SSet.stdSimplex.isoNerve.{u} m).hom =
      (orderedSimplexSubcomplexIso K).hom ≫ (orderedSimplexSubcomplex K).ι := rfl
  erw [he, Functor.map_comp, Category.assoc, sdSubcomplexMap_naturality, ← Category.assoc]

theorem sd_horn_anodyne {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) :
    SSet.anodyneExtensions (SSet.sd.map (SSet.horn.{u} n k).ι) := by
  let e := PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (α := PartOrd.of (AllowedChains (orderedSimplexSubcomplex (SSet.horn n k))))
      (β := PartOrd.of (HornFaces.{u} n k)) (hornFacesIso k))
  have he : e.hom ≫ nerveMap (OrderHom.Subtype.val
      (fun chain : NonemptyFiniteChains (ULift.{u} (Fin (n+1))) =>
        chain ∈ HornFaces.{u} n k)).toFunctor =
      allowedChainsForget (orderedSimplexSubcomplex (SSet.horn n k)) := rfl
  have h := SSet.anodyneExtensions.comp_mem e.hom _ (SSet.anodyneExtensions.of_isIso _) (hornFaceInclusion_anodyne hn k)
  rw [he] at h
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff (Arrow.isoMk
    (sdSimplexSubcomplexIso (SSet.horn n k)) (sdSimplexIso n)
    (sdSimplexSubcomplexIso_naturality (SSet.horn n k)).symm)).mpr h

theorem ex_preserves_fibrations {X Y : SSet.{u}} (p : X ⟶ Y) (hp : simplicialFibrations p) :
    simplicialFibrations (SSet.ex.map p) := by
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  exact (SSet.sdExAdjunction.hasLiftingProperty_iff _ p).mp
    (sd_horn_anodyne (by omega) k p hp)

theorem sd_preserves_anodyne {A B : SSet.{u}} (i : A ⟶ B) (hi : SSet.anodyneExtensions i) :
    SSet.anodyneExtensions (SSet.sd.map i) := by
  intro X Y p hp
  exact (SSet.sdExAdjunction.hasLiftingProperty_iff i p).mpr
    (hi (SSet.ex.map p) (ex_preserves_fibrations p hp))

lemma sdTwice_horn_anodyne {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) :
    SSet.anodyneExtensions ((SSet.sd ⋙ SSet.sd).map (SSet.horn.{u} n k).ι) :=
  sd_preserves_anodyne _ (sd_horn_anodyne hn k)
end Thomason.HornSubdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision
open CategoryTheory

def LastVertexStatement : Prop :=
  ∀ X : SSet.{u}, simplicialWeakEquivalences (lastVertex.app X)
end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.LastVertexProof
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

def Homotopic {A B : SSet.{u}} (f g : A ⟶ B) : Prop :=
  Relation.EqvGen (fun f g : A ⟶ B => Nonempty (SSet.Homotopy f g)) f g

lemma homotopic_of_homotopy {A B : SSet.{u}} {f g : A ⟶ B} (H : SSet.Homotopy f g) :
    Homotopic f g := .rel _ _ ⟨H⟩

lemma homotopic_refl {A B : SSet.{u}} (f : A ⟶ B) : Homotopic f f := .refl _
lemma homotopic_symm {A B : SSet.{u}} {f g : A ⟶ B} (H : Homotopic f g) :
    Homotopic g f := .symm _ _ H
lemma homotopic_trans {A B : SSet.{u}} {f g h : A ⟶ B}
    (H : Homotopic f g) (H' : Homotopic g h) : Homotopic f h := .trans _ _ _ H H'

noncomputable def homotopy_pre {A B C : SSet.{u}} (k : A ⟶ B) {f g : B ⟶ C}
    (H : SSet.Homotopy f g) : SSet.Homotopy (k ≫ f) (k ≫ g) :=
  CoherentGluing.toHomotopy ((k ▷ Δ[1]) ≫ H.h)
    (by rw [SSet.ι₀_comp_assoc, H.h₀])
    (by rw [SSet.ι₁_comp_assoc, H.h₁])

noncomputable def homotopy_post {A B C : SSet.{u}} {f g : A ⟶ B}
    (H : SSet.Homotopy f g) (k : B ⟶ C) : SSet.Homotopy (f ≫ k) (g ≫ k) :=
  CoherentGluing.toHomotopy (H.h ≫ k) (by simp) (by simp)

lemma homotopic_pre {A B C : SSet.{u}} (k : A ⟶ B) {f g : B ⟶ C}
    (H : Homotopic f g) : Homotopic (k ≫ f) (k ≫ g) := by
  induction H with
  | rel f g H => exact homotopic_of_homotopy (homotopy_pre k H.some)
  | refl f => exact homotopic_refl _
  | symm f g _ ih => exact homotopic_symm ih
  | trans f g h _ _ ih ih' => exact homotopic_trans ih ih'

lemma homotopic_post {A B C : SSet.{u}} {f g : A ⟶ B}
    (H : Homotopic f g) (k : B ⟶ C) : Homotopic (f ≫ k) (g ≫ k) := by
  induction H with
  | rel f g H => exact homotopic_of_homotopy (homotopy_post H.some k)
  | refl f => exact homotopic_refl _
  | symm f g _ ih => exact homotopic_symm ih
  | trans f g h _ _ ih ih' => exact homotopic_trans ih ih'

lemma homotopic_weak_iff {A B : SSet.{u}} {f g : A ⟶ B} (H : Homotopic f g) :
    simplicialWeakEquivalences f ↔ simplicialWeakEquivalences g := by
  induction H with
  | rel f g H => exact simplicialWeakEquivalences_homotopy H.some
  | refl f => rfl
  | symm f g _ ih => exact ih.symm
  | trans f g h _ _ ih ih' => exact ih.trans ih'

def intervalEnds : SimplicialCylinder.Ends (Δ[0] : SSet.{u}) ⟶ Δ[1] :=
  SimplicialCylinder.endsMap (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0))
    (SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1))

instance intervalEnds_mono : Mono (intervalEnds.{u}) := by
  rw [NatTrans.mono_iff_mono_app]
  intro k
  rw [CategoryTheory.mono_iff_injective]
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      apply congrArg Sum.inl
      apply SSet.stdSimplex.ext
      intro j
      apply Fin.ext
      omega
    | inr b =>
      have h := congrArg (fun z : (Δ[1] : SSet).obj k => SSet.stdSimplex.asOrderHom z 0) hab
      exact (zero_ne_one h).elim
  | inr a =>
    cases b with
    | inl b =>
      have h := congrArg (fun z : (Δ[1] : SSet).obj k => SSet.stdSimplex.asOrderHom z 0) hab
      exact (one_ne_zero h).elim
    | inr b =>
      apply congrArg Sum.inr
      apply SSet.stdSimplex.ext
      intro j
      apply Fin.ext
      omega

def endsTensorMap {A B : SSet.{u}} (f g : A ⟶ B) :
    A ⊗ SimplicialCylinder.Ends Δ[0] ⟶ B where
  app k := ↾fun x => match x.2 with
    | Sum.inl _ => f.app k x.1
    | Sum.inr _ => g.app k x.1
  naturality k l a := by
    ext x
    rcases x with ⟨x, y⟩
    cases y with
    | inl y => exact NatTrans.naturality_apply f a x
    | inr y => exact NatTrans.naturality_apply g a x

lemma homotopy_of_anodyne_eq {A B K : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) [SSet.KanComplex K]
    (f g : B ⟶ K) (h : i ≫ f = i ≫ g) : Nonempty (SSet.Homotopy f g) := by
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i intervalEnds
  let H : A ⊗ Δ[1] ⟶ K := fst _ _ ≫ i ≫ f
  have hc : i ▷ SimplicialCylinder.Ends Δ[0] ≫ endsTensorMap f g = A ◁ intervalEnds ≫ H := by
    ext k x
    rcases x with ⟨x,y⟩
    cases y with
    | inl y => rfl
    | inr y => exact (congrArg (fun t : A ⟶ K => t.app k x) h).symm
  let a : s.pt ⟶ K := s.isPushout.desc (endsTensorMap f g) H hc
  have : HasLiftingProperty s.ι (terminal.from K) :=
    SSet.anodyneExtensions_pushoutObjObjι' s hi (terminal.from K)
      (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  let lsq : CommSq a s.ι (terminal.from K) (terminal.from (B ⊗ Δ[1])) := ⟨by simp⟩
  have he : B ◁ intervalEnds ≫ lsq.lift = endsTensorMap f g := by
    have hj : s.inl ≫ s.ι = B ◁ intervalEnds := s.inl_ι
    rw [← hj, Category.assoc, lsq.fac_left]
    exact s.isPushout.inl_desc _ _ _
  refine ⟨CoherentGluing.toHomotopy lsq.lift ?_ ?_⟩
  · ext k x
    have he' := congrArg (fun t => t.app k (x, Sum.inl (SSet.stdSimplex.objMk (OrderHom.const _ 0)))) he
    exact he'
  · ext k x
    have he' := congrArg (fun t => t.app k (x, Sum.inr (SSet.stdSimplex.objMk (OrderHom.const _ 0)))) he
    exact he'

lemma extend_anodyne {A B K : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) [SSet.KanComplex K] (f : A ⟶ K) :
    ∃ g : B ⟶ K, i ≫ g = f := by
  have : HasLiftingProperty i (terminal.from K) := hi (terminal.from K)
    (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)
  let s : CommSq f i (terminal.from K) (terminal.from B) := ⟨by simp⟩
  exact ⟨s.lift, s.fac_left⟩

lemma ex_kan (K : SSet.{u}) [SSet.KanComplex K] : SSet.KanComplex (SSet.ex.obj K) := by
  rw [SSet.KanComplex.iff]
  intro n k f hf
  obtain ⟨g,hg⟩ := extend_anodyne (SSet.sd.map (SSet.horn (n+1) k).ι)
    (HornSubdivision.sd_horn_anodyne (by omega) k)
    ((SSet.sdExAdjunction.homEquiv _ K).symm hf.desc)
  let g' := (SSet.sdExAdjunction.homEquiv _ K) g
  have hg' : (SSet.horn (n+1) k).ι ≫ g' = hf.desc := by
    rw [show g' = (SSet.sdExAdjunction.homEquiv _ K) g from rfl,
      ← SSet.sdExAdjunction.homEquiv_naturality_left, hg]
    exact (SSet.sdExAdjunction.homEquiv _ K).apply_symm_apply _
  refine ⟨g', fun j hj => ?_⟩
  have h := congrArg (fun t => SSet.horn.ι k j hj ≫ t) hg'
  simpa only [← Category.assoc, SSet.horn.ι_ι, SSet.horn.IsCompatible.ι_desc] using h

noncomputable def sdCylinderMap (X : SSet.{u}) :
    SSet.sd.obj (X ⊗ Δ[1]) ⟶ SSet.sd.obj X ⊗ Δ[1] :=
  lift (SSet.sd.map (fst _ _)) (SSet.sd.map (snd _ _) ≫ Subdivision.lastVertex.app Δ[1])

lemma sdCylinderMap_zero (X : SSet.{u}) :
    SSet.sd.map (SSet.ι₀ (X := X)) ≫ sdCylinderMap X = SSet.ι₀ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, sdCylinderMap, lift_fst, ← Functor.map_comp,
      SSet.ι₀_fst, CategoryTheory.Functor.map_id]
  · simp only [Category.assoc, sdCylinderMap, lift_snd]
    rw [← Category.assoc, ← Functor.map_comp, Subdivision.lastVertex.naturality]
    rw [SSet.ι₀_snd, SSet.ι₀_snd]
    rfl

lemma sdCylinderMap_one (X : SSet.{u}) :
    SSet.sd.map (SSet.ι₁ (X := X)) ≫ sdCylinderMap X = SSet.ι₁ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, sdCylinderMap, lift_fst, ← Functor.map_comp,
      SSet.ι₁_fst, CategoryTheory.Functor.map_id]
  · simp only [Category.assoc, sdCylinderMap, lift_snd]
    rw [← Category.assoc, ← Functor.map_comp, Subdivision.lastVertex.naturality]
    rw [SSet.ι₁_snd, SSet.ι₁_snd]
    rfl

noncomputable def mateHomotopy {X K : SSet.{u}} {f g : SSet.sd.obj X ⟶ K}
    (H : SSet.Homotopy f g) :
    SSet.Homotopy ((SSet.sdExAdjunction.homEquiv X K) f)
      ((SSet.sdExAdjunction.homEquiv X K) g) :=
  CoherentGluing.toHomotopy
    ((SSet.sdExAdjunction.homEquiv _ K) (sdCylinderMap X ≫ H.h))
    (by rw [← SSet.sdExAdjunction.homEquiv_naturality_left,
      ← Category.assoc, sdCylinderMap_zero, H.h₀])
    (by rw [← SSet.sdExAdjunction.homEquiv_naturality_left,
      ← Category.assoc, sdCylinderMap_one, H.h₁])

lemma mate_homotopic {X K : SSet.{u}} {f g : SSet.sd.obj X ⟶ K}
    (H : Homotopic f g) :
    Homotopic ((SSet.sdExAdjunction.homEquiv X K) f)
      ((SSet.sdExAdjunction.homEquiv X K) g) := by
  induction H with
  | rel f g H => exact homotopic_of_homotopy (mateHomotopy H.some)
  | refl f => exact homotopic_refl _
  | symm f g _ ih => exact homotopic_symm ih
  | trans f g h _ _ ih ih' => exact homotopic_trans ih ih'

lemma unmate_homotopy {X K : SSet.{u}} [SSet.KanComplex K]
    {f g : X ⟶ SSet.ex.obj K} (H : SSet.Homotopy f g) :
    Nonempty (SSet.Homotopy ((SSet.sdExAdjunction.homEquiv X K).symm f)
      ((SSet.sdExAdjunction.homEquiv X K).symm g)) := by
  let h := (SSet.sdExAdjunction.homEquiv (X ⊗ Δ[1]) K).symm H.h
  let f' := (SSet.sdExAdjunction.homEquiv X K).symm f
  let g' := (SSet.sdExAdjunction.homEquiv X K).symm g
  have h₀ : SSet.sd.map (SSet.ι₀ (X := X)) ≫ h = f' := by
    dsimp only [h, f']
    rw [← SSet.sdExAdjunction.homEquiv_naturality_left_symm, H.h₀]
  have h₁ : SSet.sd.map (SSet.ι₁ (X := X)) ≫ h = g' := by
    dsimp only [h, g']
    rw [← SSet.sdExAdjunction.homEquiv_naturality_left_symm, H.h₁]
  let p := SSet.sd.map (fst X Δ[1])
  have hp₀ : SSet.sd.map (SSet.ι₀ (X := X)) ≫ p = 𝟙 _ := by
    dsimp only [p]
    rw [← Functor.map_comp, SSet.ι₀_fst, CategoryTheory.Functor.map_id]
  have hp₁ : SSet.sd.map (SSet.ι₁ (X := X)) ≫ p = 𝟙 _ := by
    dsimp only [p]
    rw [← Functor.map_comp, SSet.ι₁_fst, CategoryTheory.Functor.map_id]
  obtain ⟨Q⟩ := homotopy_of_anodyne_eq (SSet.sd.map (SSet.ι₀ (X := X)))
    (HornSubdivision.sd_preserves_anodyne _ (SimplicialCylinder.endpoint_anodyne X).1)
    (p ≫ f') h (by rw [← Category.assoc, hp₀, Category.id_comp, h₀])
  have R := homotopy_pre (SSet.sd.map (SSet.ι₁ (X := X))) Q
  rw [← Category.assoc, hp₁, Category.id_comp, h₁] at R
  exact ⟨R⟩

lemma unmate_homotopic {X K : SSet.{u}} [SSet.KanComplex K]
    {f g : X ⟶ SSet.ex.obj K} (H : Homotopic f g) :
    Homotopic ((SSet.sdExAdjunction.homEquiv X K).symm f)
      ((SSet.sdExAdjunction.homEquiv X K).symm g) := by
  induction H with
  | rel f g H => exact homotopic_of_homotopy (unmate_homotopy H.some).some
  | refl f => exact homotopic_refl _
  | symm f g _ ih => exact homotopic_symm ih
  | trans f g h _ _ ih ih' => exact homotopic_trans ih ih'

lemma ex_retract (K : SSet.{u}) [SSet.KanComplex K] :
    ∃ r : SSet.ex.obj K ⟶ K, Subdivision.exComparison.app K ≫ r = 𝟙 K ∧
      Homotopic (r ≫ Subdivision.exComparison.app K) (𝟙 _) := by
  obtain ⟨r,hr⟩ := extend_anodyne (Subdivision.exComparison.app K)
    (Subdivision.exComparison_anodyne K) (𝟙 K)
  let := ex_kan K
  obtain ⟨H⟩ := homotopy_of_anodyne_eq (Subdivision.exComparison.app K)
    (Subdivision.exComparison_anodyne K) (r ≫ Subdivision.exComparison.app K) (𝟙 _)
    (by rw [← Category.assoc, hr]; simp)
  exact ⟨r, hr, homotopic_of_homotopy H⟩

lemma mate_lastVertex {X K : SSet.{u}} (f : X ⟶ K) :
    (SSet.sdExAdjunction.homEquiv X K) (Subdivision.lastVertex.app X ≫ f) =
      f ≫ Subdivision.exComparison.app K := by
  have hn : SSet.sd.map f ≫ Subdivision.lastVertex.app K =
      Subdivision.lastVertex.app X ≫ f := Subdivision.lastVertex.naturality f
  rw [← hn, SSet.sdExAdjunction.homEquiv_naturality_left]
  rfl

lemma precomp_lastVertex_surjective (X K : SSet.{u}) [SSet.KanComplex K]
    (g : SSet.sd.obj X ⟶ K) :
    ∃ f : X ⟶ K, Homotopic (Subdivision.lastVertex.app X ≫ f) g := by
  obtain ⟨r,hr,Hr⟩ := ex_retract K
  let g' := (SSet.sdExAdjunction.homEquiv X K) g
  refine ⟨g' ≫ r, ?_⟩
  have H := homotopic_pre g' Hr
  simp only [Category.comp_id, ← Category.assoc] at H
  rw [← mate_lastVertex (g' ≫ r)] at H
  have Q := unmate_homotopic H
  dsimp only [g'] at Q
  simpa only [Equiv.symm_apply_apply] using Q

lemma precomp_lastVertex_injective (X K : SSet.{u}) [SSet.KanComplex K]
    (f g : X ⟶ K) (H : Homotopic (Subdivision.lastVertex.app X ≫ f)
      (Subdivision.lastVertex.app X ≫ g)) : Homotopic f g := by
  obtain ⟨r,hr,Hr⟩ := ex_retract K
  have H' := mate_homotopic H
  rw [mate_lastVertex, mate_lastVertex] at H'
  have Q := homotopic_post H' r
  simpa only [Category.assoc, hr, Category.comp_id] using Q

lemma lastVertex_weak (X : SSet.{u}) :
    simplicialWeakEquivalences (Subdivision.lastVertex.app X) := by
  let A := SSet.sd.obj X
  let R := Subdivision.exInfinityFunctor
  let eA : A ⟶ R.obj A := Subdivision.exInfinityComparison A
  let eX : X ⟶ R.obj X := Subdivision.exInfinityComparison X
  let l := Subdivision.lastVertex.app X
  let : SSet.KanComplex (R.obj A) := Subdivision.exInfinity_kan A
  let : SSet.KanComplex (R.obj X) := Subdivision.exInfinity_kan X
  obtain ⟨t, Ht⟩ := precomp_lastVertex_surjective X (R.obj A) eA
  have Ht' := homotopic_post Ht (R.map l)
  have he : eA ≫ R.map l = l ≫ eX :=
    Subdivision.exInfinityInclusion_naturality l 0
  rw [he, Category.assoc] at Ht'
  have H := precomp_lastVertex_injective X (R.obj X) (t ≫ R.map l) eX Ht'
  have hlt : simplicialWeakEquivalences (l ≫ t) :=
    (homotopic_weak_iff Ht).mpr (Subdivision.exInfinityComparison_weak A)
  have htr : simplicialWeakEquivalences (t ≫ R.map l) :=
    (homotopic_weak_iff H).mpr (Subdivision.exInfinityComparison_weak X)
  exact simplicialWeakEquivalences.of_postcomp l t
    (simplicialWeakEquivalences_middle l t (R.map l) hlt htr) hlt

end Thomason.LastVertexProof

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision
open CategoryTheory

theorem lastVertex_weak : LastVertexStatement.{u} := LastVertexProof.lastVertex_weak

lemma sd_map_weak_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    simplicialWeakEquivalences (SSet.sd.map f) ↔ simplicialWeakEquivalences f := by
  have he : SSet.sd.map f ≫ lastVertex.app Y = lastVertex.app X ≫ f :=
    lastVertex.naturality f
  constructor
  · intro h
    exact simplicialWeakEquivalences.of_precomp (lastVertex.app X) f
      (lastVertex_weak X)
      (he ▸ simplicialWeakEquivalences.comp_mem _ _ h (lastVertex_weak Y))
  · intro h
    exact simplicialWeakEquivalences.of_postcomp (SSet.sd.map f) (lastVertex.app Y)
      (lastVertex_weak Y)
      (he.symm ▸ simplicialWeakEquivalences.comp_mem _ _ (lastVertex_weak X) h)
end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.SubdividedUnit
open CategoryTheory

def OneStatement : Prop := ∀ K : SSet.{u},
  simplicialWeakEquivalences
    ((categorificationFiniteAdjunction 1).unit.app (SSet.sd.obj (SSet.sd.obj K)))
end Thomason.SubdividedUnit

end

noncomputable section
universe u v w z


namespace Thomason.KanHomotopy
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory
open HornSubdivision LastVertexProof

def sides {A K : SSet.{u}} (f g : A ⊗ Δ[1] ⟶ K) :
    SimplicialCylinder.Ends A ⊗ Δ[1] ⟶ K where
  app n := ↾fun x => match x.1 with
    | Sum.inl a => f.app n (a,x.2)
    | Sum.inr a => g.app n (a,x.2)
  naturality n m θ := by
    ext x
    rcases x with ⟨x,t⟩
    cases x with
    | inl x => exact congrArg (fun q : (A ⊗ Δ[1]).obj n ⟶ K.obj m => q (x,t)) (f.naturality θ)
    | inr x => exact congrArg (fun q : (A ⊗ Δ[1]).obj n ⟶ K.obj m => q (x,t)) (g.naturality θ)

lemma endpoint_sides {A K : SSet.{u}} (f g : A ⊗ Δ[1] ⟶ K) (j : Fin 2) :
    endpoint (SimplicialCylinder.Ends A) j ≫ sides f g =
      SimplicialCylinder.endsMap (endpoint A j ≫ f) (endpoint A j ≫ g) := by
  ext n x
  cases x <;> rfl

lemma ends_sides_post {A K L : SSet.{u}} (f g : A ⊗ Δ[1] ⟶ K) (p : K ⟶ L) :
    sides f g ≫ p = sides (f ≫ p) (g ≫ p) := by
  ext n x
  rcases x with ⟨x,t⟩
  cases x <;> rfl

lemma ends_pre {A K : SSet.{u}} (b : A ⊗ Δ[1] ⟶ K) :
    SimplicialCylinder.endsInclusion A ≫ b =
      SimplicialCylinder.endsMap (SSet.ι₀ ≫ b) (SSet.ι₁ ≫ b) := by
  ext n x
  cases x <;> rfl

lemma square_top_zero {A K : SSet.{u}}
    (Q : (A ⊗ Δ[1]) ⊗ Δ[1] ⟶ K) (l r : A ⊗ Δ[1] ⟶ K)
    (h : SimplicialCylinder.endsInclusion A ▷ Δ[1] ≫ Q = sides l r) :
    SSet.ι₀ ≫ SSet.ι₁ ≫ Q = SSet.ι₁ ≫ l := by
  ext n x
  exact congrArg (fun f => f.app n (Sum.inl x, SSet.stdSimplex.const _ 1 _)) h

lemma square_top_one {A K : SSet.{u}}
    (Q : (A ⊗ Δ[1]) ⊗ Δ[1] ⟶ K) (l r : A ⊗ Δ[1] ⟶ K)
    (h : SimplicialCylinder.endsInclusion A ▷ Δ[1] ≫ Q = sides l r) :
    SSet.ι₁ ≫ SSet.ι₁ ≫ Q = SSet.ι₁ ≫ r := by
  ext n x
  exact congrArg (fun f => f.app n (Sum.inr x, SSet.stdSimplex.const _ 1 _)) h

lemma fill_rectangle {A K : SSet.{u}} [SSet.KanComplex K]
    {a b c d : A ⟶ K} (bottom : SSet.Homotopy a b)
    (left : SSet.Homotopy a c) (right : SSet.Homotopy b d) :
    Nonempty (SSet.Homotopy c d) := by
  have hp : simplicialFibrations (terminal.from K) := by
    change SSet.modelCategoryQuillen.J.rlp (terminal.from K)
    rw [← SSet.modelCategoryQuillen.fibrations_eq, ← HomotopicalAlgebra.fibration_iff]
    infer_instance
  obtain ⟨Q,hQ,_,_⟩ := cylinder_lift (SimplicialCylinder.endsInclusion A)
    (terminal.from K) hp 1 bottom.h (sides left.h right.h) (terminal.from _)
    (by rw [endpoint_sides, endpoint_zero, left.h₀, right.h₀,
      ends_pre, bottom.h₀, bottom.h₁])
    (by subsingleton) (by subsingleton)
  refine ⟨CoherentGluing.toHomotopy (SSet.ι₁ ≫ Q) ?_ ?_⟩
  · exact (square_top_zero Q left.h right.h hQ).trans left.h₁
  · exact (square_top_one Q left.h right.h hQ).trans right.h₁

def refl {A K : SSet.{u}} (a : A ⟶ K) : SSet.Homotopy a a :=
  CoherentGluing.toHomotopy (fst A Δ[1] ≫ a) (by simp) (by simp)

lemma homotopy_symm {A K : SSet.{u}} [SSet.KanComplex K]
    {a b : A ⟶ K} (H : SSet.Homotopy a b) : Nonempty (SSet.Homotopy b a) :=
  fill_rectangle (refl a) H (refl a)

lemma homotopy_trans {A K : SSet.{u}} [SSet.KanComplex K]
    {a b c : A ⟶ K} (H : SSet.Homotopy a b) (H' : SSet.Homotopy b c) :
    Nonempty (SSet.Homotopy a c) := fill_rectangle H (refl a) H'

lemma homotopy_of_homotopic {A K : SSet.{u}} [SSet.KanComplex K]
    {a b : A ⟶ K} (H : Homotopic a b) : Nonempty (SSet.Homotopy a b) := by
  induction H with
  | rel f g H => exact H
  | refl f => exact ⟨refl f⟩
  | symm f g _ ih => exact homotopy_symm ih.some
  | trans f g h _ _ ih ih' => exact homotopy_trans ih.some ih'.some

def maxSquare (A : SSet.{u}) : (A ⊗ Δ[1]) ⊗ Δ[1] ⟶ A ⊗ Δ[1] where
  app n := ↾fun x => (x.1.1, SSet.stdSimplex.objMk
    (SSet.stdSimplex.asOrderHom x.1.2 ⊔ SSet.stdSimplex.asOrderHom x.2))
  naturality n m θ := by
    ext x
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro j
      rfl

@[reassoc] lemma maxSquare_bottom (A : SSet.{u}) : SSet.ι₀ ≫ maxSquare A = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    change max (_ : Fin 2) 0 = _
    exact max_eq_left (Fin.zero_le _)

@[reassoc] lemma maxSquare_top (A : SSet.{u}) :
    SSet.ι₁ ≫ maxSquare A = fst A Δ[1] ≫ SSet.ι₁ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    change max (_ : Fin 2) 1 = 1
    exact max_eq_right (Fin.is_le _)

lemma maxSquare_sides (A : SSet.{u}) :
    SimplicialCylinder.endsInclusion A ▷ Δ[1] ≫ maxSquare A =
      sides (𝟙 _) (fst A Δ[1] ≫ SSet.ι₁) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨x,t⟩
  cases x with
  | inl x =>
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro j
      change max 0 (_ : Fin 2) = _
      exact max_eq_right (Fin.zero_le _)
  | inr x =>
    apply Prod.ext
    · rfl
    · apply SSet.stdSimplex.ext
      intro j
      change max 1 (_ : Fin 2) = 1
      exact max_eq_left (Fin.is_le _)

lemma verticalize {X Y : SSet.{u}} (p : X ⟶ Y) (hp : simplicialFibrations p)
    (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y)
    (H : SSet.Homotopy (p ≫ s) (𝟙 X)) :
    ∃ (Q : SSet.Homotopy (p ≫ s) (𝟙 X)), Q.h ≫ p = fst X Δ[1] ≫ p := by
  let l := H.h ≫ p ≫ s
  let r := fst X Δ[1]
  have hl₀ : SSet.ι₀ ≫ l = p ≫ s := by
    dsimp only [l]
    rw [H.h₀_assoc, Category.assoc, ← Category.assoc s p, hs, Category.id_comp]
  have hl₁ : SSet.ι₁ ≫ l = p ≫ s := by
    dsimp only [l]
    rw [H.h₁_assoc, Category.id_comp]
  have hc : sides l r ≫ p = SimplicialCylinder.endsInclusion X ▷ Δ[1] ≫
      (maxSquare X ≫ H.h ≫ p) := by
    rw [ends_sides_post, ← Category.assoc, maxSquare_sides, Category.assoc,
      ends_sides_post]
    congr 1
    · simp only [Category.assoc, hs, Category.comp_id, Category.id_comp]
    · dsimp only [r]
      simp only [Category.assoc, H.h₁_assoc, Category.id_comp]
  obtain ⟨Q,hQ,_,hQp⟩ := cylinder_lift (SimplicialCylinder.endsInclusion X)
    p hp 1 H.h (sides l r) (maxSquare X ≫ H.h ≫ p)
    (by rw [endpoint_sides, endpoint_zero, hl₀, show SSet.ι₀ ≫ r = 𝟙 X from by
          dsimp only [r]; simp, ends_pre, H.h₀, H.h₁])
    (by rw [endpoint_zero, maxSquare_bottom_assoc]) hc
  have hz : SSet.ι₀ ≫ SSet.ι₁ ≫ Q = p ≫ s :=
    (square_top_zero Q l r hQ).trans hl₁
  have ho : SSet.ι₁ ≫ SSet.ι₁ ≫ Q = 𝟙 X := by
    rw [square_top_one Q l r hQ]
    dsimp only [r]
    simp
  refine ⟨CoherentGluing.toHomotopy (SSet.ι₁ ≫ Q) hz ho, ?_⟩
  change (SSet.ι₁ ≫ Q) ≫ p = _
  rw [Category.assoc, hQp, ← Category.assoc, maxSquare_top, Category.assoc,
    H.h₁_assoc, Category.id_comp]

lemma rlp_of_vertical_retract {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : simplicialFibrations p) (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y)
    (H : SSet.Homotopy (p ≫ s) (𝟙 X)) (hH : H.h ≫ p = fst X Δ[1] ≫ p) :
    (MorphismProperty.monomorphisms SSet).rlp p := by
  intro A B i hi
  let : Mono i := hi
  constructor
  intro a b sq
  obtain ⟨Q,hQ,hQ₀,hQp⟩ := cylinder_lift i p hp 1 (b ≫ s)
    (a ▷ Δ[1] ≫ H.h) (fst B Δ[1] ≫ b)
    (by rw [endpoint_zero, SSet.ι₀_comp_assoc, H.h₀];
        simpa only [Category.assoc] using congrArg (· ≫ s) sq.w)
    (by rw [endpoint_zero]; simp [hs])
    (by rw [Category.assoc, hH, ← Category.assoc, whiskerRight_fst,
          Category.assoc, sq.w]; rfl)
  refine ⟨⟨{ l := SSet.ι₁ ≫ Q, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← SSet.ι₁_comp_assoc, hQ, SSet.ι₁_comp_assoc, H.h₁]
    simp
  · rw [Category.assoc, hQp]
    simp

def IsHomotopyEquivalence {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, Homotopic (f ≫ g) (𝟙 X) ∧ Homotopic (g ≫ f) (𝟙 Y)

lemma homotopy_equivalence_weak {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : IsHomotopyEquivalence f) : simplicialWeakEquivalences f := by
  obtain ⟨g,hg,hf⟩ := hf
  have hfg := (homotopic_weak_iff hg).mpr (simplicialWeakEquivalences.id_mem X)
  have hgf := (homotopic_weak_iff hf).mpr (simplicialWeakEquivalences.id_mem Y)
  exact simplicialWeakEquivalences.of_postcomp f g
    (simplicialWeakEquivalences_middle f g f hfg hgf) hfg

lemma rlp_of_homotopy_equivalence {X Y : SSet.{u}}
    [SSet.KanComplex X] [SSet.KanComplex Y]
    (p : X ⟶ Y) (hp : simplicialFibrations p) (he : IsHomotopyEquivalence p) :
    (MorphismProperty.monomorphisms SSet).rlp p := by
  obtain ⟨g,hg,hh⟩ := he
  obtain ⟨H⟩ := homotopy_of_homotopic hh
  have : HasLiftingProperty (SSet.ι₀ (X := Y)) p :=
    (SimplicialCylinder.endpoint_anodyne Y).1 p hp
  let sq : CommSq g SSet.ι₀ p H.h := ⟨H.h₀.symm⟩
  let s := SSet.ι₁ ≫ sq.lift
  have hs : s ≫ p = 𝟙 Y := by
    dsimp only [s]
    rw [Category.assoc, sq.fac_right, H.h₁]
  let Q : SSet.Homotopy g s := CoherentGluing.toHomotopy sq.lift sq.fac_left rfl
  have hs' : Homotopic (p ≫ s) (𝟙 X) := homotopic_trans
    (homotopic_symm (homotopic_pre p (homotopic_of_homotopy Q))) hg
  obtain ⟨T,hT⟩ := verticalize p hp s hs (homotopy_of_homotopic hs').some
  exact rlp_of_vertical_retract p hp s hs T hT

end Thomason.KanHomotopy

end

end OAI
