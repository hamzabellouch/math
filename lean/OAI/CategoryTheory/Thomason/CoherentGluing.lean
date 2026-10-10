import Mathlib
import OAI.CategoryTheory.Thomason.FiniteAttachments
import OAI.CategoryTheory.Thomason.SubdividedUnit

namespace OAI

/-! Coherent Gluing. -/

noncomputable section
universe u v w z


namespace Thomason.KanLocal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial
open LastVertexProof KanHomotopy

lemma heq_id (X : SSet.{u}) : IsHomotopyEquivalence (𝟙 X) :=
  ⟨𝟙 X, by simpa using homotopic_refl (𝟙 X), by simpa using homotopic_refl (𝟙 X)⟩

lemma heq_of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    IsHomotopyEquivalence f := by
  refine ⟨inv f, ?_, ?_⟩ <;> simp only [IsIso.hom_inv_id, IsIso.inv_hom_id]
  · exact homotopic_refl _
  · exact homotopic_refl _

lemma heq_comp {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsHomotopyEquivalence f) (hg : IsHomotopyEquivalence g) :
    IsHomotopyEquivalence (f ≫ g) := by
  obtain ⟨f', hff',hf'f⟩ := hf
  obtain ⟨g', hgg',hg'g⟩ := hg
  refine ⟨g' ≫ f', ?_, ?_⟩
  · have h := homotopic_post (homotopic_pre f hgg') f'
    simp only [Category.comp_id, Category.assoc] at h ⊢
    exact homotopic_trans h hff'
  · have h := homotopic_post (homotopic_pre g' hf'f) g
    simp only [Category.comp_id, Category.assoc] at h ⊢
    exact homotopic_trans h hg'g

lemma heq_homotopic {X Y : SSet.{u}} {f g : X ⟶ Y}
    (h : Homotopic f g) (hf : IsHomotopyEquivalence f) : IsHomotopyEquivalence g := by
  obtain ⟨k,h₀,h₁⟩ := hf
  exact ⟨k, homotopic_trans (homotopic_symm (homotopic_post h k)) h₀,
    homotopic_trans (homotopic_symm (homotopic_pre k h)) h₁⟩

lemma heq_of_rlp {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : (MorphismProperty.monomorphisms SSet).rlp f) : IsHomotopyEquivalence f := by
  have : HasLiftingProperty (initial.to Y) f := hf _ (by infer_instance)
  let sq : CommSq (initial.to X) (initial.to Y) f (𝟙 Y) := ⟨by simp⟩
  let g := sq.lift
  have hg : g ≫ f = 𝟙 Y := sq.fac_right
  have : HasLiftingProperty (SimplicialCylinder.endsInclusion X) f := hf _ (by infer_instance)
  let s : CommSq (SimplicialCylinder.endsMap (f ≫ g) (𝟙 X))
      (SimplicialCylinder.endsInclusion X) f (fst X Δ[1] ≫ f) := ⟨by
    ext n x
    cases x with
    | inl x => exact congrArg (fun q : Y ⟶ Y => (f ≫ q).app n x) hg
    | inr x => rfl⟩
  have h₀ : SSet.ι₀ ≫ s.lift = f ≫ g := by
    ext n x
    exact congrArg (fun q => q.app n (Sum.inl x)) s.fac_left
  have h₁ : SSet.ι₁ ≫ s.lift = 𝟙 X := by
    ext n x
    exact congrArg (fun q => q.app n (Sum.inr x)) s.fac_left
  refine ⟨g, homotopic_of_homotopy (CoherentGluing.toHomotopy s.lift h₀ h₁), ?_⟩
  rw [hg]
  exact homotopic_refl _

lemma pre_rlp_of_anodyne {A B : SSet.{u}} (f : A ⟶ B)
    (hf : SSet.anodyneExtensions f) (K : SSet.{u}) [SSet.KanComplex K] :
    (MorphismProperty.monomorphisms SSet).rlp ((pre f).app K) := by
  intro X Y i hi
  let : Mono i := hi
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) f i
  let pb := Functor.PullbackObjObj.ofIsTerminal
    MonoidalClosed.internalHom f (terminal.from K) terminalIsTerminal
  exact (internalHomAdjunction₂.hasLiftingProperty_iff pp pb).mp
    (SSet.anodyneExtensions_pushoutObjObjι' pp hf (terminal.from K)
      (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance))

def Local {A B : SSet.{u}} (f : A ⟶ B) : Prop :=
  ∀ (K : SSet.{u}), SSet.KanComplex K → IsHomotopyEquivalence ((pre f).app K)

lemma local_anodyne {A B : SSet.{u}} (f : A ⟶ B) (hf : SSet.anodyneExtensions f) :
    Local f := fun K _ => heq_of_rlp _ (pre_rlp_of_anodyne f hf K)

lemma local_iso {A B : SSet.{u}} (f : A ⟶ B) [IsIso f] : Local f := by
  intro K hK
  change IsHomotopyEquivalence ((internalHom.map f.op).app K)
  exact heq_of_isIso _

lemma local_comp {A B C : SSet.{u}} {f : A ⟶ B} {g : B ⟶ C}
    (hf : Local f) (hg : Local g) : Local (f ≫ g) := by
  intro K hK
  simpa only [pre_map, NatTrans.comp_app] using heq_comp (hg K hK) (hf K hK)

def preHomotopyMap {A B K : SSet.{u}} {f g : A ⟶ B} (H : SSet.Homotopy f g) :
    A ⊗ ((ihom B).obj K ⊗ Δ[1]) ⟶ B ⊗ (ihom B).obj K :=
  lift (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ H.h) (snd _ _ ≫ fst _ _)

lemma preHomotopyMap_zero {A B K : SSet.{u}} {f g : A ⟶ B} (H : SSet.Homotopy f g) :
    A ◁ SSet.ι₀ ≫ preHomotopyMap (K := K) H = f ▷ (ihom B).obj K := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, preHomotopyMap, lift_fst]
    have h : A ◁ SSet.ι₀ ≫ lift (fst A _) (snd A _ ≫ snd _ Δ[1]) =
        fst A ((ihom B).obj K) ≫ SSet.ι₀ := by rfl
    rw [← Category.assoc, h, Category.assoc, H.h₀, whiskerRight_fst]
  · rfl

lemma preHomotopyMap_one {A B K : SSet.{u}} {f g : A ⟶ B} (H : SSet.Homotopy f g) :
    A ◁ SSet.ι₁ ≫ preHomotopyMap (K := K) H = g ▷ (ihom B).obj K := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, preHomotopyMap, lift_fst]
    have h : A ◁ SSet.ι₁ ≫ lift (fst A _) (snd A _ ≫ snd _ Δ[1]) =
        fst A ((ihom B).obj K) ≫ SSet.ι₁ := by rfl
    rw [← Category.assoc, h, Category.assoc, H.h₁, whiskerRight_fst]
  · rfl

def preHomotopy {A B : SSet.{u}} {f g : A ⟶ B} (H : SSet.Homotopy f g) (K : SSet.{u}) :
    SSet.Homotopy ((pre f).app K) ((pre g).app K) :=
  CoherentGluing.toHomotopy (curry (preHomotopyMap H ≫ (ihom.ev B).app K))
    (by apply uncurry_injective
        rw [uncurry_natural_left, uncurry_curry, uncurry_pre,
          ← Category.assoc, preHomotopyMap_zero])
    (by apply uncurry_injective
        rw [uncurry_natural_left, uncurry_curry, uncurry_pre,
          ← Category.assoc, preHomotopyMap_one])

lemma homotopic_pre_map {A B : SSet.{u}} {f g : A ⟶ B} (H : Homotopic f g) (K : SSet.{u}) :
    Homotopic ((pre f).app K) ((pre g).app K) := by
  induction H with
  | rel f g H => exact homotopic_of_homotopy (preHomotopy H.some K)
  | refl f => exact homotopic_refl _
  | symm f g _ ih => exact homotopic_symm ih
  | trans f g h _ _ ih ih' => exact homotopic_trans ih ih'

lemma local_homotopic {A B : SSet.{u}} {f g : A ⟶ B} (H : Homotopic f g)
    (hf : Local f) : Local g := fun K hK => heq_homotopic (homotopic_pre_map H K) (hf K hK)

lemma local_heq {A B : SSet.{u}} (f : A ⟶ B) (hf : IsHomotopyEquivalence f) : Local f := by
  intro K hK
  obtain ⟨g,hg,hh⟩ := hf
  refine ⟨(pre g).app K, ?_, ?_⟩
  · simpa only [pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app] using homotopic_pre_map hh K
  · simpa only [pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app] using homotopic_pre_map hg K

def uncurryHomotopy {A T K : SSet.{u}} {f g : T ⟶ (ihom A).obj K}
    (H : SSet.Homotopy f g) : SSet.Homotopy (uncurry f) (uncurry g) :=
  CoherentGluing.toHomotopy ((α_ A T Δ[1]).hom ≫ uncurry H.h)
    (by rw [← Category.assoc]
        change A ◁ SSet.ι₀ ≫ uncurry H.h = _
        rw [← uncurry_natural_left, H.h₀])
    (by rw [← Category.assoc]
        change A ◁ SSet.ι₁ ≫ uncurry H.h = _
        rw [← uncurry_natural_left, H.h₁])

def curryHomotopy {A T K : SSet.{u}} {f g : A ⊗ T ⟶ K}
    (H : SSet.Homotopy f g) : SSet.Homotopy (curry f) (curry g) :=
  CoherentGluing.toHomotopy (curry ((α_ A T Δ[1]).inv ≫ H.h))
    (by apply uncurry_injective
        rw [uncurry_natural_left, uncurry_curry, uncurry_curry, ← Category.assoc]
        change SSet.ι₀ ≫ H.h = f
        exact H.h₀)
    (by apply uncurry_injective
        rw [uncurry_natural_left, uncurry_curry, uncurry_curry, ← Category.assoc]
        change SSet.ι₁ ≫ H.h = g
        exact H.h₁)

lemma homotopic_uncurry {A T K : SSet.{u}} {f g : T ⟶ (ihom A).obj K}
    (H : Homotopic f g) : Homotopic (uncurry f) (uncurry g) := by
  induction H with
  | rel f g H => exact homotopic_of_homotopy (uncurryHomotopy H.some)
  | refl f => exact homotopic_refl _
  | symm f g _ ih => exact homotopic_symm ih
  | trans f g h _ _ ih ih' => exact homotopic_trans ih ih'

lemma homotopic_curry {A T K : SSet.{u}} {f g : A ⊗ T ⟶ K}
    (H : Homotopic f g) : Homotopic (curry f) (curry g) := by
  induction H with
  | rel f g H => exact homotopic_of_homotopy (curryHomotopy H.some)
  | refl f => exact homotopic_refl _
  | symm f g _ ih => exact homotopic_symm ih
  | trans f g h _ _ ih ih' => exact homotopic_trans ih ih'

lemma homotopic_uncurry' {A K : SSet.{u}} {f g : 𝟙_ SSet ⟶ (ihom A).obj K}
    (H : Homotopic f g) : Homotopic (uncurry' f) (uncurry' g) :=
  homotopic_pre (ρ_ A).inv (homotopic_uncurry H)

lemma homotopic_curry' {A K : SSet.{u}} {f g : A ⟶ K}
    (H : Homotopic f g) : Homotopic (curry' f) (curry' g) :=
  homotopic_curry (homotopic_pre (ρ_ A).hom H)

lemma uncurry'_pre {A B K : SSet.{u}} (f : A ⟶ B) (g : 𝟙_ SSet ⟶ (ihom B).obj K) :
    uncurry' (g ≫ (pre f).app K) = f ≫ uncurry' g := by
  simp only [uncurry', uncurry_pre_app]
  rw [← Category.assoc]
  rfl

lemma curry'_pre {A B K : SSet.{u}} (f : A ⟶ B) (g : B ⟶ K) :
    curry' (f ≫ g) = curry' g ≫ (pre f).app K := by
  apply uncurry'_injective
  rw [uncurry'_curry', uncurry'_pre, uncurry'_curry']

lemma precomp_surjective {A B K : SSet.{u}} (f : A ⟶ B) (hf : Local f)
    [SSet.KanComplex K] (a : A ⟶ K) : ∃ b : B ⟶ K, Homotopic (f ≫ b) a := by
  obtain ⟨g,hg,hh⟩ := hf K inferInstance
  refine ⟨uncurry' (curry' a ≫ g), ?_⟩
  have H := homotopic_uncurry' (homotopic_pre (curry' a) hh)
  simpa only [Category.comp_id, ← Category.assoc, uncurry'_pre, uncurry'_curry'] using H

lemma precomp_injective {A B K : SSet.{u}} (f : A ⟶ B) (hf : Local f)
    [SSet.KanComplex K] (a b : B ⟶ K) (H : Homotopic (f ≫ a) (f ≫ b)) : Homotopic a b := by
  obtain ⟨g,hg,hh⟩ := hf K inferInstance
  have H' := homotopic_post (homotopic_curry' H) g
  rw [curry'_pre, curry'_pre] at H'
  have h₀ := homotopic_pre (curry' a) hg
  have h₁ := homotopic_pre (curry' b) hg
  simp only [Category.comp_id, Category.assoc] at H' h₀ h₁
  have Q := homotopic_uncurry' (homotopic_trans (homotopic_symm h₀) (homotopic_trans H' h₁))
  simpa only [uncurry'_curry'] using Q

lemma local_weak {A B : SSet.{u}} (f : A ⟶ B) (hf : Local f) :
    simplicialWeakEquivalences f := by
  let R := Subdivision.exInfinityFunctor
  let eA : A ⟶ R.obj A := Subdivision.exInfinityComparison A
  let eB : B ⟶ R.obj B := Subdivision.exInfinityComparison B
  let : SSet.KanComplex (R.obj A) := Subdivision.exInfinity_kan A
  let : SSet.KanComplex (R.obj B) := Subdivision.exInfinity_kan B
  obtain ⟨t,Ht⟩ := precomp_surjective f hf eA
  have Ht' := homotopic_post Ht (R.map f)
  have he : eA ≫ R.map f = f ≫ eB := Subdivision.exInfinityInclusion_naturality f 0
  rw [he, Category.assoc] at Ht'
  have H := precomp_injective f hf (t ≫ R.map f) eB Ht'
  have hft : simplicialWeakEquivalences (f ≫ t) :=
    (homotopic_weak_iff Ht).mpr (Subdivision.exInfinityComparison_weak A)
  have htr : simplicialWeakEquivalences (t ≫ R.map f) :=
    (homotopic_weak_iff H).mpr (Subdivision.exInfinityComparison_weak B)
  exact simplicialWeakEquivalences.of_postcomp f t
    (simplicialWeakEquivalences_middle f t (R.map f) hft htr) hft

end Thomason.KanLocal

end

noncomputable section
universe u v w z


namespace Thomason.KanLocal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed Simplicial
open LastVertexProof KanHomotopy HornSubdivision
open SSet.modelCategoryQuillen

lemma heq_of_precomp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : IsHomotopyEquivalence f) (hfg : IsHomotopyEquivalence (f ≫ g)) :
    IsHomotopyEquivalence g := by
  obtain ⟨f',h₀,h₁⟩ := hf
  have hf' : IsHomotopyEquivalence f' := ⟨f,h₁,h₀⟩
  have H := homotopic_post h₁ g
  simp only [Category.assoc, Category.id_comp] at H
  exact heq_homotopic H (heq_comp hf' hfg)

lemma heq_of_postcomp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hg : IsHomotopyEquivalence g) (hfg : IsHomotopyEquivalence (f ≫ g)) :
    IsHomotopyEquivalence f := by
  obtain ⟨g',h₀,h₁⟩ := hg
  have hg' : IsHomotopyEquivalence g' := ⟨g,h₁,h₀⟩
  have H := homotopic_pre f h₀
  simp only [Category.comp_id, ← Category.assoc] at H
  exact heq_homotopic H (heq_comp hfg hg')

lemma homotopy_of_anodyne_eq_relative {A B K : SSet.{u}} (i : A ⟶ B)
    (hi : SSet.anodyneExtensions i) [SSet.KanComplex K]
    (f g : B ⟶ K) (h : i ≫ f = i ≫ g) :
    ∃ H : SSet.Homotopy f g, i ▷ Δ[1] ≫ H.h = fst _ _ ≫ i ≫ f := by
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
    have hij : s.inl ≫ s.ι = B ◁ intervalEnds := s.inl_ι
    rw [← hij, Category.assoc, lsq.fac_left]
    exact s.isPushout.inl_desc _ _ _
  let Q : SSet.Homotopy f g := CoherentGluing.toHomotopy lsq.lift
    (by ext k x
        exact congrArg (fun t => t.app k (x, Sum.inl (SSet.stdSimplex.objMk (OrderHom.const _ 0)))) he)
    (by ext k x
        exact congrArg (fun t => t.app k (x, Sum.inr (SSet.stdSimplex.objMk (OrderHom.const _ 0)))) he)
  refine ⟨Q, ?_⟩
  change i ▷ Δ[1] ≫ lsq.lift = H
  have hij : s.inr ≫ s.ι = i ▷ Δ[1] := s.inr_ι
  rw [← hij, Category.assoc, lsq.fac_left]
  exact s.isPushout.inr_desc _ _ _

lemma anodyne_deformation {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (i : X ⟶ Y) (hi : SSet.anodyneExtensions i) :
    ∃ (r : Y ⟶ X) (H : SSet.Homotopy (𝟙 Y) (r ≫ i)),
      i ≫ r = 𝟙 X ∧ i ▷ Δ[1] ≫ H.h = fst _ _ ≫ i := by
  obtain ⟨r,hr⟩ := extend_anodyne i hi (𝟙 X)
  obtain ⟨H,hH⟩ := homotopy_of_anodyne_eq_relative i hi (𝟙 Y) (r ≫ i)
    (by simp [← Category.assoc, hr])
  exact ⟨r,H,hr,by simpa using hH⟩

lemma heq_anodyne {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (i : X ⟶ Y) (hi : SSet.anodyneExtensions i) : IsHomotopyEquivalence i := by
  obtain ⟨r,H,hr,_⟩ := anodyne_deformation i hi
  refine ⟨r, ?_, homotopic_symm (homotopic_of_homotopy H)⟩
  rw [hr]
  exact homotopic_refl _

lemma pullback_anodyne_heq {P X E Y : SSet.{u}}
    [SSet.KanComplex X] [SSet.KanComplex Y]
    {a : P ⟶ X} {j : P ⟶ E} {i : X ⟶ Y} {p : E ⟶ Y}
    (sq : IsPullback a j i p) (hi : SSet.anodyneExtensions i)
    (hp : simplicialFibrations p) : IsHomotopyEquivalence j := by
  let : Mono i := KanQuillen.anodyne_monomorphism _ hi
  let : Mono j := MorphismProperty.of_isPullback sq
    (show (MorphismProperty.monomorphisms SSet) i from inferInstance)
  obtain ⟨r,H,hr,hH⟩ := anodyne_deformation i hi
  obtain ⟨Q,hQ,hQ₀,hQp⟩ := cylinder_lift j p hp 1 (𝟙 E)
    (fst P Δ[1] ≫ j) (p ▷ Δ[1] ≫ H.h)
    (by simp [endpoint_zero])
    (by rw [endpoint_zero, SSet.ι₀_comp_assoc, H.h₀, Category.comp_id, Category.id_comp])
    (by
      calc
        (fst P Δ[1] ≫ j) ≫ p = fst P Δ[1] ≫ a ≫ i := by rw [Category.assoc, ← sq.w]
        _ = a ▷ Δ[1] ≫ i ▷ Δ[1] ≫ H.h := by rw [hH, whiskerRight_fst_assoc]
        _ = j ▷ Δ[1] ≫ p ▷ Δ[1] ≫ H.h := by
          rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, sq.w,
            MonoidalCategory.comp_whiskerRight, Category.assoc])
  let s : E ⟶ P := sq.lift (p ≫ r) (SSet.ι₁ ≫ Q)
    (by simp only [Category.assoc]; rw [hQp, SSet.ι₁_comp_assoc, H.h₁])
  have hs : j ≫ s = 𝟙 P := by
    apply sq.hom_ext
    · simp only [Category.assoc, s, IsPullback.lift_fst, Category.id_comp]
      rw [← Category.assoc, ← sq.w, Category.assoc, hr, Category.comp_id]
    · simp only [Category.assoc, s, IsPullback.lift_snd, Category.id_comp]
      rw [← SSet.ι₁_comp_assoc, hQ]
      simp
  refine ⟨s, ?_, ?_⟩
  · rw [hs]
    exact homotopic_refl _
  · have H' : SSet.Homotopy (𝟙 E) (s ≫ j) :=
      CoherentGluing.toHomotopy Q (by simpa [endpoint_zero] using hQ₀)
        (by simp [s])
    exact homotopic_symm (homotopic_of_homotopy H')

lemma pullback_heq {P X E Y : SSet.{u}}
    [SSet.KanComplex X] [SSet.KanComplex Y]
    {a : P ⟶ X} {j : P ⟶ E} {f : X ⟶ Y} {p : E ⟶ Y}
    (sq : IsPullback a j f p) (hf : IsHomotopyEquivalence f)
    (hp : simplicialFibrations p) : IsHomotopyEquivalence j := by
  let d := MorphismProperty.factorizationData SSet.modelCategoryQuillen.J.rlp.llp
    SSet.modelCategoryQuillen.J.rlp f
  let : HomotopicalAlgebra.Fibration d.p := by
    rw [HomotopicalAlgebra.fibration_iff, SSet.modelCategoryQuillen.fibrations_eq]
    exact d.hp
  let : SSet.KanComplex d.Z := HomotopicalAlgebra.isFibrant_of_fibration d.p
  have hd : IsHomotopyEquivalence d.p := heq_of_precomp d.i d.p
    (heq_anodyne d.i d.hi) (d.fac.symm ▸ hf)
  have hd' := rlp_of_homotopy_equivalence d.p d.hp hd
  let b := pullback.fst d.p p
  let c := pullback.snd d.p p
  have sq₀ : IsPullback b c d.p p := IsPullback.of_hasPullback d.p p
  let k : P ⟶ pullback d.p p := sq₀.lift (a ≫ d.i) j
    (by rw [Category.assoc, d.fac, sq.w])
  have hk₀ : k ≫ b = a ≫ d.i := sq₀.lift_fst _ _ _
  have hk₁ : k ≫ c = j := sq₀.lift_snd _ _ _
  have sq₁ : IsPullback a k d.i b := by
    have sq' : IsPullback a (k ≫ c) (d.i ≫ d.p) p := by rw [hk₁, d.fac]; exact sq
    exact sq'.of_bot hk₀.symm sq₀
  have hb : simplicialFibrations b := by
    change SSet.modelCategoryQuillen.J.rlp b
    exact MorphismProperty.of_isPullback sq₀.flip hp
  have hk : IsHomotopyEquivalence k := pullback_anodyne_heq sq₁ d.hi hb
  have hc : IsHomotopyEquivalence c := heq_of_rlp c (MorphismProperty.of_isPullback sq₀ hd')
  exact hk₁ ▸ heq_comp hk hc

lemma local_pushout {A B C D : SSet.{u}} {f : A ⟶ B} {i : A ⟶ C}
    {j : B ⟶ D} {k : C ⟶ D} (sq : IsPushout f i j k) [Mono i]
    (hf : Local f) : Local k := by
  intro K hK
  have sq' := sq.op.map (internalHom.flip.obj K)
  have hi : simplicialFibrations ((pre i).app K) := by
    change SSet.modelCategoryQuillen.J.rlp _
    rw [← SSet.modelCategoryQuillen.fibrations_eq, ← HomotopicalAlgebra.fibration_iff]
    infer_instance
  have sq'' : IsPullback ((pre j).app K) ((pre k).app K)
      ((pre f).app K) ((pre i).app K) := sq'.flip
  exact pullback_heq sq'' (hf K hK) hi

lemma local_pushout_map {K A B C P Q : SSet.{u}} (k : K ⟶ A) (c : K ⟶ C) [Mono c]
    (f : A ⟶ B) (hf : Local f)
    {lA : A ⟶ P} {lC : C ⟶ P} (sp : IsPushout k c lA lC)
    {lB : B ⟶ Q} {lC' : C ⟶ Q} (sq : IsPushout (k ≫ f) c lB lC')
    (F : P ⟶ Q) (hFA : lA ≫ F = f ≫ lB) (hFC : lC ≫ F = lC') : Local F := by
  have sq' : IsPushout (k ≫ f) c lB (lC ≫ F) := by rw [hFC]; exact sq
  have : Mono lA := MorphismProperty.of_isPushout sp
    (show (MorphismProperty.monomorphisms SSet) c from inferInstance)
  exact local_pushout (sq'.of_left hFA.symm sp) hf

end Thomason.KanLocal

end

noncomputable section
universe u v w z


namespace Thomason.OneCat
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

@[reassoc] lemma cylinderMap_pre {C D E : Cat.{u,u}} (f : C ⟶ D)
    (H : cylinder.obj D ⟶ E) :
    nerveFunctor.map f ▷ Δ[1] ≫ cylinderMap H = cylinderMap (cylinder.map f ≫ H) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  rfl

@[reassoc] lemma cylinderMap_post {C D E : Cat.{u,u}} (H : cylinder.obj C ⟶ D)
    (f : D ⟶ E) :
    cylinderMap H ≫ nerveFunctor.map f = cylinderMap (H ≫ f) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  rfl

lemma cylinderMap_projection (C : Cat.{u,u}) :
    cylinderMap (projection C) = fst (nerveFunctor.obj C) Δ[1] := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  rfl

lemma pushout_deformation_coherent {A E X Y : Cat.{u,u}} {a : A ⟶ X} {i : A ⟶ E}
    {j : X ⟶ Y} {v : E ⟶ Y} (sq : IsPushout a i j v)
    (r : E ⟶ A) (ri : i ≫ r = 𝟙 A)
    (H : cylinder.obj E ⟶ E)
    (h₀ : endpoint E 0 ≫ H = r ≫ i)
    (h₁ : endpoint E 1 ≫ H = 𝟙 E)
    (hA : cylinder.map i ≫ H = projection A ≫ i) :
    ∃ (p : Y ⟶ X) (H' : cylinder.obj Y ⟶ Y),
      j ≫ p = 𝟙 X ∧ v ≫ p = r ≫ a ∧
      endpoint Y 0 ≫ H' = p ≫ j ∧ endpoint Y 1 ≫ H' = 𝟙 Y ∧
      cylinder.map j ≫ H' = projection X ≫ j ∧ cylinder.map v ≫ H' = H ≫ v := by
  let p : Y ⟶ X := sq.desc (𝟙 X) (r ≫ a) (by simp [← Category.assoc,ri])
  have pj : j ≫ p = 𝟙 X := sq.inl_desc _ _ _
  have pv : v ≫ p = r ≫ a := sq.inr_desc _ _ _
  have sw := sq.map cylinder
  have hw : cylinder.map a ≫ (projection X ≫ j) = cylinder.map i ≫ (H ≫ v) := by
    rw [projection_natural_assoc, ← Category.assoc (cylinder.map i),hA]
    simpa only [Category.assoc] using congrArg (projection A ≫ ·) sq.w
  let Q : cylinder.obj Y ⟶ Y := sw.desc (projection X ≫ j) (H ≫ v) hw
  have Qj : cylinder.map j ≫ Q = projection X ≫ j := sw.inl_desc _ _ _
  have Qv : cylinder.map v ≫ Q = H ≫ v := sw.inr_desc _ _ _
  refine ⟨p,Q,pj,pv,?_,?_,Qj,Qv⟩
  · apply sq.hom_ext
    · erw [← Category.assoc, ← endpoint_natural, Category.assoc, Qj, ← Category.assoc, endpoint_projection,
        Category.id_comp, ← Category.assoc, pj, Category.id_comp]
    · erw [← Category.assoc, ← endpoint_natural, Category.assoc, Qv, ← Category.assoc, h₀,
        ← Category.assoc v p j, pv]
      simpa only [Category.assoc] using congrArg (r ≫ ·) sq.w.symm
  · apply sq.hom_ext
    · erw [Category.comp_id, ← Category.assoc, ← endpoint_natural, Category.assoc, Qj,
        ← Category.assoc, endpoint_projection, Category.id_comp]
    · erw [Category.comp_id, ← Category.assoc, ← endpoint_natural, Category.assoc, Qv,
        ← Category.assoc, h₁, Category.id_comp]

lemma nerve_pushout_coherent {A E X Y : Cat.{u,u}} {a : A ⟶ X} {i : A ⟶ E}
    {j : X ⟶ Y} {v : E ⟶ Y} (sc : IsPushout a i j v)
    (r : E ⟶ A) (ri : i ≫ r = 𝟙 A)
    (HE : cylinder.obj E ⟶ E)
    (h₀ : endpoint E 0 ≫ HE = r ≫ i)
    (h₁ : endpoint E 1 ≫ HE = 𝟙 E)
    (hA : cylinder.map i ≫ HE = projection A ≫ i)
    {P : SSet.{u}} {lX : nerveFunctor.obj X ⟶ P} {lE : nerveFunctor.obj E ⟶ P}
    (ss : IsPushout (nerveFunctor.map a) (nerveFunctor.map i) lX lE)
    (F : P ⟶ nerveFunctor.obj Y) (hFX : lX ≫ F = nerveFunctor.map j)
    (hFE : lE ≫ F = nerveFunctor.map v) :
    ∃ (G : nerveFunctor.obj Y ⟶ P)
      (HP : SSet.Homotopy (F ≫ G) (𝟙 P))
      (HQ : SSet.Homotopy (G ≫ F) (𝟙 (nerveFunctor.obj Y))),
      HP.h ≫ F = F ▷ Δ[1] ≫ HQ.h := by
  obtain ⟨p,HY,hpj,hpv,hY₀,hY₁,hYX,hYE⟩ :=
    pushout_deformation_coherent sc r ri HE h₀ h₁ hA
  let G : nerveFunctor.obj Y ⟶ P := nerveFunctor.map p ≫ lX
  have hG₀ : nerveFunctor.map (p ≫ j) = G ≫ F := by
    simp only [G, CategoryTheory.Functor.map_comp, Category.assoc, hFX]
  let HQ : SSet.Homotopy (G ≫ F) (𝟙 (nerveFunctor.obj Y)) :=
    CoherentGluing.toHomotopy (cylinderMap HY)
      (by erw [cylinderMap_zero,hY₀,hG₀])
      (by erw [cylinderMap_one,hY₁,CategoryTheory.Functor.map_id])
  have hI : (nerveFunctor.map a ▷ Δ[1]) ≫ (fst (nerveFunctor.obj X) Δ[1] ≫ lX) =
      (nerveFunctor.map i ▷ Δ[1]) ≫ (cylinderMap HE ≫ lE) := by
    erw [← Category.assoc _ (cylinderMap HE), cylinderMap_pre, hA, ← cylinderMap_post,
      cylinderMap_projection]
    erw [Category.assoc, ← ss.w]
    rfl
  let sI := ss.map (tensorRight (Δ[1] : SSet.{u}))
  let H : P ⊗ Δ[1] ⟶ P := sI.desc (fst (nerveFunctor.obj X) Δ[1] ≫ lX)
    (cylinderMap HE ≫ lE) hI
  have hHX : lX ▷ Δ[1] ≫ H = fst (nerveFunctor.obj X) Δ[1] ≫ lX := sI.inl_desc _ _ _
  have hHE : lE ▷ Δ[1] ≫ H = cylinderMap HE ≫ lE := sI.inr_desc _ _ _
  have hH₀ : SSet.ι₀ ≫ H = F ≫ G := by
    apply ss.hom_ext
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hHX,
        ← Category.assoc, SSet.ι₀_fst, Category.id_comp,
        ← Category.assoc lX F, hFX]
      dsimp only [G]
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hpj, CategoryTheory.Functor.map_id, Category.id_comp]
    · erw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, hHE,
        ← Category.assoc, cylinderMap_zero,h₀,CategoryTheory.Functor.map_comp,
        Category.assoc, ← ss.w, ← Category.assoc lE F, hFE]
      dsimp only [G]
      rw [← Category.assoc (nerveFunctor.map v), ← CategoryTheory.Functor.map_comp, hpv]
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
  have hH₁ : SSet.ι₁ ≫ H = 𝟙 P := by
    apply ss.hom_ext
    · rw [Category.comp_id, ← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hHX,
        ← Category.assoc, SSet.ι₁_fst, Category.id_comp]
    · erw [Category.comp_id, ← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hHE,
        ← Category.assoc, cylinderMap_one, h₁, CategoryTheory.Functor.map_id, Category.id_comp]
  refine ⟨G, CoherentGluing.toHomotopy H hH₀ hH₁, HQ, ?_⟩
  change H ≫ F = F ▷ Δ[1] ≫ cylinderMap HY
  apply sI.hom_ext
  · change lX ▷ Δ[1] ≫ (H ≫ F) = lX ▷ Δ[1] ≫ (F ▷ Δ[1] ≫ cylinderMap HY)
    erw [← Category.assoc _ H, hHX, Category.assoc, hFX,
      ← Category.assoc (lX ▷ Δ[1]), ← comp_whiskerRight, hFX,
      cylinderMap_pre, hYX, ← cylinderMap_post,cylinderMap_projection]
    rfl
  · change lE ▷ Δ[1] ≫ (H ≫ F) = lE ▷ Δ[1] ≫ (F ▷ Δ[1] ≫ cylinderMap HY)
    erw [← Category.assoc _ H, hHE, Category.assoc, hFE,
      ← Category.assoc (lE ▷ Δ[1]), ← comp_whiskerRight, hFE,
      cylinderMap_pre,hYE,← cylinderMap_post]
    rfl
end Thomason.OneCat

end

noncomputable section
universe u v w z


namespace Thomason.CoherentGluing
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

def Coherent {A B : SSet.{u}} (f : A ⟶ B) : Prop :=
  ∃ (g : B ⟶ A) (HA : SSet.Homotopy (f ≫ g) (𝟙 A))
    (HB : SSet.Homotopy (g ≫ f) (𝟙 B)), HA.h ≫ f = f ▷ Δ[1] ≫ HB.h

lemma coherent_of_postIso {A B C : SSet.{u}} (f : A ⟶ B) (e : B ≅ C)
    (h : Coherent (f ≫ e.hom)) : Coherent f := by
  obtain ⟨g,HA,HB,hcoh⟩ := h
  let g' := e.hom ≫ g
  let HA' : SSet.Homotopy (f ≫ g') (𝟙 A) :=
    toHomotopy HA.h (by simpa only [g',Category.assoc] using HA.h₀) HA.h₁
  let HB' : SSet.Homotopy (g' ≫ f) (𝟙 B) :=
    toHomotopy (e.hom ▷ Δ[1] ≫ HB.h ≫ e.inv)
      (by rw [SSet.ι₀_comp_assoc, HB.h₀_assoc]; simp [g',Category.assoc])
      (by rw [SSet.ι₁_comp_assoc, HB.h₁_assoc]; simp)
  refine ⟨g',HA',HB',?_⟩
  change HA.h ≫ f = f ▷ Δ[1] ≫ e.hom ▷ Δ[1] ≫ HB.h ≫ e.inv
  apply (cancel_mono e.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, comp_whiskerRight] using hcoh
end Thomason.CoherentGluing

end

noncomputable section
universe u v w z


namespace Thomason.OneCat
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory

variable {A E : Type u} [PartialOrder A] [PartialOrder E]
    (i : A →o E) (r : E →o A) (ri : ∀ a, r (i a) = a)
    (counit : ∀ e, i (r e) ≤ e)

def orderMapCylinder : Interval.{u} × E →o E where
  toFun x := if x.1.down = 0 then i (r x.2) else x.2
  monotone' := by
    rintro ⟨⟨b⟩,e⟩ ⟨⟨c⟩,f⟩ ⟨hbc,hef⟩
    fin_cases b <;> fin_cases c
    · exact i.monotone (r.monotone hef)
    · exact (counit e).trans hef
    · exact False.elim (by simp at hbc)
    · exact hef

def posetMapCylinder : cylinder.obj (Cat.of E) ⟶ Cat.of E :=
  ({ obj := orderMapCylinder i r counit
     map := fun f => homOfLE ((orderMapCylinder i r counit).monotone
       ⟨leOfHom f.1,leOfHom f.2⟩) } : Interval.{u} × E ⥤ E).toCatHom

lemma posetMapCylinder_zero : endpoint (Cat.of E) 0 ≫ posetMapCylinder i r counit =
    r.toFunctor.toCatHom ≫ i.toFunctor.toCatHom := by
  apply Cat.Hom.ext
  exact CategoryTheory.Functor.ext (fun _ => rfl)
lemma posetMapCylinder_one : endpoint (Cat.of E) 1 ≫ posetMapCylinder i r counit = 𝟙 (Cat.of E) := by
  apply Cat.Hom.ext
  exact CategoryTheory.Functor.ext (fun _ => rfl)
include ri in
lemma posetMapCylinder_stationary :
    cylinder.map i.toFunctor.toCatHom ≫ posetMapCylinder i r counit =
      projection (Cat.of A) ≫ i.toFunctor.toCatHom := by
  apply Cat.Hom.ext
  exact CategoryTheory.Functor.ext (fun ⟨⟨b⟩,a⟩ => by
    change (if b = 0 then i (r (i a)) else i a) = i a
    rw [ri a]
    simp)
include ri in
lemma posetMapRetraction : i.toFunctor.toCatHom ≫ r.toFunctor.toCatHom = 𝟙 (Cat.of A) := by
  apply Cat.Hom.ext
  exact CategoryTheory.Functor.ext ri

end Thomason.OneCat

end

noncomputable section
universe u v w z


namespace Thomason.OneCat
open CategoryTheory Limits Simplicial MonoidalCategory CartesianMonoidalCategory OmegaCategory

lemma nerve_categorification_attach {C : Cat.{u,u}} {X : NCategory.{u} 1}
    (a : (categorificationFinite 1).obj (nerveFunctor.obj C) ⟶ X) :
    nerveFunctor.map ((categorificationCatIso C).hom ≫ oneSkeletonCatFunctor.map a) =
      (categorificationFiniteAdjunction 1).unit.app (nerveFunctor.obj C) ≫
        (streetNerveFinite 1).map a ≫ oneNerveFunctorIso.hom.app X := by
  rw [CategoryTheory.Functor.map_comp, categorificationCatIso_nerve]
  erw [Category.assoc]

lemma finite_poset_comparison_coherent {A E : Type u} [PartialOrder A] [PartialOrder E]
    (i : A →o E) (r : E →o A) (ri : ∀ a, r (i a) = a)
    (counit : ∀ e, i (r e) ≤ e)
    {X Y : NCategory.{u} 1}
    {a : (categorificationFinite 1).obj (nerve A) ⟶ X}
    {j : X ⟶ Y} {v : (categorificationFinite 1).obj (nerve E) ⟶ Y}
    (sc : IsPushout a ((categorificationFinite 1).map (nerveMap i.toFunctor)) j v)
    {P : SSet.{u}} {lX : (streetNerveFinite 1).obj X ⟶ P}
    {lE : (streetNerveFinite 1).obj ((categorificationFinite 1).obj (nerve E)) ⟶ P}
    (ss : IsPushout ((streetNerveFinite 1).map a)
      ((streetNerveFinite 1).map ((categorificationFinite 1).map (nerveMap i.toFunctor))) lX lE)
    (F : P ⟶ (streetNerveFinite 1).obj Y)
    (hFX : lX ≫ F = (streetNerveFinite 1).map j)
    (hFE : lE ≫ F = (streetNerveFinite 1).map v) : CoherentGluing.Coherent F := by
  let sk := oneSkeletonCatFunctor
  let N := streetNerveFinite 1
  let a' := (categorificationCatIso (Cat.of A)).hom ≫ sk.map a
  let v' := (categorificationCatIso (Cat.of E)).hom ≫ sk.map v
  have sc' : IsPushout a' i.toFunctor.toCatHom (sk.map j) v' := by
    apply (sc.map sk).of_iso' (categorificationCatIso (Cat.of A)) (Iso.refl _)
      (categorificationCatIso (Cat.of E)) (Iso.refl _)
    · simp [a']
      rfl
    · exact (categorificationCatIso_natural i.toFunctor.toCatHom).symm
    · simp
    · simp [v']
      rfl
  let dX := oneNerveFunctorIso.app X
  let dY := oneNerveFunctorIso.app Y
  let uA := (categorificationFiniteAdjunction 1).unit.app (nerve A)
  let uE := (categorificationFiniteAdjunction 1).unit.app (nerve E)
  have : IsIso uA := oneUnitCatIso (Cat.of A)
  have : IsIso uE := oneUnitCatIso (Cat.of E)
  have ha' : nerveFunctor.map a' = uA ≫ N.map a ≫ dX.hom :=
    nerve_categorification_attach (C := Cat.of A) a
  have hv' : nerveFunctor.map v' = uE ≫ N.map v ≫ dY.hom :=
    nerve_categorification_attach (C := Cat.of E) v
  have ss' : IsPushout (nerveFunctor.map a') (nerveMap i.toFunctor)
      (dX.inv ≫ lX) (uE ≫ lE) := by
    apply ss.of_iso' (asIso uA) dX.symm (asIso uE) (Iso.refl _)
    · simp only [asIso_hom, ha', Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.symm_hom]
      rfl
    · exact ((categorificationFiniteAdjunction 1).unit.naturality (nerveMap i.toFunctor)).symm
    · simp
    · simp
  have hf'X : (dX.inv ≫ lX) ≫ (F ≫ dY.hom) = nerveFunctor.map (sk.map j) := by
    rw [Category.assoc, ← Category.assoc lX F, hFX]
    rw [show N.map j ≫ dY.hom = dX.hom ≫ nerveFunctor.map (sk.map j) from
      oneNerveFunctorIso.hom.naturality j]
    erw [Iso.inv_hom_id_assoc]
  have hf'E : (uE ≫ lE) ≫ (F ≫ dY.hom) = nerveFunctor.map v' := by
    rw [Category.assoc, ← Category.assoc lE F, hFE, hv']
  apply CoherentGluing.coherent_of_postIso F dY
  exact nerve_pushout_coherent sc' r.toFunctor.toCatHom
    (posetMapRetraction i r ri) (posetMapCylinder i r counit)
    (posetMapCylinder_zero i r counit) (posetMapCylinder_one i r counit)
    (posetMapCylinder_stationary i r ri counit) ss' (F ≫ dY.hom) hf'X hf'E
end Thomason.OneCat

end

noncomputable section
universe u v w z


namespace Thomason.AttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments

abbrev posetObj (n : ℕ) (P : Type u) [PartialOrder P] :=
  (categorificationFinite n).obj (nerve P)

abbrev posetMap (n : ℕ) {P Q : Type u} [PartialOrder P] [PartialOrder Q] (f : P →o Q) :=
  (categorificationFinite n).map (nerveMap f.toFunctor)

abbrev sb (n : ℕ) {P : Type u} [PartialOrder P] (A B : Set P) (h : A ⊆ B) :=
  (categorificationFinite n).map (nerveMap (subposetMap A B h).toFunctor)

abbrev inc (n : ℕ) {P : Type u} [PartialOrder P] (A : Set P) :=
  (categorificationFinite n).map
    (nerveMap (OrderHom.Subtype.val (fun element : P => element ∈ A)).toFunctor)

@[reassoc] lemma sb_inc (n : ℕ) {P : Type u} [PartialOrder P]
    (A B : Set P) (h : A ⊆ B) : sb n A B h ≫ inc n B = inc n A := by
  rw [← (categorificationFinite n).map_comp]
  rfl

lemma attachment_nerve_cover (n : ℕ) (hn : 1 ≤ n) {P : Type u} [PartialOrder P]
    (A Z C : Set P) (hZ : IsUpperSet Z) (hC : IsUpperSet C)
    (hAZ : A ⊆ Z) (hAC : Disjoint A C) (hcover : Z ∪ C = Set.univ)
    {X Y : NCategory.{u} n} (a : posetObj n A ⟶ X) (j : X ⟶ Y)
    (v : posetObj n P ⟶ Y) (sc : IsPushout a (inc n A) j v) :
    ∃ (YZ : NCategory.{u} n) (jZ : X ⟶ YZ) (vZ : posetObj n Z ⟶ YZ) (uZ : YZ ⟶ Y),
      IsPushout a (sb n A Z hAZ) jZ vZ ∧ jZ ≫ uZ = j ∧ vZ ≫ uZ = inc n Z ≫ v ∧
      IsPushout ((streetNerveFinite n).map (sb n (Z ∩ C) Z Set.inter_subset_left ≫ vZ))
        ((streetNerveFinite n).map (sb n (Z ∩ C) C Set.inter_subset_right))
        ((streetNerveFinite n).map uZ) ((streetNerveFinite n).map (inc n C ≫ v)) := by
  obtain ⟨T₁,T₂,hT₁,hT₂,hTc,⟨jZ,vZ,hj,hv,sz⟩,⟨e₂,he₂⟩,⟨e₃,he₃⟩⟩ :=
    cosieve_finite_attachment_covers n hn A Z C hZ hC hAZ hAC hcover a j v sc
  let N := streetNerveFinite n
  let u₁ := fullFiniteInclusion n Y T₁
  let u₂ := fullFiniteInclusion n Y T₂
  let u₃ := fullFiniteInclusion n Y (T₁ ∩ T₂)
  let p₁ : fullFinite n Y (T₁ ∩ T₂) ⟶ fullFinite n Y T₁ :=
    fullOnMap Set.inter_subset_left
  let p₂ : fullFinite n Y (T₁ ∩ T₂) ⟶ fullFinite n Y T₂ :=
    fullOnMap Set.inter_subset_right
  change vZ ≫ u₁ = inc n Z ≫ v at hv
  change e₂.hom ≫ u₂ = inc n C ≫ v at he₂
  change e₃.hom ≫ u₃ = inc n (Z ∩ C) ≫ v at he₃
  have hu₁ : p₁ ≫ u₁ = u₃ := rfl
  have hu₂ : p₂ ≫ u₂ = u₃ := rfl
  have : Mono (N.map u₁) := fullInclusion_nerve_mono Y.val T₁
  have : Mono (N.map u₂) := fullInclusion_nerve_mono Y.val T₂
  have sq : IsPushout (N.map p₁) (N.map p₂) (N.map u₁) (N.map u₂) :=
    cosieve_cover_nerve_isPushout hT₁ hT₂ (fun x => by
      have hx : x ∈ T₁ ∪ T₂ := by rw [hTc]; trivial
      exact hx)
  refine ⟨fullFinite n Y T₁, jZ, vZ, u₁, sz, hj, hv, ?_⟩
  apply sq.of_iso' (N.mapIso e₃) (Iso.refl _) (N.mapIso e₂) (Iso.refl _)
  · simp only [CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
    change N.map e₃.hom ≫ N.map p₁ = N.map (sb n (Z ∩ C) Z Set.inter_subset_left ≫ vZ)
    apply (cancel_mono (N.map u₁)).mp
    simp only [← N.map_comp, Category.assoc, hu₁, he₃, hv]
    rw [sb_inc_assoc]
  · simp only [CategoryTheory.Functor.mapIso_hom]
    change N.map e₃.hom ≫ N.map p₂ = N.map (sb n (Z ∩ C) C Set.inter_subset_right) ≫ N.map e₂.hom
    apply (cancel_mono (N.map u₂)).mp
    simp only [← N.map_comp, Category.assoc, hu₂, he₃, he₂]
    rw [sb_inc_assoc]
  · simp [N]
  · simp only [CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
    change N.map e₂.hom ≫ N.map u₂ = N.map (inc n C ≫ v)
    rw [← N.map_comp, he₂]

lemma poset_nerve_cover (n : ℕ) (hn : 1 ≤ n) {P : Type u} [PartialOrder P]
    (Z C : Set P) (hZ : IsUpperSet Z) (hC : IsUpperSet C)
    (hcover : Z ∪ C = Set.univ) :
    IsPushout ((streetNerveFinite n).map (sb n (Z ∩ C) Z Set.inter_subset_left))
      ((streetNerveFinite n).map (sb n (Z ∩ C) C Set.inter_subset_right))
      ((streetNerveFinite n).map (inc n Z)) ((streetNerveFinite n).map (inc n C)) := by
  obtain ⟨YZ,jZ,vZ,uZ,sz,hj,hv,sq⟩ := attachment_nerve_cover n hn (∅ : Set P) Z C
    hZ hC (Set.empty_subset Z) (by simp) hcover
    (𝟙 (posetObj n (∅ : Set P))) (inc n (∅ : Set P)) (𝟙 (posetObj n P))
    (IsPushout.of_id_fst)
  have : IsIso vZ := sz.isIso_inr_of_isIso
  let N := streetNerveFinite n
  apply sq.of_iso' (Iso.refl _) (N.mapIso (asIso vZ)) (Iso.refl _) (Iso.refl _)
  · simp [N]
  · simp
  · simp only [CategoryTheory.Functor.mapIso_hom, asIso_hom, Iso.refl_hom, Category.comp_id]
    change N.map vZ ≫ N.map uZ = N.map (inc n Z)
    rw [← N.map_comp, hv, Category.comp_id]
  · simp
end Thomason.AttachmentComparison

end

end OAI
