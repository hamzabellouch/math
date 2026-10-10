import Mathlib

namespace OAI

noncomputable section

namespace CampanaPeternellSix.ProjectiveCoordinates
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousLocalization
universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : A →+* B) (d : ℕ) (hd : 0 < d)
  (hdeg : ∀ n {a : A}, a ∈ 𝒜 n → f a ∈ ℬ (d * n))

include hd hdeg in
lemma map_component (x : A) (n : ℕ) :
    f (DirectSum.decompose 𝒜 x n) = (DirectSum.decompose ℬ (f x) (d * n) : B) := by
  classical
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i x =>
    by_cases h : i = n
    · subst h
      rw [DirectSum.decompose_of_mem_same 𝒜 x.2,
        DirectSum.decompose_of_mem_same ℬ (hdeg _ x.2)]
    · rw [DirectSum.decompose_of_mem_ne 𝒜 x.2 h,
        DirectSum.decompose_of_mem_ne ℬ (hdeg _ x.2) (fun e ↦ h (Nat.eq_of_mul_eq_mul_left hd e)), map_zero]
  | add x y hx hy => simp [DirectSum.decompose_add, hx, hy]

def comapIdeal (I : HomogeneousIdeal ℬ) : HomogeneousIdeal 𝒜 where
  __ := I.toIdeal.comap f
  is_homogeneous' n a ha := by
    change f _ ∈ I.toIdeal
    rw [map_component f d hd hdeg]
    exact I.2 _ ha

variable {P : Submonoid A} {Q : Submonoid B}

def mapFraction (hPQ : P ≤ Q.comap f) (c : NumDenSameDeg 𝒜 P) : NumDenSameDeg ℬ Q where
  deg := d * c.deg
  num := ⟨f c.num, hdeg _ c.num.2⟩
  den := ⟨f c.den, hdeg _ c.den.2⟩
  den_mem := hPQ c.den_mem

 

def mapLocalization (hPQ : P ≤ Q.comap f) :
    HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization ℬ Q where
  toFun := Quotient.map' (mapFraction f d hdeg hPQ) fun x y
    (e : x.embedding = y.embedding) ↦ by
      apply_fun IsLocalization.map (Localization Q) f hPQ at e
      simp_rw [NumDenSameDeg.embedding, Localization.mk_eq_mk',
        IsLocalization.map_mk', ← Localization.mk_eq_mk'] at e
      exact e
  map_add' := Quotient.ind₂' fun x y ↦ by
    change mk (mapFraction f d hdeg hPQ (x + y)) =
      mk (mapFraction f d hdeg hPQ x) + mk (mapFraction f d hdeg hPQ y)
    rw [← mk_add]
    apply (HomogeneousLocalization.ext_iff_val _ _).mpr
    simp [mapFraction, NumDenSameDeg.num_add, NumDenSameDeg.den_add,
      Localization.add_mk, mul_comm, add_comm]
  map_mul' := Quotient.ind₂' fun x y ↦ by
    change mk (mapFraction f d hdeg hPQ (x * y)) =
      mk (mapFraction f d hdeg hPQ x) * mk (mapFraction f d hdeg hPQ y)
    rw [← mk_mul]
    apply (HomogeneousLocalization.ext_iff_val _ _).mpr
    simp [mapFraction, NumDenSameDeg.num_mul, NumDenSameDeg.den_mul,
      Localization.mk_mul]
  map_zero' := by
    change mk (mapFraction f d hdeg hPQ 0) = mk (0 : NumDenSameDeg ℬ Q)
    apply (HomogeneousLocalization.ext_iff_val _ _).mpr
    simp [mapFraction, Localization.mk_zero]
  map_one' := by
    change mk (mapFraction f d hdeg hPQ 1) = mk (1 : NumDenSameDeg ℬ Q)
    apply (HomogeneousLocalization.ext_iff_val _ _).mpr
    simp [mapFraction]

@[simp] lemma mapLocalization_mk (hPQ : P ≤ Q.comap f) (c : NumDenSameDeg 𝒜 P) :
    mapLocalization f d hdeg hPQ (mk c) = mk (mapFraction f d hdeg hPQ c) := rfl

variable (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime] (hIJ : I = J.comap f)

def mapLocalRing : AtPrime 𝒜 I →+* AtPrime ℬ J :=
  mapLocalization f d hdeg (Localization.le_comap_primeCompl_iff.mpr (hIJ ▸ le_rfl))

@[simp] lemma val_mapLocalRing (x : AtPrime 𝒜 I) :
    (mapLocalRing f d hdeg I J hIJ x).val =
      Localization.localRingHom I J f hIJ x.val := by
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp [mapLocalRing, mapLocalization_mk, mapFraction]

instance : IsLocalHom (mapLocalRing f d hdeg I J hIJ) where
  map_nonunit x hx := by
    rw [← isUnit_iff_isUnit_val] at hx ⊢
    rw [val_mapLocalRing] at hx
    exact IsLocalHom.map_nonunit _ hx

private lemma isUnit_of_mapLocalRing {x : AtPrime 𝒜 I}
    (hx : IsUnit (mapLocalRing f d hdeg I J hIJ x)) : IsUnit x :=
  IsLocalHom.map_nonunit x hx
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousLocalization
  ProjectiveSpectrum Proj ProjectiveSpectrum.StructureSheaf
universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : A →+* B) (d : ℕ) (hd : 0 < d)
  (hdeg : ∀ n {a : A}, a ∈ 𝒜 n → f a ∈ ℬ (d * n))
  (hbase : ∀ p : ProjectiveSpectrum ℬ,
    ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ p.1.toIdeal.comap f)

def comapPoint (p : ProjectiveSpectrum ℬ) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := comapIdeal f d hd hdeg p.1
  isPrime := p.2.comap f
  not_irrelevant_le := hbase p

def comapContinuous : C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where
  toFun := comapPoint f d hd hdeg hbase
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp,
      forall_eq_apply_imp_iff]
    exact fun s ↦ ⟨f '' s, by ext; simp only [Set.mem_preimage, mem_zeroLocus, Set.image_subset_iff]; rfl⟩

variable (U : Opens (ProjectiveSpectrum 𝒜)) (V : Opens (ProjectiveSpectrum ℬ))
  (hUV : V.1 ⊆ comapContinuous f d hd hdeg hbase ⁻¹' U.1)

def comapSectionFun (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (y : V) :
    AtPrime ℬ y.1.1.1 :=
  mapLocalRing f d hdeg _ y.1.1.1 rfl <|
    s ⟨comapPoint f d hd hdeg hbase y.1, hUV y.2⟩

lemma locallyFraction_comapSection
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (hs : (isLocallyFraction 𝒜).pred s) :
    (isLocallyFraction ℬ).pred (comapSectionFun f d hd hdeg hbase U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨comapPoint f d hd hdeg hbase p, hUV hpV⟩ with
    ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (comapContinuous f d hd hdeg hbase) ⊓ V, ⟨m, hpV⟩,
    Opens.infLERight _ _, d * i, ⟨f a, hdeg _ a.2⟩, ⟨f b, hdeg _ b.2⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ hb ⟨_, hqW⟩, fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ ?_⟩
  ext
  specialize h_frac ⟨_, hqW⟩
  change s ⟨comapPoint f d hd hdeg hbase q, hUV hqV⟩ = _ at h_frac
  let : q.1.toIdeal.IsPrime := q.isPrime
  change (mapLocalRing f d hdeg
    (comapPoint f d hd hdeg hbase q).1.toIdeal q.1.toIdeal rfl
    (s ⟨comapPoint f d hd hdeg hbase q, hUV hqV⟩)).val = _
  rw [h_frac]
  rfl

def comapSections :
    (Proj.structureSheaf 𝒜).1.obj (op U) →+* (Proj.structureSheaf ℬ).1.obj (op V) where
  toFun s := ⟨comapSectionFun f d hd hdeg hbase U V hUV s.1,
    locallyFraction_comapSection f d hd hdeg hbase U V hUV s.1 s.2⟩
  map_one' := by
    apply Subtype.ext
    funext p
    let : p.1.1.toIdeal.IsPrime := p.1.isPrime
    exact map_one (mapLocalRing f d hdeg
      (comapPoint f d hd hdeg hbase p.1).1.toIdeal p.1.1.toIdeal rfl)
  map_zero' := by
    apply Subtype.ext
    funext p
    let : p.1.1.toIdeal.IsPrime := p.1.isPrime
    exact map_zero (mapLocalRing f d hdeg
      (comapPoint f d hd hdeg hbase p.1).1.toIdeal p.1.1.toIdeal rfl)
  map_add' x y := by
    apply Subtype.ext
    funext p
    let : p.1.1.toIdeal.IsPrime := p.1.isPrime
    exact map_add (mapLocalRing f d hdeg
      (comapPoint f d hd hdeg hbase p.1).1.toIdeal p.1.1.toIdeal rfl) _ _
  map_mul' x y := by
    apply Subtype.ext
    funext p
    let : p.1.1.toIdeal.IsPrime := p.1.isPrime
    exact map_mul (mapLocalRing f d hdeg
      (comapPoint f d hd hdeg hbase p.1).1.toIdeal p.1.1.toIdeal rfl) _ _

def projectiveSheafMap : Proj.toSheafedSpace ℬ ⟶ Proj.toSheafedSpace 𝒜 where
  hom :=
    { base := TopCat.ofHom (comapContinuous f d hd hdeg hbase)
      c :=
        { app U := by
            exact @CommRingCat.ofHom
              ((Proj.structureSheaf 𝒜).1.obj U)
              ((Proj.structureSheaf ℬ).1.obj
                (op (U.unop.comap (comapContinuous f d hd hdeg hbase))))
              inferInstance inferInstance
              (comapSections f d hd hdeg hbase _ _ Set.Subset.rfl) } }


lemma germ_map_section {p : ProjectiveSpectrum ℬ}
    (c : NumDenSameDeg 𝒜 (comapPoint f d hd hdeg hbase p).1.toIdeal.primeCompl) :
    (toSheafedSpace ℬ).presheaf.germ
      ((Opens.map (projectiveSheafMap f d hd hdeg hbase).hom.base).obj _) p
      (mem_basicOpen_den _ _ _)
      ((projectiveSheafMap f d hd hdeg hbase).hom.c.app _
        (sectionInBasicOpen 𝒜 _ c)) =
    (toSheafedSpace ℬ).presheaf.germ (ProjectiveSpectrum.basicOpen _ (f c.den)) p c.4
      (sectionInBasicOpen ℬ p (mapFraction f d hdeg le_rfl c)) := rfl

lemma localRingMap_comp_stalkIso (p : ProjectiveSpectrum ℬ) :
    (stalkIso 𝒜 (comapPoint f d hd hdeg hbase p)).hom ≫
      CommRingCat.ofHom (mapLocalRing f d hdeg _ _ rfl) ≫ (stalkIso ℬ p).inv =
      (projectiveSheafMap f d hd hdeg hbase).hom.stalkMap p := by
  erw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change mapLocalRing f d hdeg _ _ rfl x =
    (stalkIso' ℬ p) ((projectiveSheafMap f d hd hdeg hbase).hom.stalkMap p
      ((stalkIso' 𝒜 (comapPoint f d hd hdeg hbase p)).symm x))
  obtain ⟨c, rfl⟩ := x.mk_surjective
  erw [stalkIso'_symm_mk, PresheafedSpace.stalkMap_germ_apply,
    germ_map_section, stalkIso'_germ]
  rfl

 
private lemma isUnit_of_ringIso {R S : CommRingCat.{u}} (e : R ≅ S) (x : R)
    (hx : IsUnit (e.hom.hom x)) : IsUnit x := by
  have : IsLocalHom e.hom.hom := isLocalHom_of_isIso _
  exact (isUnit_map_iff e.hom.hom x).mp hx

def projectiveMap : Proj ℬ ⟶ Proj 𝒜 where
  __ := (projectiveSheafMap f d hd hdeg hbase).hom
  prop p := .mk fun x hx ↦ by
    erw [← localRingMap_comp_stalkIso f d hd hdeg hbase p] at hx
    let : p.1.toIdeal.IsPrime := p.isPrime
    change IsUnit ((stalkIso ℬ p).inv.hom
      (mapLocalRing f d hdeg (comapPoint f d hd hdeg hbase p).1.toIdeal
        p.1.toIdeal rfl
        ((stalkIso 𝒜 (comapPoint f d hd hdeg hbase p)).hom.hom x))) at hx
    have : IsLocalHom (stalkIso ℬ p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff (stalkIso ℬ p).inv.hom _).mp hx
    replace hx := isUnit_of_mapLocalRing f d hdeg
      (comapPoint f d hd hdeg hbase p).1.toIdeal p.1.toIdeal rfl hx
    exact isUnit_of_ringIso (stalkIso 𝒜 (comapPoint f d hd hdeg hbase p)) x hx

@[simp] theorem preimage_basicOpen (a : A) :
    projectiveMap f d hd hdeg hbase ⁻¹ᵁ Proj.basicOpen 𝒜 a =
      Proj.basicOpen ℬ (f a) := rfl

end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ProjectiveSpectrum
universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

 

def HasCoordinatePullback (f : A →+* B) (Φ : Proj ℬ ⟶ Proj 𝒜) : Prop :=
  (∀ p : ProjectiveSpectrum ℬ,
    (Φ.base p).1.toIdeal = p.1.toIdeal.comap f) ∧
  (∀ (U : Opens (ProjectiveSpectrum 𝒜))
    (s : (Proj.structureSheaf 𝒜).1.obj (op U))
    (p : ((Opens.map Φ.base).obj U)),
    ∀ h : (Φ.base p.1).1.toIdeal = p.1.1.toIdeal.comap f,
    letI : (Φ.base p.1).1.toIdeal.IsPrime := (Φ.base p.1).isPrime
    let : p.1.1.toIdeal.IsPrime := p.1.isPrime
    (((Φ.c.app (op U)) s).val p).val =
      Localization.localRingHom _ _ f h (s.val ⟨Φ.base p.1, p.2⟩).val)

theorem degreeScalingProjMap (f : A →+* B) (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ n {a : A}, a ∈ 𝒜 n → f a ∈ ℬ (d * n))
    (hbase : ∀ p : ProjectiveSpectrum ℬ,
      ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ p.1.toIdeal.comap f) :
    ∃ Φ : Proj ℬ ⟶ Proj 𝒜, HasCoordinatePullback 𝒜 ℬ f Φ := by
  refine ⟨projectiveMap f d hd hdeg hbase, ⟨fun p ↦ rfl, ?_⟩⟩
  intro U s p h
  let : ((projectiveMap f d hd hdeg hbase).base p.1).1.toIdeal.IsPrime :=
    ((projectiveMap f d hd hdeg hbase).base p.1).isPrime
  let : p.1.1.toIdeal.IsPrime := p.1.isPrime
  exact val_mapLocalRing (𝒜 := 𝒜) (ℬ := ℬ) f d hdeg _ _ h _

end
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousLocalization
  ProjectiveSpectrum Proj ProjectiveSpectrum.StructureSheaf
universe u
lemma topIso_inv_appTop (X : Scheme.{u}) :
    X.topIso.inv.app ⊤ = (⊤ : X.Opens).topIso.hom := by
  apply (cancel_mono (⊤ : X.Opens).topIso.inv).mp
  rw [Iso.hom_inv_id]
  have h := Scheme.Hom.congr_app (Scheme.ι_toIso_inv X) ⊤
  simp only [Scheme.Hom.comp_app, Scheme.Hom.preimage_top,
    Scheme.Opens.ι_app, Scheme.Hom.id_app] at h ⊢
  convert h using 1
  · congr 1
  · change 𝟙 _ = 𝟙 _ ≫ (⊤ : X.Opens).toScheme.presheaf.map (𝟙 (op ⊤))
    erw [CategoryTheory.Functor.map_id, Category.id_comp]

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

lemma toSpecZero_section (a : 𝒜 0) (p : ProjectiveSpectrum 𝒜) :
    (((Scheme.ΓSpecIso (.of (𝒜 0))).inv ≫
      Scheme.Hom.appTop (AlgebraicGeometry.Proj.toSpecZero 𝒜)) a).val ⟨p, trivial⟩ =
        fromZeroRingHom 𝒜 p.1.toIdeal.primeCompl a := by
  simp only [AlgebraicGeometry.Proj.toSpecZero, Scheme.Hom.appTop,
    Scheme.Hom.comp_app, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_top,
    AlgebraicGeometry.Proj.basicOpenToSpec_app_top]
  simp
  rw [← CommRingCat.comp_apply]
  simp only [Scheme.isoOfEq_inv, Scheme.homOfLE_app, topIso_inv_appTop,
    Scheme.Opens.topIso_hom]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

lemma mapLocalRing_fromZero (f : A →+* B) (d : ℕ)
    (hdeg : ∀ n {a : A}, a ∈ 𝒜 n → f a ∈ ℬ (d * n))
    (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime] (hIJ : I = J.comap f)
    (a : 𝒜 0) :
    mapLocalRing f d hdeg I J hIJ (fromZeroRingHom 𝒜 I.primeCompl a) =
      fromZeroRingHom ℬ J.primeCompl
        ⟨f a, by simpa only [mul_zero] using hdeg 0 a.2⟩ := by
  apply HomogeneousLocalization.val_injective
  rw [val_mapLocalRing]
  change Localization.localRingHom I J f hIJ (Localization.mk (a : A) 1) =
    Localization.mk (f a) 1
  simp
  rfl

end CampanaPeternellSix.ProjectiveCoordinates
namespace CampanaPeternellSix.RelativePolynomialEvaluation
open CategoryTheory AlgebraicGeometry ProjectiveSpectrum Opposite
universe u
variable (R : Type u) [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
abbrev grading (n : ℕ) := MvPolynomial.homogeneousSubmodule (Fin (n+1)) R
def space (n : ℕ) : Scheme := Proj (grading R n)
def constants (n : ℕ) : R →+* grading R n 0 where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)
def toBase (n : ℕ) : space R n ⟶ Spec (.of R) :=
  AlgebraicGeometry.Proj.toSpecZero (grading R n) ≫ Spec.map (CommRingCat.ofHom (constants R n))

open HomogeneousLocalization CampanaPeternellSix.ProjectiveCoordinates
lemma toBase_section (n : ℕ) (a : R) (p : ProjectiveSpectrum (grading R n)) :
    (((Scheme.ΓSpecIso (.of R)).inv ≫ (toBase R n).appTop) a).val ⟨p, trivial⟩ =
      fromZeroRingHom (grading R n) p.1.toIdeal.primeCompl (constants R n a) := by
  erw [toBase, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  exact toSpecZero_section (constants R n a) p

variable (n d : ℕ) (hd : 0 < d)
  (P : Fin (n+1) → MvPolynomial (Fin 2) R)
  (hhom : ∀ i, (P i).IsHomogeneous d)
  (hfree : ∀ p : ProjectiveSpectrum (grading R 1), ∃ i, P i ∉ p.1)

include hhom in
lemma tuple_homogeneous (k : ℕ) {a : MvPolynomial (Fin (n+1)) R}
    (ha : a ∈ grading R n k) :
    (MvPolynomial.aeval P).toRingHom a ∈ grading R 1 (d*k) :=
  MvPolynomial.IsHomogeneous.aeval ha P hhom

include hfree in
lemma tuple_admissible (p : ProjectiveSpectrum (grading R 1)) :
    ¬ (HomogeneousIdeal.irrelevant (grading R n)).toIdeal ≤
      p.1.toIdeal.comap (MvPolynomial.aeval P).toRingHom := by
  obtain ⟨i, hi⟩ := hfree p
  intro h
  apply hi
  have hx : MvPolynomial.X i ∈ HomogeneousIdeal.irrelevant (grading R n) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ (Nat.zero_lt_one)
      (MvPolynomial.isHomogeneous_X R i)
  have := h hx
  simpa using this

 

def evaluation : space R 1 ⟶ space R n :=
  CampanaPeternellSix.ProjectiveCoordinates.projectiveMap
    (MvPolynomial.aeval P).toRingHom d hd (tuple_homogeneous R n d P hhom)
    (tuple_admissible R n P hfree)

lemma evaluation_coordinates :
    CampanaPeternellSix.ProjectiveCoordinates.HasCoordinatePullback
      (grading R n) (grading R 1) (MvPolynomial.aeval P).toRingHom
        (evaluation R n d hd P hhom hfree) := by
  constructor
  · intro p; rfl
  · intro U s p h
    let : ((evaluation R n d hd P hhom hfree).base p.1).1.toIdeal.IsPrime :=
      ((evaluation R n d hd P hhom hfree).base p.1).isPrime
    let : p.1.1.toIdeal.IsPrime := p.1.isPrime
    exact CampanaPeternellSix.ProjectiveCoordinates.val_mapLocalRing
      (𝒜 := grading R n) (ℬ := grading R 1) (MvPolynomial.aeval P).toRingHom
      d (tuple_homogeneous R n d P hhom) _ _ h _
lemma evaluation_overBase :
    evaluation R n d hd P hhom hfree ≫ toBase R n = toBase R 1 := by
  apply ext_to_Spec
  simp only [Scheme.Γ_map_op, Scheme.Hom.comp_appTop]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply Subtype.ext
  funext p
  let e := evaluation R n d hd P hhom hfree
  let s := ((Scheme.ΓSpecIso (.of R)).inv ≫ (toBase R n).appTop) a
  change (((e.c.app (op ⊤)) s).val p) =
    ((((Scheme.ΓSpecIso (.of R)).inv ≫ (toBase R 1).appTop) a).val p)
  apply HomogeneousLocalization.val_injective
  let h := evaluation_coordinates R n d hd P hhom hfree
  erw [h.2 ⊤ s p (h.1 p.1)]
  let : (e.base p.1).1.toIdeal.IsPrime := (e.base p.1).isPrime
  let : p.1.1.toIdeal.IsPrime := p.1.isPrime
  change Localization.localRingHom (e.base p.1).1.toIdeal p.1.1.toIdeal
    (MvPolynomial.aeval P).toRingHom (h.1 p.1)
    (s.val ⟨e.base p.1, trivial⟩).val = _
  dsimp only [s]
  erw [toBase_section R n a, toBase_section R 1 a p.1]
  change Localization.localRingHom (e.base p.1).1.toIdeal p.1.1.toIdeal
    (MvPolynomial.aeval P).toRingHom (h.1 p.1)
      (Localization.mk (MvPolynomial.C a) 1) = Localization.mk (MvPolynomial.C a) 1
  simp
  rfl

 

theorem homogeneousTupleMap (n d : ℕ) (hd : 0 < d)
    (P : Fin (n+1) → MvPolynomial (Fin 2) R)
    (hhom : ∀ i, (P i).IsHomogeneous d)
    (hfree : ∀ p : ProjectiveSpectrum (grading R 1), ∃ i, P i ∉ p.1) :
    ∃ e : space R 1 ⟶ space R n,
      e ≫ toBase R n = toBase R 1 ∧
      CampanaPeternellSix.ProjectiveCoordinates.HasCoordinatePullback
        (grading R n) (grading R 1) (MvPolynomial.aeval P).toRingHom e :=
  ⟨evaluation R n d hd P hhom hfree,
    evaluation_overBase R n d hd P hhom hfree,
    evaluation_coordinates R n d hd P hhom hfree⟩

end CampanaPeternellSix.RelativePolynomialEvaluation

end

end OAI
