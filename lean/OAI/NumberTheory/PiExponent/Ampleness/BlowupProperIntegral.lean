import OAI.NumberTheory.PiExponent.Ampleness.BlowupComplement
import OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing
import OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupRestriction

namespace OAI


noncomputable section

namespace PiExponentSeshadri
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

instance AffineBlowup.projection_proper {X : Scheme.{0}} [IsAffine X]
    [IsLocallyNoetherian X] (I : X.IdealSheafData) : IsProper (AffineBlowup.projection I) := by
  let : IsNoetherianRing Γ(X,⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤,isAffineOpen_top X⟩
  unfold AffineBlowup.projection
  infer_instance

instance BlowupGluing.projection_proper {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) : IsProper (BlowupGluing.projection I) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper) (BlowupGluing.baseCover I)
  intro U
  let he := (BlowupGluing.local_pullback I U).flip.isoPullback
  have hh : he.hom ≫ pullback.snd (BlowupGluing.projection I) U.toOpens.ι =
      BlowupGluing.localProjection I U := by
    exact (BlowupGluing.local_pullback I U).flip.isoPullback_hom_snd
  have h : IsProper (BlowupGluing.localProjection I U) := by infer_instance
  rw [← hh] at h
  exact (MorphismProperty.cancel_left_of_respectsIso (@IsProper) he.hom _).mp h

end PiExponentSeshadri



namespace PiExponentSeshadri.ProjectiveGeometry
open AlgebraicGeometry
universe u v
variable {A : Type u} {σ : Type v} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

instance homogeneous_isReduced (S : Submonoid A) [_root_.IsReduced A] :
    _root_.IsReduced (HomogeneousLocalization 𝒜 S) :=
  isReduced_of_injective (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S))
    (HomogeneousLocalization.val_injective S)

instance proj_isReduced [_root_.IsReduced A] : IsReduced (Proj 𝒜) := by
  have (x : Proj 𝒜) : _root_.IsReduced ((Proj 𝒜).presheaf.stalk x) :=
    isReduced_of_injective (Proj.stalkIso' 𝒜 x) (Proj.stalkIso' 𝒜 x).injective
  exact isReduced_of_isReduced_stalk _

def genericPoint [IsDomain A] [Nonempty (Proj 𝒜)] : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := ⊥
  isPrime := Ideal.isPrime_bot
  not_irrelevant_le h := by
    obtain ⟨x⟩ := ‹Nonempty (Proj 𝒜)›
    exact x.not_irrelevant_le (h.trans bot_le)

lemma genericPoint_dense [IsDomain A] [Nonempty (Proj 𝒜)] :
    closure ({genericPoint 𝒜} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 _ _).mp
    (show (genericPoint 𝒜).asHomogeneousIdeal ≤ x.asHomogeneousIdeal from bot_le)

instance proj_irreducible [IsDomain A] [Nonempty (Proj 𝒜)] :
    IrreducibleSpace (Proj 𝒜) := by
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum 𝒜))
  rw [← genericPoint_dense 𝒜]
  exact (isIrreducible_singleton).closure

instance proj_isIntegral [IsDomain A] [Nonempty (Proj 𝒜)] : IsIntegral (Proj 𝒜) :=
  (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩

end PiExponentSeshadri.ProjectiveGeometry

namespace PiExponentSeshadri.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

abbrev centreComplement (I : X.IdealSheafData) : X.Opens := I.support.compl

lemma ideal_comap_complement (I : X.IdealSheafData) :
    I.comap (centreComplement I).ι = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext x
  change (x.val ∈ I.support ↔ False)
  exact iff_false_intro x.property

lemma complement_nonempty (hI : I.support ≠ ⊤) : Nonempty (centreComplement I).toScheme := by
  by_contra h
  apply hI
  ext x
  change x ∈ I.support ↔ True
  rw [iff_true]
  by_contra hx
  exact h ⟨⟨x, hx⟩⟩

def IsBlowup.complementLift (hπ : IsBlowup I π) : (centreComplement I).toScheme ⟶ B := by
  let := hπ.isIso_over_complement
  exact inv (pullback.fst (centreComplement I).ι π) ≫
    pullback.snd (centreComplement I).ι π

@[reassoc (attr := simp)]
lemma IsBlowup.complementLift_comp (hπ : IsBlowup I π) :
    hπ.complementLift ≫ π = (centreComplement I).ι := by
  let := hπ.isIso_over_complement
  dsimp only [IsBlowup.complementLift]
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
    Category.id_comp]

instance (hπ : IsBlowup I π) : IsOpenImmersion hπ.complementLift := by
  let := hπ.isIso_over_complement
  dsimp only [IsBlowup.complementLift]
  infer_instance

lemma IsBlowup.complementLift_range (hπ : IsBlowup I π) :
    Set.range hπ.complementLift = π ⁻¹' (centreComplement I : Set X) := by
  let := hπ.isIso_over_complement
  change Set.range ((pullback.snd (centreComplement I).ι π) ∘
    (inv (pullback.fst (centreComplement I).ι π))) = _
  rw [Set.range_comp]
  rw [(inv (pullback.fst (centreComplement I).ι π)).surjective.range_eq,
    Set.image_univ, Scheme.Pullback.range_snd]
  simp

lemma IsBlowup.nonempty_of_support_ne_top (hπ : IsBlowup I π) (hI : I.support ≠ ⊤) :
    Nonempty B :=
  (complement_nonempty hI).map hπ.complementLift

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.ReesGrading
open AlgebraicGeometry Polynomial
variable {R : Type} [CommRing R] (I : Ideal R)

instance polynomial_isReduced [_root_.IsReduced R] : _root_.IsReduced R[X] where
  eq_zero p hp := by
    ext n
    exact (Polynomial.isNilpotent_iff.mp hp n).eq_zero

instance affineBlowup_isReduced [_root_.IsReduced R] : IsReduced (affineBlowup I) := by
  let : _root_.IsReduced (reesAlgebra I) :=
    isReduced_of_injective (reesAlgebra I).val Subtype.val_injective
  exact ProjectiveGeometry.proj_isReduced (piece I)

instance affineBlowup_isIntegral [IsDomain R] [Nonempty (affineBlowup I)] :
    IsIntegral (affineBlowup I) := by
  let : IsDomain (reesAlgebra I) :=
    Function.Injective.isDomain (reesAlgebra I).val Subtype.val_injective
  let : Nonempty (Proj (piece I)) := ‹Nonempty (affineBlowup I)›
  exact ProjectiveGeometry.proj_isIntegral (piece I)

end PiExponentSeshadri.ReesGrading

namespace PiExponentSeshadri.AffineBlowup
open AlgebraicGeometry
variable {X : Scheme.{0}} [IsAffine X] (I : X.IdealSheafData)

instance scheme_isReduced [IsReduced X] : IsReduced (scheme I) := by
  dsimp only [scheme]
  infer_instance

instance scheme_isIntegral [IsIntegral X] [Nonempty (scheme I)] : IsIntegral (scheme I) := by
  dsimp only [scheme]
  infer_instance

end PiExponentSeshadri.AffineBlowup

namespace PiExponentSeshadri.BlowupGluing
open AlgebraicGeometry
variable {X : Scheme.{0}} (I : X.IdealSheafData)

instance scheme_isReduced [IsReduced X] : IsReduced (scheme I) := by
  let : ∀ U : (cover I).I₀, IsReduced ((cover I).X U) := fun U => by
    change IsReduced (localScheme I U)
    infer_instance
  exact IsReduced.of_openCover _ (cover I)

end PiExponentSeshadri.BlowupGluing

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme.{0}} [IrreducibleSpace X] (I : X.IdealSheafData)

lemma support_comap_ne_top_of_open (hI : I.support ≠ ⊤) (j : Y ⟶ X)
    [IsOpenImmersion j] [Nonempty Y] : (I.comap j).support ≠ ⊤ := by
  have hc : (centreComplement I : Set X).Nonempty := by
    obtain ⟨x⟩ := complement_nonempty hI
    exact ⟨x.val, x.property⟩
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    j.isOpenEmbedding.isOpen_range (centreComplement I).isOpen (Set.range_nonempty j) hc
  intro he
  have hyn : y ∈ (I.comap j).support := by rw [he]; trivial
  rw [Scheme.IdealSheafData.support_comap] at hyn
  exact hy hyn

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.BlowupGluing
open AlgebraicGeometry CategoryTheory TopologicalSpace PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [IsIntegral X] (I : X.IdealSheafData)

lemma localScheme_isIntegral (hI : I.support ≠ ⊤) (U : X.AffineZariskiSite)
    [Nonempty U.toOpens.toScheme] : IsIntegral (localScheme I U) := by
  let : IsIntegral U.toOpens.toScheme := isIntegral_of_isOpenImmersion U.toOpens.ι
  let : Nonempty (localScheme I U) := (local_isBlowup I U).nonempty_of_support_ne_top
    (support_comap_ne_top_of_open I hI U.toOpens.ι)
  infer_instance

omit [IsIntegral X] in
lemma cover_range (U : X.AffineZariskiSite) :
    Set.range ((cover I).f U) = projection I ⁻¹' (U.toOpens : Set X) := by
  have h := ((gluing I).preimage_toBase_eq_range_ι U).symm
  change Set.range ((cover I).f U) = projection I ⁻¹' Set.range U.toOpens.ι at h
  simpa only [Scheme.Opens.range_ι] using h

lemma complement_dense (hI : I.support ≠ ⊤) :
    Dense (projection I ⁻¹' (centreComplement I : Set X)) := by
  rw [dense_iff_inter_open]
  intro V hV ⟨y, hyV⟩
  obtain ⟨U, z, rfl⟩ := (cover I).exists_eq y
  let : Nonempty U.toOpens.toScheme := ⟨localProjection I U z⟩
  let : IsIntegral ((cover I).X U) := localScheme_isIntegral I hI U
  have hc : (centreComplement I : Set X).Nonempty := by
    obtain ⟨x⟩ := complement_nonempty hI
    exact ⟨x.val, x.property⟩
  have hU : (U.toOpens : Set X).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty U.toOpens.toScheme›
    exact ⟨x.val, x.property⟩
  obtain ⟨x, hxU, hxc⟩ := nonempty_preirreducible_inter
    U.toOpens.isOpen (centreComplement I).isOpen hU hc
  let b : scheme I := (isBlowup I).complementLift ⟨x, hxc⟩
  have hpb : projection I b = x :=
    congrArg (fun f : (centreComplement I).toScheme ⟶ X => f ⟨x, hxc⟩)
      (isBlowup I).complementLift_comp
  have hbr : b ∈ Set.range ((cover I).f U) := by
    erw [cover_range I U]
    change projection I b ∈ U.toOpens
    rwa [hpb]
  obtain ⟨w, hw⟩ := hbr
  have hwc : (cover I).f U w ∈ projection I ⁻¹' (centreComplement I : Set X) := by
    change projection I ((cover I).f U w) ∈ centreComplement I
    rwa [hw, hpb]
  obtain ⟨q, hqV, hqc⟩ := nonempty_preirreducible_inter
    (hV.preimage ((cover I).f U).continuous)
    (((centreComplement I).isOpen.preimage (projection I).continuous).preimage
      ((cover I).f U).continuous) ⟨z, hyV⟩ ⟨w, hwc⟩
  exact ⟨(cover I).f U q, hqV, hqc⟩

lemma scheme_isIntegral (hI : I.support ≠ ⊤) : IsIntegral (scheme I) := by
  let : Nonempty (centreComplement I).toScheme := complement_nonempty hI
  let : IsIntegral (centreComplement I).toScheme :=
    isIntegral_of_isOpenImmersion (centreComplement I).ι
  have hi : IsIrreducible (Set.range (isBlowup I).complementLift) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := (centreComplement I).toScheme)).image
        (isBlowup I).complementLift (isBlowup I).complementLift.continuous.continuousOn
  have hd : Dense (Set.range (isBlowup I).complementLift) := by
    rw [Geometry.IsBlowup.complementLift_range]
    exact complement_dense I hI
  let : IrreducibleSpace (scheme I) := (irreducibleSpace_def _).mpr (by
    change IsIrreducible (Set.univ : Set (scheme I))
    rw [← hd.closure_eq]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end PiExponentSeshadri.BlowupGluing

end

end OAI
