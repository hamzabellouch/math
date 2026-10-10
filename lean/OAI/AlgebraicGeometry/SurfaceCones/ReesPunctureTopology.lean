import OAI.AlgebraicGeometry.SurfaceCones.KummerCompletedBlowup

namespace OAI


noncomputable section
namespace ReesProj
open Polynomial AlgebraicGeometry CategoryTheory
variable {R : Type} [CommRing R] {ι : Type} (s : ι → R)

lemma structuralMap_mem (I : Ideal R) (x : proj I) (r : R) :
    r ∈ (structuralMap I x).asIdeal ↔
      algebraMap R (reesAlgebra I) r ∈ x.asHomogeneousIdeal := by
  change zeroEquiv I r ∈ (Proj.toSpecZero (homogeneous I) x).asIdeal ↔ _
  exact ProjZeroPoints.toSpecZero_mem (homogeneous I) x (zeroEquiv I r)

lemma chartSection_relation (i j : ι) :
    algebraMap R (reesAlgebra (sectionIdeal s)) (s i) * chartSection s j =
      algebraMap R (reesAlgebra (sectionIdeal s)) (s j) * chartSection s i := by
  apply Subtype.ext
  change C (s i) * monomial 1 (s j) = C (s j) * monomial 1 (s i)
  simp only [C_mul_monomial, mul_comm]

/-- Away from a chosen source section, the entire blowup belongs to the
corresponding distinguished projective chart. -/
lemma preimage_basicOpen_le_chart (i : ι) :
    (structuralMap (sectionIdeal s)) ⁻¹ᵁ (PrimeSpectrum.basicOpen (s i)) ≤
      Proj.basicOpen (homogeneous (sectionIdeal s)) (chartSection s i) := by
  intro x hx
  change ¬ chartSection s i ∈ x.asHomogeneousIdeal
  intro hxi
  have hi : ¬ algebraMap R (reesAlgebra (sectionIdeal s)) (s i) ∈
      x.asHomogeneousIdeal := by
    exact (structuralMap_mem _ x (s i)).not.mp hx
  have hall : ∀ j, chartSection s j ∈ x.asHomogeneousIdeal := by
    intro j
    have hm : algebraMap R (reesAlgebra (sectionIdeal s)) (s i) * chartSection s j ∈
        x.asHomogeneousIdeal := by
      rw [chartSection_relation s i j]
      exact x.asHomogeneousIdeal.toIdeal.mul_mem_left _ hxi
    exact (x.isPrime.mem_or_mem hm).resolve_left hi
  have htop := chartSections_cover s
  have hxcover : x ∈ (⨆ j, Proj.basicOpen (homogeneous (sectionIdeal s)) (chartSection s j)) := by
    rw [htop]; trivial
  obtain ⟨j,hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
  exact hj (hall j)

end ReesProj


namespace FractionalAlgebraAway
open AlgebraicGeometry CategoryTheory
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
  [IsDomain B] (t : R)
  (hf : Function.Injective (algebraMap R B)) (ht : t ≠ 0)
  {ι : Type*} (v : ι → B) (s : ι → R)
  (hgen : Algebra.adjoin R (Set.range v) = ⊤)
  (hrel : ∀ i, v i * algebraMap R B t = algebraMap R B (s i))

lemma awayMap_eq_equiv :
    Localization.awayMap (algebraMap R B) t =
      (sourceAwayEquiv t hf ht v s hgen hrel).symm.toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers t)
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply, Localization.awayMap,
    IsLocalization.Away.map, IsLocalization.map_eq]
  exact ((sourceAwayEquiv t hf ht v s hgen hrel).symm.commutes r).symm

include hf ht v s hgen hrel in
/-- A fraction-generated algebra gives the actual isomorphism over the
principal open, including the structural morphism. -/
theorem specMap_restrict_isIso :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap R B))) ∣_
      (PrimeSpectrum.basicOpen t)) := by
  have he := awayMap_eq_equiv t hf ht v s hgen hrel
  have : IsIso (CommRingCat.ofHom (Localization.awayMap (algebraMap R B) t)) := by
    rw [he]
    exact (sourceAwayEquiv t hf ht v s hgen hrel).symm.toRingEquiv.toCommRingCatIso.isIso_hom
  have : IsIso (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap R B) t))) :=
    inferInstance
  exact (Arrow.isIso_iff_isIso_of_isIso
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom (algebraMap R B)) t).hom).mpr inferInstance

end FractionalAlgebraAway


open AlgebraicGeometry CategoryTheory
namespace SchemeRestrictionImage

lemma openImmersion_restrict_isIso {X Y : Scheme} (f : X ⟶ Y)
    [IsOpenImmersion f] (U : Y.Opens) (hU : U ≤ f.opensRange) : IsIso (f ∣_ U) := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ?_⟩
  rw [surjective_iff]
  intro x
  obtain ⟨y,hy⟩ := hU x.property
  refine ⟨⟨y,?_⟩,?_⟩
  · change f y ∈ U
    rw [hy]
    exact x.property
  · apply Subtype.ext
    exact (morphismRestrict_base_coe f U _).trans hy

/-- If an open chart contains the entire preimage of a target open, an
isomorphism for its composite is an isomorphism for the original map. -/
lemma isIso_of_chart {X Y Z : Scheme} (g : X ⟶ Y) (f : Y ⟶ Z)
    [IsOpenImmersion g] (U : Z.Opens)
    (hU : f ⁻¹ᵁ U ≤ g.opensRange) [IsIso ((g ≫ f) ∣_ U)] : IsIso (f ∣_ U) := by
  let := openImmersion_restrict_isIso g (f ⁻¹ᵁ U) hU
  have hcomp : IsIso ((g ≫ f) ∣_ U) := inferInstance
  rw [morphismRestrict_comp] at hcomp
  exact (isIso_comp_left_iff (g ∣_ (f ⁻¹ᵁ U)) (f ∣_ U)).mp hcomp

/-- Being an isomorphism over each member of a family is enough over its
union, with no quasi-compactness or finiteness assumption. -/
lemma isIso_restrict_iSup {X Y : Scheme} (f : X ⟶ Y) {ι : Type}
    (U : ι → Y.Opens) (hU : ∀ i, IsIso (f ∣_ U i)) : IsIso (f ∣_ iSup U) := by
  let V := iSup U
  let W : ι → V.toScheme.Opens := fun i => V.ι ⁻¹ᵁ U i
  have hcover : iSup W = ⊤ := by
    change (⨆ i, V.ι ⁻¹ᵁ U i) = ⊤
    rw [← Scheme.Hom.preimage_iSup]
    exact V.ι_preimage_self
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    W hcover
  intro i
  change IsIso ((f ∣_ V) ∣_ W i)
  apply (Arrow.isIso_iff_isIso_of_isIso (morphismRestrictRestrict f V (W i)).hom).mpr
  have he : V.ι ''ᵁ W i = U i := by
    rw [show W i = V.ι ⁻¹ᵁ U i from rfl,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (le_iSup U i)
  rw [he]
  exact hU i

end SchemeRestrictionImage

end


noncomputable section
namespace ReesProj
open AlgebraicGeometry CategoryTheory
variable {R K : Type} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
variable {ι : Type} (s : ι → R) (i : ι) (hi : s i ≠ 0)

omit [IsDomain R] in
lemma fractionChartInclusion_opensRange :
    (fractionChartInclusion (K := K) s (s i) (Ideal.subset_span (Set.mem_range_self i)) hi).opensRange =
    Proj.basicOpen (homogeneous (sectionIdeal s)) (chartSection s i) := by
  let ht : s i ∈ sectionIdeal s := Ideal.subset_span (Set.mem_range_self i)
  let f := (Scheme.Spec.mapIso
    (generatedChartEquiv (K := K) s (s i) ht hi).toRingEquiv.toCommRingCatIso.op).hom
  let g := Proj.awayι (homogeneous (sectionIdeal s))
    (linearSection (sectionIdeal s) (s i) ht)
    (linearSection_homogeneous _ _ _) (by decide : 0 < (1 : ℕ))
  change (f ≫ g).opensRange = _
  have : IsOpenImmersion g := by dsimp [g]; infer_instance
  exact (Scheme.Hom.opensRange_comp_of_isIso f g).trans
    (Proj.opensRange_awayι (homogeneous (sectionIdeal s))
      (linearSection (sectionIdeal s) (s i) ht)
      (linearSection_homogeneous _ _ _) (by decide : 0 < (1 : ℕ)))

include hi in
/-- The actual proper Rees-Proj morphism is an isomorphism over every
source principal open belonging to its ideal of sections. -/
theorem structuralMap_restrict_section_isIso :
    IsIso ((structuralMap (sectionIdeal s)) ∣_ (PrimeSpectrum.basicOpen (s i))) := by
  let g := fractionChartInclusion (K := FractionRing R) s (s i)
    (Ideal.subset_span (Set.mem_range_self i)) hi
  have : IsOpenImmersion g := inferInstance
  have : IsIso ((g ≫ structuralMap (sectionIdeal s)) ∣_ PrimeSpectrum.basicOpen (s i)) := by
    dsimp only [g]
    rw [fractionChartInclusion_structuralMap]
    exact FractionalAlgebraAway.specMap_restrict_isIso (s i)
      (fractionChartScalar_injective (K := FractionRing R) s (s i)) hi
      (fractionChartRatio s (s i)) s (fractionChartRatio_generate s (s i))
      (fractionChartRatio_relation s (s i) hi)
  apply SchemeRestrictionImage.isIso_of_chart g (structuralMap (sectionIdeal s))
    (PrimeSpectrum.basicOpen (s i))
  rw [show g.opensRange = _ from fractionChartInclusion_opensRange (K := FractionRing R) s i hi]
  exact preimage_basicOpen_le_chart s i

/-- The ordinary blowup is canonically the identity off the vanishing set
of its nonzero chosen source sections. -/
theorem structuralMap_restrict_union_isIso (hs : ∀ j, s j ≠ 0) :
    IsIso ((structuralMap (sectionIdeal s)) ∣_
      (⨆ j, PrimeSpectrum.basicOpen (s j))) := by
  exact SchemeRestrictionImage.isIso_restrict_iSup _ _
    (fun j => structuralMap_restrict_section_isIso s j (hs j))

end ReesProj


namespace ExplicitCone
open AlgebraicGeometry CategoryTheory

/-- The open punctured spectrum is defined by the eighteen literal
source sections; its complement is proved to be precisely the closed point. -/
def completedPunctureOpen : (Spec (.of completedRing)).Opens :=
  ⨆ i : Fin 6 × Fin 3, PrimeSpectrum.basicOpen (completedSection i)

theorem completedPunctureOpen_coe :
    (completedPunctureOpen.1 : Set (PrimeSpectrum completedRing)) = {completedClosedPoint}ᶜ := by
  exact (TopologicalSpace.Opens.coe_iSup
    (fun i : Fin 6 × Fin 3 => PrimeSpectrum.basicOpen (completedSection i))).trans
    completedPuncture_sectionCover

/-- The actual proper eighteen-section Rees blowup is an isomorphism over
the entire punctured spectrum, not just on a distinguished point or chart. -/
instance completedBlowupMap_puncture_isIso :
    IsIso (completedBlowupMap ∣_ completedPunctureOpen) :=
  ReesProj.structuralMap_restrict_union_isIso completedSection completedSection_ne_zero

def completedBlowupPunctureIso :
    (completedBlowupMap ⁻¹ᵁ completedPunctureOpen).toScheme ≅
      completedPunctureOpen.toScheme :=
  asIso (completedBlowupMap ∣_ completedPunctureOpen)

/-- This isomorphism is the restriction of the fixed proper structural
morphism of the actual completed-cone blowup. -/
lemma completedBlowupPunctureIso_hom_ι :
    completedBlowupPunctureIso.hom ≫ completedPunctureOpen.ι =
      (completedBlowupMap ⁻¹ᵁ completedPunctureOpen).ι ≫ completedBlowupMap :=
  morphismRestrict_ι completedBlowupMap completedPunctureOpen

end ExplicitCone


namespace ProjDomain
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {σ : Type*} {A : Type} [CommRing A] [IsDomain A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

lemma stalk_domain (x : Proj 𝒜) : IsDomain ((Proj 𝒜).presheaf.stalk x) := by
  have : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  let : IsDomain (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :=
    (HomogeneousLocalization.val_injective _).isDomain
      (algebraMap (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal)
        (Localization.AtPrime x.asHomogeneousIdeal.toIdeal))
  exact (Proj.stalkIso 𝒜 x).commRingCatIsoToRingEquiv.injective.isDomain
    (Proj.stalkIso 𝒜 x).hom.hom

/-- A nonzero positive homogeneous element makes (0) a genuine point of Proj. -/
def genericPoint (f : A) {n : ℕ} (hn : n ≠ 0) (hf : f ∈ 𝒜 n) (hfn : f ≠ 0) : Proj 𝒜 where
  asHomogeneousIdeal := ⊥
  isPrime := Ideal.isPrime_bot
  not_irrelevant_le := by
    intro h
    have hf' : f ∈ HomogeneousIdeal.irrelevant 𝒜 := by
      rw [HomogeneousIdeal.mem_irrelevant_iff]
      exact DirectSum.decompose_of_mem_ne 𝒜 hf hn
    exact hfn (h hf')

lemma genericPoint_specializes (f : A) {n : ℕ} (hn : n ≠ 0)
    (hf : f ∈ 𝒜 n) (hfn : f ≠ 0) (x : Proj 𝒜) :
    genericPoint 𝒜 f hn hf hfn ⤳ x := by
  rw [specializes_iff_mem_closure]
  exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 _ _).mp (show
    (genericPoint 𝒜 f hn hf hfn).asHomogeneousIdeal ≤ x.asHomogeneousIdeal from bot_le)

/-- Integrality of the literal Proj of a domain; no smoothness assumption. -/
theorem integral (f : A) {n : ℕ} (hn : n ≠ 0) (hf : f ∈ 𝒜 n) (hfn : f ≠ 0) :
    IsIntegral (Proj 𝒜) := by
  let (x : Proj 𝒜) : IsDomain ((Proj 𝒜).presheaf.stalk x) := stalk_domain 𝒜 x
  let : IsReduced (Proj 𝒜) := isReduced_of_isReduced_stalk _
  have hg : IsGenericPoint (genericPoint 𝒜 f hn hf hfn) Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact specializes_iff_mem_closure.mp (genericPoint_specializes 𝒜 f hn hf hfn x)
  let : IrreducibleSpace (Proj 𝒜) := (irreducibleSpace_def _).mpr hg.isIrreducible
  exact isIntegral_of_irreducibleSpace_of_isReduced _
end ProjDomain


namespace ProperLocal
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {R : Type} [CommRing R] [IsLocalRing R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]

/-- Every point of a proper model over a local ring specializes to a point
of its closed fiber. -/
theorem specializes_closedFiber (x : X) :
    ∃ y : X, x ⤳ y ∧ f y = IsLocalRing.closedPoint R := by
  have hclosed := f.isClosedMap (closure ({x} : Set X)) isClosed_closure
  have hfx : f x ∈ f '' closure ({x} : Set X) :=
    Set.mem_image_of_mem _ (subset_closure (Set.mem_singleton x))
  have hmem : IsLocalRing.closedPoint R ∈ f '' closure ({x} : Set X) :=
    (IsLocalRing.specializes_closedPoint (f x)).mem_closed hclosed hfx
  obtain ⟨y, hy, he⟩ := hmem
  exact ⟨y, specializes_iff_mem_closure.mpr hy, he⟩

/-- A property stable under generalization and true on the closed fiber
holds on the proper model over a local ring. -/
theorem property_of_closedFiber (P : X → Prop)
    (hgen : ∀ {x y}, x ⤳ y → P y → P x)
    (hfiber : ∀ y, f y = IsLocalRing.closedPoint R → P y) : ∀ x, P x := by
  intro x
  obtain ⟨y, hxy, hy⟩ := specializes_closedFiber f x
  exact hgen hxy (hfiber y hy)
end ProperLocal


namespace ExplicitCone
open AlgebraicGeometry CategoryTheory

instance completedBlowup_locallyNoetherian : IsLocallyNoetherian completedBlowup := by
  let := actualCompletion_noetherian
  exact LocallyOfFiniteType.isLocallyNoetherian completedBlowupMap

lemma completedBlowupSection_ne_zero : completedBlowupSection ≠ 0 := by
  intro h
  apply completedSection_base_ne_zero
  have he := congrArg (fun p : Polynomial completedRing => p.coeff 1)
    (congrArg Subtype.val h)
  simpa [completedBlowupSection, ReesProj.linearSection] using he

/-- The projective Rees modification is integral. -/
instance completedBlowup_integral : IsIntegral completedBlowup :=
  ProjDomain.integral (ReesProj.homogeneous completedSectionIdeal)
    completedBlowupSection one_ne_zero (ReesProj.linearSection_homogeneous _ _ _)
    completedBlowupSection_ne_zero

/-- Every point of the actual model specializes into its closed fiber. -/
theorem completedBlowup_specializes_closedFiber (x : completedBlowup) :
    ∃ y : completedBlowup, x ⤳ y ∧ completedBlowupMap y = completedClosedPoint :=
  ProperLocal.specializes_closedFiber completedBlowupMap x

end ExplicitCone


namespace ExplicitCone
open AlgebraicGeometry CategoryTheory

/-- The closed fiber of the actual proper modification is nonempty; this
is proved from properness and integrality, not supplied as model data. -/
theorem completedBlowup_closedFiber_nonempty :
    ∃ x : completedBlowup, completedBlowupMap x = completedClosedPoint := by
  let x : completedBlowup := Classical.choice inferInstance
  obtain ⟨y, -, hy⟩ := completedBlowup_specializes_closedFiber x
  exact ⟨y, hy⟩

/-- The genuine model covers the entire completed local spectrum, including
the closed point. The puncture is the literal isomorphism already proved. -/
theorem completedBlowupMap_surjective : Function.Surjective completedBlowupMap := by
  intro x
  by_cases hx : x = completedClosedPoint
  · obtain ⟨y, hy⟩ := completedBlowup_closedFiber_nonempty
    exact ⟨y, hy.trans hx.symm⟩
  · have hu : x ∈ completedPunctureOpen := by
      change x ∈ (completedPunctureOpen.1 : Set (PrimeSpectrum completedRing))
      rw [completedPunctureOpen_coe]
      exact hx
    let u : completedPunctureOpen.toScheme := ⟨x, hu⟩
    let v := completedBlowupPunctureIso.inv u
    refine ⟨v.1, ?_⟩
    have he := congrArg (fun f : (completedBlowupMap ⁻¹ᵁ completedPunctureOpen).toScheme ⟶
      Spec (.of completedRing) => f v) completedBlowupPunctureIso_hom_ι
    have hv : completedBlowupPunctureIso.hom v = u := by
      exact congrArg (fun f : completedPunctureOpen.toScheme ⟶
        completedPunctureOpen.toScheme => f u) completedBlowupPunctureIso.inv_hom_id
    change (completedBlowupPunctureIso.hom v).1 = completedBlowupMap v.1 at he
    exact he.symm.trans (congrArg Subtype.val hv)

end ExplicitCone


namespace ReesProj
open AlgebraicGeometry CategoryTheory
variable {R : Type} [CommRing R]
    (I : Ideal R) (t : R) (ht : t ∈ I)

/-- The literal homogeneous affine chart, as a scheme over the base ring. -/
lemma homogeneousChartInclusion_structuralMap :
    Proj.awayι (homogeneous I) (linearSection I t ht)
      (linearSection_homogeneous I t ht) (by decide : 0 < (1 : ℕ)) ≫ structuralMap I =
    Spec.map (CommRingCat.ofHom
      (@algebraMap R (homogeneousChart I t ht) _ _ (homogeneousChartScalarAlgebra I t ht))) := by
  unfold structuralMap
  erw [← Category.assoc]
  erw [Proj.awayι_toSpecZero (homogeneous I) (linearSection I t ht)
    (linearSection_homogeneous I t ht) (by decide : 0 < (1 : ℕ))]
  simp only [Functor.mapIso_hom, Iso.op_hom, RingEquiv.toCommRingCatIso_hom,
    Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [← Spec.map_comp]
  congr 1
end ReesProj


namespace ExplicitCone
open AlgebraicGeometry CategoryTheory

/-- The actual open embedding of the distinguished homogeneous Rees chart. -/
abbrev completedChartInclusion : Spec (.of completedBlowupChart) ⟶ completedBlowup :=
  Proj.awayι (ReesProj.homogeneous completedSectionIdeal) completedBlowupSection
    (ReesProj.linearSection_homogeneous _ _ _) (by decide : 0 < (1 : ℕ))

instance completedChartInclusion_open : IsOpenImmersion completedChartInclusion := by
  change IsOpenImmersion (Proj.awayι (ReesProj.homogeneous completedSectionIdeal)
    completedBlowupSection (ReesProj.linearSection_homogeneous _ _ _)
    (by decide : 0 < (1 : ℕ)))
  infer_instance

/-- The intrinsic Proj chart is over the fixed completed ring by precisely
its scalar map, with actual equality of scheme morphisms. -/
lemma completedChartInclusion_map :
    completedChartInclusion ≫ completedBlowupMap =
      Spec.map (CommRingCat.ofHom (algebraMap completedRing completedBlowupChart)) :=
  ReesProj.homogeneousChartInclusion_structuralMap completedSectionIdeal
    (completedSection (0,0)) (completedSection_mem_ideal (0,0))
end ExplicitCone

end

end OAI
