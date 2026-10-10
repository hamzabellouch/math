import OAI.AlgebraicGeometry.SurfaceCones.CartierEquation

namespace OAI


/-! Injectivity of every completed source-chart ring map. These are needed to transport the positive
generic rank of the arbitrary input M. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace SourceConeMorphism
open KummerSourceModel
instance p_dominant : IsDominant p := by
  have : IsDominant ExplicitCone.completedPunctureOpen.ι :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
      ExplicitCone.completedPunctureOpen.ι.isOpenEmbedding.isOpenMap⟩
  have : IsDominant ((p ⁻¹ᵁ ExplicitCone.completedPunctureOpen).ι ≫ p) := by
    rw [← puncturedIso_hom_ι]
    infer_instance
  exact IsDominant.of_comp (p ⁻¹ᵁ ExplicitCone.completedPunctureOpen).ι p
end SourceConeMorphism
namespace SourcePullbackChart
open KummerSourceModel SourceConeMorphism
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra
instance completedSourceChart_nontrivial (i : Fin 3) : Nontrivial (completedSourceChart i) :=
  (completedZeroEvaluation_surjective i).nontrivial
instance completedSourceChart_integral (i : Fin 3) :
    IsIntegral (Spec (.of (completedSourceChart i))) := isIntegral_of_isOpenImmersion (completedIota i)
instance completedSourceChart_domain (i : Fin 3) : IsDomain (completedSourceChart i) :=
  (affine_isIntegral_iff (.of (completedSourceChart i))).mp inferInstance
instance completedIota_dominant (i : Fin 3) : IsDominant (completedIota i) :=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _ (completedIota i).isOpenEmbedding.isOpenMap⟩

/-- The coordinate map induced by `p` on the completed chart `Bᵢ ⊗[S] A`. -/
def completedConeMap (i : Fin 3) : CommRingCat.of ExplicitCone.completedRing ⟶
    CommRingCat.of (completedSourceChart i) :=
  Spec.preimage (completedIota i ≫ p)

lemma completedConeMap_spec (i : Fin 3) : Spec.map (completedConeMap i) = completedIota i ≫ p :=
  Spec.map_preimage _

lemma completedConeMap_injective (i : Fin 3) : Function.Injective (completedConeMap i) := by
  have : IsDominant (Spec.map (completedConeMap i)) := by
    rw [completedConeMap_spec]
    infer_instance
  have h := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    (completedConeMap i).hom).mp (Spec.map (completedConeMap i)).denseRange
  rw [nilradical_eq_zero] at h
  exact (RingHom.injective_iff_ker_eq_bot (completedConeMap i).hom).mpr (le_antisymm h bot_le)

end SourcePullbackChart

end


/-! The principal-divisor rank formula transported through a surjective affine coordinate map. -/
noncomputable section
open scoped TensorProduct
open TensorProduct
namespace PrincipalDivisorGeneric
variable {R D M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [CommRing D] [IsDomain D] [Algebra R D]
  [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.IsTorsionFree R M]
lemma surjection_rank (hsurj : Function.Surjective (algebraMap R D))
    (t : R) (ht : t ≠ 0) (hker : RingHom.ker (algebraMap R D) = Ideal.span {t}) :
    Module.finrank D (D ⊗[R] M) = Module.finrank R M := by
  have hquotient (q : Ideal R) [q.IsPrime] (h : q = Ideal.span {t}) :
      Module.finrank (R ⧸ q) ((R ⧸ q) ⊗[R] M) = Module.finrank R M := by
    subst q
    exact quotient_rank t ht
  let q := RingHom.ker (algebraMap R D)
  have : q.IsPrime := RingHom.ker_isPrime (algebraMap R D)
  have : (Ideal.span ({t} : Set R)).IsPrime := hker ▸ (inferInstance : q.IsPrime)
  let Q := R ⧸ q
  let e : Q ≃+* D := RingHom.quotientKerEquivOfSurjective hsurj
  let : Algebra Q D := e.toRingHom.toAlgebra
  have : IsScalarTower R Q D := IsScalarTower.of_algebraMap_eq fun r => by
    exact (RingHom.quotientKerEquivOfSurjective_apply_mk hsurj r).symm
  have hrank : Module.finrank Q (Q ⊗[R] M) = Module.finrank R M := by
    exact hquotient q hker
  rw [← (AlgebraTensorModule.cancelBaseChange R Q D D M).finrank_eq,
    DomainModuleRank.baseChange_rank D e.injective, hrank]

end PrincipalDivisorGeneric

end


/-! Exact generic rank of the exceptional restriction of E. The input is an arbitrary finite module
on R; it is not graded or an algebra. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace CoherentModelActual
open Scheme.Modules
lemma affineE_surjection_rank_eq {R B D : CommRingCat.{0}}
    [IsDomain R] [IsDomain B] [IsNoetherianRing B] [IsDomain D]
    (f : R ⟶ B) (M : ModuleCat R) [Module.Finite R M]
    (hf : Function.Injective f) (q : B ⟶ D) (hq : Function.Surjective q)
    (t : B) (ht : t ≠ 0) (hker : RingHom.ker q.hom = Ideal.span {t}) :
    Module.finrank D (moduleSpecΓFunctor.obj
      ((Scheme.Modules.pullback (Spec.map q)).obj (E (Spec.map f) M))) =
      Module.finrank R M := by
  let : Algebra R B := f.hom.toAlgebra
  let : Algebra B D := q.hom.toAlgebra
  let N := Module.Dual B (Module.Dual B (affineModule f M))
  have : IsNoetherian B N := isNoetherian_linearMap B B (Module.Dual B (affineModule f M))
  have : Module.Finite B N := ⟨IsNoetherian.noetherian ⊤⟩
  rw [(affineEPullbackGammaIso f M q).toLinearEquiv.finrank_eq]
  change Module.finrank D (D ⊗[B] N) = _
  rw [PrincipalDivisorGeneric.surjection_rank hq t ht hker]
  exact DomainModuleRank.doubleDual_baseChange_rank B hf
end CoherentModelActual
namespace SourceExceptionalRestriction
open KummerSourceModel SourcePullbackChart SourceZeroSections Scheme.Modules
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra

/-- The affine double-dual restriction model for `P` on each surface chart. -/
def chartModelIso (M : ModuleCat.{0} ExplicitCone.completedRing) (i : Fin 3) :
    (restrictFunctor (surfaceIota i)).obj (P M) ≅
      (Scheme.Modules.pullback (completedZeroChart i)).obj
        (CoherentModelActual.E (Spec.map (completedConeMap i)) M) :=
  chartPullbackIso _ i ≪≫
    (Scheme.Modules.pullback (completedZeroChart i)).mapIso
      ((restrictFunctorIsoPullback (completedIota i)).app _ ≪≫
        CoherentModelActual.openPullbackEIsoOfComp (completedIota i) SourceConeMorphism.p
          (Spec.map (completedConeMap i)) (completedConeMap_spec i).symm M)

abbrev chartSections (M : ModuleCat.{0} ExplicitCone.completedRing) (i : Fin 3) :=
  (moduleSpecΓFunctor (R := CommRingCat.of (surfaceChart i))).obj
    ((restrictFunctor (surfaceIota i)).obj (P M))

lemma chart_rank_eq (M : ModuleCat.{0} ExplicitCone.completedRing)
    [Module.Finite ExplicitCone.completedRing M] (i : Fin 3) :
    Module.finrank (surfaceChart i) (chartSections M i) =
      Module.finrank ExplicitCone.completedRing M := by
  rw [((moduleSpecΓFunctor (R := CommRingCat.of (surfaceChart i))).mapIso
    (chartModelIso M i)).toLinearEquiv.finrank_eq]
  apply CoherentModelActual.affineE_surjection_rank_eq (completedConeMap i) M
    (completedConeMap_injective i) (CommRingCat.ofHom (completedZeroEvaluation i))
    (completedZeroEvaluation_surjective i) (completedFiberParameter i)
  · intro h
    apply one_ne_zero (α := completedSourceChart i)
    apply completedFiberParameter_regular i
    simp [h]
  · exact completedZeroEvaluation_kernel i

lemma chart_rank_pos (M : ModuleCat.{0} ExplicitCone.completedRing)
    [Module.Finite ExplicitCone.completedRing M] [Nontrivial M]
    [Module.IsTorsionFree ExplicitCone.completedRing M] (i : Fin 3) :
    0 < Module.finrank (surfaceChart i) (chartSections M i) := by
  rw [chart_rank_eq M i]
  exact Module.finrank_pos

end SourceExceptionalRestriction

end


/-! The exceptional ideal on the completed source is invertible, with local equations given by the
completed fiber coordinates. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace SourceZeroSections
open KummerSourceModel SourcePullbackChart Scheme.Modules ActualCartier ActualSheafTensor
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra

def sourceIdealChartIso (i : Fin 3) :
    (restrictFunctor (completedIota i)).obj (idealSheaf completedSourceZero) ≅
      SheafOfModules.unit (Spec (.of (completedSourceChart i))).ringCatSheaf :=
  chartAffinePrincipalIdealUnitIso completedSourceZero
    (CommRingCat.ofHom (completedZeroEvaluation i)) (surfaceIota i) (completedIota i)
    (surfaceIota_completedSourceZero i) (by
      simpa only [Scheme.Hom.image_top_eq_opensRange] using (surfaceZero_chart_preimage i).symm)
    (completedFiberParameter i) (completedFiberParameter_regular i)
    (completedZeroEvaluation_kernel i)

/-- Line trivialization of the kernel ideal sheaf on W. -/
def sourceIdealLine : LineTrivialization W.sheaf (idealSheaf completedSourceZero) :=
  lineTrivializationOfCharts _ (fun i => Spec (.of (completedSourceChart i)))
    completedIota completedCover.iSup_opensRange sourceIdealChartIso

lemma sourceIdeal_coherent : (idealSheaf completedSourceZero).IsFinitePresentation :=
  idealSheaf_coherent _

end SourceZeroSections

end


/-! Preservation of torsion freedom by dominant pushforward. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace SheafTorsion
open Scheme.Modules

/-- Dominant quasi-compact pushforward between integral schemes preserves sectionwise torsion
freedom. -/
lemma pushforward {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [QuasiCompact f] (M : X.Modules)
    (hM : ∀ U, @Module.IsTorsionFree (X.sheaf.obj.obj U) (M.val.obj U) _ _
      (M.val.obj U).isModule)
    (U : Y.Opensᵒᵖ) : @Module.IsTorsionFree (Y.sheaf.obj.obj U)
      (((Scheme.Modules.pushforward f).obj M).val.obj U) _ _
      (((Scheme.Modules.pushforward f).obj M).val.obj U).isModule := by
  let : Module (Y.sheaf.obj.obj U) (((Scheme.Modules.pushforward f).obj M).val.obj U) :=
    (((Scheme.Modules.pushforward f).obj M).val.obj U).isModule
  let : Module Γ(X, f ⁻¹ᵁ U.unop) (M.val.obj (op (f ⁻¹ᵁ U.unop))) :=
    (M.val.obj (op (f ⁻¹ᵁ U.unop))).isModule
  have : IsSchemeTheoreticallyDominant f := .of_isDominant f
  by_cases hV : Nonempty (f ⁻¹ᵁ U.unop)
  · let := hV
    have : Nonempty U.unop := by
      obtain ⟨v⟩ := hV
      exact ⟨⟨f v.1, v.2⟩⟩
    have : IsDomain (Y.sheaf.obj.obj U) := IsIntegral.component_integral U.unop
    have : Module.IsTorsionFree Γ(X, f ⁻¹ᵁ U.unop)
        (M.val.obj (op (f ⁻¹ᵁ U.unop))) := hM _
    refine @Module.IsTorsionFree.mk (Y.sheaf.obj.obj U)
      (((Scheme.Modules.pushforward f).obj M).val.obj U) _ _
      (((Scheme.Modules.pushforward f).obj M).val.obj U).isModule ?_
    intro r hr x y hxy
    have hr0 : r ≠ 0 := isRegular_iff_ne_zero.mp hr
    have hs : f.app U.unop r ≠ 0 := by
      intro hs0
      exact hr0 ((f.app_injective U.unop) (hs0.trans (map_zero _).symm))
    apply (isRegular_iff_ne_zero.mpr hs).isSMulRegular
      (M := M.val.obj (op (f ⁻¹ᵁ U.unop)))
    exact hxy
  · have hz : f ⁻¹ᵁ U.unop = ⊥ := by
      ext v
      exact ⟨fun hv => (hV ⟨⟨v, hv⟩⟩).elim, False.elim⟩
    have : Subsingleton Γ(X, f ⁻¹ᵁ U.unop) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hz)
    have : Subsingleton (((Scheme.Modules.pushforward f).obj M).val.obj U) :=
      Module.subsingleton Γ(X, f ⁻¹ᵁ U.unop) (M.val.obj (op (f ⁻¹ᵁ U.unop)))
    exact @Subsingleton.to_moduleIsTorsionFree _ _ _ _
      (((Scheme.Modules.pushforward f).obj M).val.obj U).isModule this

/-- The torsion-free property is compatible with the exact finite pushforward on the coherent
categories. -/
lemma coherent_pushforward {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsDominant f] [IsFinite f]
    (M : CoherentGlobal.Coh X)
    (hM : ∀ U, @Module.IsTorsionFree (X.sheaf.obj.obj U) (M.obj.val.obj U) _ _
      (M.obj.val.obj U).isModule)
    (U : Y.Opensᵒᵖ) : @Module.IsTorsionFree (Y.sheaf.obj.obj U)
      (((CoherentGlobal.cohPushforward f).obj M).obj.val.obj U) _ _
      (((CoherentGlobal.cohPushforward f).obj M).obj.val.obj U).isModule :=
  pushforward f M.obj hM U
end SheafTorsion

end


/-! Integrality of the finite image of the integral source, using flatness of the line bundle
projection. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
open KummerSourceModel
local instance (i : Fin 3) : CommRing (planeChart i) := inferInstance
local instance (i : Fin 3) : Semiring (planeChart i) := (inferInstance : CommRing (planeChart i)).toSemiring
instance planeChart_domain (i : Fin 3) : IsDomain (planeChart i) :=
  Function.Injective.isDomain (planeField i) (planeField_injective i)
instance plane_reduced : IsReduced ExplicitCone.plane := by
  have (i : planeCover.I₀) : IsReduced (planeCover.X i) := by
    change Fin 3 at i
    change IsReduced (Spec (.of (planeChart i)))
    let : IsDomain (planeChart i) := planeChart_domain i
    infer_instance
  exact IsReduced.of_openCover _ planeCover

def blowupCover : V₀.OpenCover where
  I₀ := Fin 3
  X i := Spec (.of (chart i))
  f := blowupIota
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    have hx : x ∈ (⨆ i : Fin 3, Proj.basicOpen grades (sourceSection i)) := by
      rw [KummerSourceModel.sourceSections_cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hi' : x ∈ (blowupIota i).opensRange := by
      simpa only [blowupIota, Proj.opensRange_awayι] using hi
    obtain ⟨y, hy⟩ := hi'
    exact ⟨i, y, hy⟩

instance directionMap_flat (i : Fin 3) : Flat (Spec.map (CommRingCat.ofHom (directionMap i))) := by
  apply Flat.SpecMap_iff.mpr
  let : Algebra (planeChart i) (chart i) := (directionMap i).toAlgebra
  have : Module.Free (planeChart i) (chart i) :=
    Module.Free.of_equiv (planePolynomialEquiv i).toLinearEquiv
  have : Module.Flat (planeChart i) (chart i) := inferInstance
  exact RingHom.flat_algebraMap_iff.mpr this

instance direction_flat : Flat direction := by
  let : IsZariskiLocalAtSource (@Flat.{0}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ Flat.instHasRingHomPropertyFlat
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Flat.{0}) blowupCover).mpr
  intro i
  change Fin 3 at i
  change Flat (blowupIota i ≫ direction)
  rw [blowup_chart_square]
  infer_instance

instance completedDirection_flat : Flat completedDirection := by
  unfold completedDirection
  infer_instance

instance source_g_schematicallyDominant : IsSchemeTheoreticallyDominant g := by
  let : Surjective ExplicitCone.projectiveNormalization :=
    ⟨ExplicitCone.projectiveNormalization_surjective⟩
  let := ExplicitCone.projectiveNormalization_finite
  have : IsSchemeTheoreticallyDominant ExplicitCone.projectiveNormalization :=
    .of_isDominant _
  unfold g
  infer_instance

instance source_g_finite : IsFinite g := g_finite
instance source_g_surjective : Surjective g := g_surjective
instance source_V_integral : IsIntegral V := IsSchemeTheoreticallyDominant.isIntegral g
instance source_V_noetherian : IsLocallyNoetherian V :=
  LocallyOfFiniteType.isLocallyNoetherian completedBlowdown

abbrev modelPushforward (M : ModuleCat ExplicitCone.completedRing) : V.Modules :=
  (Scheme.Modules.pushforward g).obj (SourceConeMorphism.E M)

lemma modelPushforward_coherent (M : ModuleCat ExplicitCone.completedRing)
    [Module.Finite ExplicitCone.completedRing M] :
    (modelPushforward M).IsFinitePresentation := by
  let := SourceConeMorphism.E_coherent M
  exact CoherentGlobal.coherent_pushforward g _
lemma modelPushforward_torsionFree (M : ModuleCat ExplicitCone.completedRing)
    (U : V.Opensᵒᵖ) : @Module.IsTorsionFree (V.sheaf.obj.obj U)
      ((modelPushforward M).val.obj U) _ _
      ((modelPushforward M).val.obj U).isModule :=
  SheafTorsion.pushforward g (SourceConeMorphism.E M)
    (fun U => SourceConeMorphism.E_torsionFree M U.unop) U

end SourcePullbackChart

end

/-! The completed polynomial blowup identifies the complement of its zero section with the punctured
base. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
open KummerSourceModel
local instance (i : Fin 3) : CommRing (planeChart i) := inferInstance
local instance (i : Fin 3) : Semiring (planeChart i) := (inferInstance : CommRing (planeChart i)).toSemiring
local instance (i : Fin 3) : CommRing (chart i) := inferInstance
local instance (i : Fin 3) : Semiring (chart i) := (inferInstance : CommRing (chart i)).toSemiring
local instance chartBaseAlgebra (i : Fin 3) : Algebra S (chart i) := (baseMap i).toAlgebra
instance blowupChart_domain (i : Fin 3) : IsDomain (chart i) :=
  Function.Injective.isDomain (reesField i) (reesField_injective i)

abbrev chartRatio (i j : Fin 3) : chart i :=
  directionMap i (SectionCompletion.polynomialChartDehom i (MvPolynomial.X j))

lemma ratio_generate (i : Fin 3) : Algebra.adjoin S (Set.range (chartRatio i)) = ⊤ := by
  let B := Algebra.adjoin S (Set.range (chartRatio i))
  have hc (a : planeChart i) : directionMap i a ∈ B := by
    obtain ⟨v, rfl⟩ := polynomialChartDehom_surjective i a
    induction v using MvPolynomial.induction_on with
    | C a =>
      change directionMap i (SectionCompletion.polynomialChartDehom i (algebraMap ℂ S a)) ∈ B
      rw [(SectionCompletion.polynomialChartDehom i).commutes, directionMap_scalar]
      exact B.algebraMap_mem (MvPolynomial.C a)
    | add a b ha hb => simpa only [map_add] using B.add_mem ha hb
    | mul_X a j ha =>
      simp only [map_mul]
      exact B.mul_mem ha (Algebra.subset_adjoin (Set.mem_range_self j))
  have hq (q : Polynomial (planeChart i)) : planePolynomialEquiv i q ∈ B := by
    induction q using Polynomial.induction_on' with
    | add a b ha hb => simpa only [map_add] using B.add_mem ha hb
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
        planePolynomialEquiv_C, planePolynomialEquiv_X]
      exact B.mul_mem (hc a) (B.pow_mem (B.algebraMap_mem (MvPolynomial.X i)) n)
  apply top_unique
  intro z _
  obtain ⟨q, rfl⟩ := (planePolynomialEquiv i).surjective z
  exact hq q

lemma baseMap_restrict_isIso (i : Fin 3) :
    IsIso ((Spec.map (CommRingCat.ofHom (baseMap i))) ∣_
      PrimeSpectrum.basicOpen (MvPolynomial.X i)) := by
  have hinj : Function.Injective (algebraMap S (chart i)) := by
    intro a b h
    apply IsFractionRing.injective S K
    change baseMap i a = baseMap i b at h
    simpa only [reesField_base] using congrArg (reesField i) h
  exact FractionalAlgebraAway.specMap_restrict_isIso (R := S) (B := chart i)
    (MvPolynomial.X i) hinj (MvPolynomial.X_ne_zero i)
    (chartRatio i) MvPolynomial.X (ratio_generate i) (ratio_relation i)

lemma blowdown_restrict_isIso (i : Fin 3) :
    IsIso (blowdown ∣_ PrimeSpectrum.basicOpen (MvPolynomial.X i)) := by
  have : IsIso ((blowupIota i ≫ blowdown) ∣_ PrimeSpectrum.basicOpen (MvPolynomial.X i)) := by
    rw [blowupIota_blowdown]
    exact baseMap_restrict_isIso i
  exact SchemeRestrictionImage.isIso_of_chart (blowupIota i) blowdown _
    (blowdown_preimage_le_chart i)
end SourcePullbackChart
namespace KummerSourceModel
abbrev polynomialPuncture : (Spec (.of S)).Opens :=
  ⨆ i : Fin 3, PrimeSpectrum.basicOpen (MvPolynomial.X i)
abbrev seriesPuncture : (Spec (.of A)).Opens :=
  ⨆ i : Fin 3, PrimeSpectrum.basicOpen (MvPowerSeries.X i)

instance blowdown_puncture_isIso : IsIso (blowdown ∣_ polynomialPuncture) := by
  exact SchemeRestrictionImage.isIso_restrict_iSup blowdown _
    SourcePullbackChart.blowdown_restrict_isIso

lemma completion_preimage_puncture :
    completionToPolynomial ⁻¹ᵁ polynomialPuncture = seriesPuncture := by
  rw [polynomialPuncture]
  erw [Scheme.Hom.preimage_iSup]
  congr 1
  funext i
  change PrimeSpectrum.basicOpen (MvPolynomial.toMvPowerSeries (MvPolynomial.X i)) = _
  simp

instance completedBlowdown_puncture_isIso : IsIso (completedBlowdown ∣_ seriesPuncture) := by
  rw [← completion_preimage_puncture]
  exact Scheme.Hom.isIso_restrict_of_isPullback
    (IsPullback.of_hasPullback blowdown completionToPolynomial).flip polynomialPuncture
end KummerSourceModel

end

/-! Local equations of the plane zero section after power-series base change. The base chart is
literally B_i tensor_S A. -/
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
open KummerSourceModel
attribute [local instance] originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra
local instance planeOriginAlgebra (i : Fin 3) : Algebra S (planeChart i) :=
  ((algebraMap ℂ (planeChart i)).comp MvPolynomial.constantCoeff).toAlgebra
local instance baseChartModule (i : Fin 3) : Module S (chart i) := (chartBaseAlgebra i).toModule
local instance baseChartAction (i : Fin 3) : MulAction S (chart i) := (baseChartModule i).toMulAction
local instance baseChartSMul (i : Fin 3) : SMul S (chart i) := (baseChartModule i).toSMul
local instance baseChartTower (i : Fin 3) : IsScalarTower S S (chart i) := inferInstance
local instance planeOriginModule (i : Fin 3) : Module S (planeChart i) := (planeOriginAlgebra i).toModule

lemma zeroEvaluation_kernel (i : Fin 3) :
    RingHom.ker (zeroEvaluation i) = Ideal.span {baseMap i (MvPolynomial.X i)} := by
  ext q
  change zeroEvaluation i q = 0 ↔ q ∈ Ideal.span {baseMap i (MvPolynomial.X i)}
  rw [Ideal.mem_span_singleton]
  change Polynomial.eval 0 ((planePolynomialEquiv i).symm q) = 0 ↔ _
  rw [← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.X_dvd_iff]
  rw [← (planePolynomialEquiv i).symm_apply_apply Polynomial.X, planePolynomialEquiv_X]
  exact map_dvd_iff (planePolynomialEquiv i).symm

lemma baseFiber_regular (i : Fin 3) : IsSMulRegular (chart i) (baseMap i (MvPolynomial.X i)) := by
  apply IsSMulRegular.of_ne_zero
  rw [← planePolynomialEquiv_X]
  intro h
  exact Polynomial.X_ne_zero ((planePolynomialEquiv i).injective (h.trans (map_zero _).symm))

def zeroAlg (i : Fin 3) : chart i →ₐ[S] planeChart i :=
  { zeroEvaluation i with commutes' := fun a => RingHom.congr_fun (zeroEvaluation_base i) a }

abbrev completedBlowupChart (i : Fin 3) := chart i ⊗[S] A
local instance completedBlowupCommRing (i : Fin 3) : CommRing (completedBlowupChart i) := inferInstance
local instance completedBlowupSemiring (i : Fin 3) : Semiring (completedBlowupChart i) :=
  (completedBlowupCommRing i).toSemiring
local instance completedBlowupAlgebra (i : Fin 3) : Algebra S (completedBlowupChart i) :=
  Algebra.TensorProduct.instAlgebra

def completedBlowupFiber (i : Fin 3) : completedBlowupChart i := baseMap i (MvPolynomial.X i) ⊗ₜ[S] 1
abbrev completedBlowupZeroIdeal (i : Fin 3) : Ideal (completedBlowupChart i) :=
  (RingHom.ker (zeroEvaluation i)).map (algebraMap (chart i) (completedBlowupChart i))
local instance completedBlowupQuotAlgebra (i : Fin 3) :
    Algebra S (completedBlowupChart i ⧸ completedBlowupZeroIdeal i) := Ideal.Quotient.algebra S

lemma completedBlowupZeroIdeal_eq (i : Fin 3) :
    completedBlowupZeroIdeal i = Ideal.span {completedBlowupFiber i} := by
  simp only [completedBlowupZeroIdeal, zeroEvaluation_kernel, Ideal.map_span, Set.image_singleton]
  rfl

def completedPlaneQuotient (i : Fin 3) :
    (completedBlowupChart i ⧸ completedBlowupZeroIdeal i) ≃+* planeChart i :=
  (ScalarQuotientBaseChange.equiv (A := A) (zeroAlg i) (zeroEvaluation_surjective i)).trans
    (OriginScalarBaseChange.equiv (Fin 3) ℂ (planeChart i) rfl)

def completedPlaneEvaluation (i : Fin 3) : completedBlowupChart i →+* planeChart i :=
  (completedPlaneQuotient i).toRingHom.comp (Ideal.Quotient.mk (completedBlowupZeroIdeal i))

lemma completedPlaneEvaluation_tmul (i : Fin 3) (q : chart i) (a : A) :
    completedPlaneEvaluation i (q ⊗ₜ[S] a) =
      zeroEvaluation i q * algebraMap ℂ (planeChart i) (MvPowerSeries.constantCoeff a) := by
  change OriginScalarBaseChange.equiv (Fin 3) ℂ (planeChart i) rfl
    (ScalarQuotientBaseChange.equiv (A := A) (zeroAlg i)
      (zeroEvaluation_surjective i) (Ideal.Quotient.mk _ (q ⊗ₜ[S] a))) = _
  erw [ScalarQuotientBaseChange.equiv_tmul, OriginScalarBaseChange.equiv_tmul]
  rfl

lemma completedPlaneEvaluation_surjective (i : Fin 3) : Function.Surjective (completedPlaneEvaluation i) :=
  (completedPlaneQuotient i).surjective.comp Ideal.Quotient.mk_surjective

lemma completedPlaneEvaluation_kernel (i : Fin 3) :
    RingHom.ker (completedPlaneEvaluation i) = Ideal.span {completedBlowupFiber i} := by
  rw [← completedBlowupZeroIdeal_eq]
  ext a
  change completedPlaneQuotient i (Ideal.Quotient.mk (completedBlowupZeroIdeal i) a) = 0 ↔
    a ∈ completedBlowupZeroIdeal i
  rw [RingEquiv.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

lemma completedBlowupFiber_regular (i : Fin 3) :
    IsSMulRegular (completedBlowupChart i) (completedBlowupFiber i) :=
  (baseFiber_regular i).of_flat
end SourcePullbackChart

end

/-! The completed base charts and the completed plane zero section. These squares identify the
kernel ideals, not just their supports. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
open KummerSourceModel SourceZeroSections
attribute [local instance] originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra

def baseChartFirst (i : Fin 3) : Spec (.of (completedBlowupChart i)) ⟶ Spec (.of (chart i)) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : chart i →+* completedBlowupChart i))
def baseChartSecond (i : Fin 3) : Spec (.of (completedBlowupChart i)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A →+* completedBlowupChart i))

lemma baseChartTensor_isPullback (i : Fin 3) :
    IsPullback (baseChartFirst i) (baseChartSecond i)
      (Spec.map (CommRingCat.ofHom (baseMap i))) completionToPolynomial := by
  apply (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (baseMap i)))
    completionToPolynomial).of_iso'
      (pullbackSpecIso S (chart i) A).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    exact pullbackSpecIso_inv_fst S (chart i) A
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    exact pullbackSpecIso_inv_snd S (chart i) A
  · simp
  · simp

def completedBlowupIota (i : Fin 3) : Spec (.of (completedBlowupChart i)) ⟶ V :=
  pullback.lift (baseChartFirst i ≫ blowupIota i) (baseChartSecond i)
    (by rw [Category.assoc, blowupIota_blowdown]; exact (baseChartTensor_isPullback i).w)

@[reassoc] lemma completedBlowupIota_first (i : Fin 3) :
    completedBlowupIota i ≫ pullback.fst blowdown completionToPolynomial = baseChartFirst i ≫ blowupIota i :=
  pullback.lift_fst _ _ _
@[reassoc] lemma completedBlowupIota_second (i : Fin 3) :
    completedBlowupIota i ≫ completedBlowdown = baseChartSecond i :=
  pullback.lift_snd _ _ _

lemma completedBlowupIota_isPullback (i : Fin 3) :
    IsPullback (completedBlowupIota i) (baseChartFirst i)
      (pullback.fst blowdown completionToPolynomial) (blowupIota i) := by
  have hh : IsPullback (completedBlowupIota i ≫ completedBlowdown) (baseChartFirst i)
      completionToPolynomial (blowupIota i ≫ blowdown) := by
    rw [completedBlowupIota_second, blowupIota_blowdown]
    exact (baseChartTensor_isPullback i).flip
  exact hh.of_right (completedBlowupIota_first i)
    (IsPullback.of_hasPullback blowdown completionToPolynomial).flip

instance (i : Fin 3) : IsOpenImmersion (completedBlowupIota i) := by
  rw [← (completedBlowupIota_isPullback i).isoPullback_hom_fst]
  infer_instance

lemma completedBlowupIota_opensRange (i : Fin 3) : (completedBlowupIota i).opensRange =
    (pullback.fst blowdown completionToPolynomial) ⁻¹ᵁ (blowupIota i).opensRange := by
  have hh := (Scheme.Hom.opensRange_comp_of_isIso
    (completedBlowupIota_isPullback i).isoPullback.hom
    (pullback.fst (pullback.fst blowdown completionToPolynomial) (blowupIota i))).trans
      (Scheme.Hom.opensRange_pullbackFst (blowupIota i) (pullback.fst blowdown completionToPolynomial))
  simpa only [(completedBlowupIota_isPullback i).isoPullback_hom_fst] using hh

lemma completedBlowupCover : (⨆ i, (completedBlowupIota i).opensRange) = ⊤ := by
  simp_rw [completedBlowupIota_opensRange]
  rw [← Scheme.Hom.preimage_iSup]
  have hh := blowupCover.iSup_opensRange
  change (⨆ i, (blowupIota i).opensRange) = ⊤ at hh
  rw [hh, Scheme.Hom.preimage_top]

lemma completedPlaneEvaluation_left (i : Fin 3) :
    (completedPlaneEvaluation i).comp
      (Algebra.TensorProduct.includeLeftRingHom : chart i →+* completedBlowupChart i) = zeroEvaluation i := by
  apply RingHom.ext
  intro q
  change completedPlaneEvaluation i (q ⊗ₜ[S] (1 : A)) = _
  rw [completedPlaneEvaluation_tmul, map_one, map_one, mul_one]

lemma completedPlaneEvaluation_right (i : Fin 3) :
    (completedPlaneEvaluation i).comp
      (Algebra.TensorProduct.includeRight.toRingHom : A →+* completedBlowupChart i) =
    (algebraMap ℂ (planeChart i)).comp MvPowerSeries.constantCoeff := by
  apply RingHom.ext
  intro a
  change completedPlaneEvaluation i ((1 : chart i) ⊗ₜ[S] a) = _
  rw [completedPlaneEvaluation_tmul, map_one, one_mul]
  rfl

abbrev completedPlaneZeroChart (i : Fin 3) : Spec (.of (planeChart i)) ⟶ Spec (.of (completedBlowupChart i)) :=
  Spec.map (CommRingCat.ofHom (completedPlaneEvaluation i))

@[reassoc] lemma completedPlaneZeroChart_first (i : Fin 3) :
    completedPlaneZeroChart i ≫ baseChartFirst i = Spec.map (CommRingCat.ofHom (zeroEvaluation i)) := by
  rw [baseChartFirst, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (completedPlaneEvaluation_left i)

@[reassoc] lemma completedPlaneZeroChart_second (i : Fin 3) :
    completedPlaneZeroChart i ≫ baseChartSecond i =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (planeChart i))) ≫ seriesOrigin := by
  rw [baseChartSecond, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (completedPlaneEvaluation_right i)

@[reassoc] lemma planeIota_completedPlaneZero (i : Fin 3) :
    planeIota i ≫ completedPlaneZero = completedPlaneZeroChart i ≫ completedBlowupIota i := by
  apply pullback.hom_ext
  · rw [Category.assoc, completedPlaneZero_fst, Category.assoc, completedBlowupIota_first,
      completedPlaneZeroChart_first_assoc, planeIota_zero]
  · change (planeIota i ≫ completedPlaneZero) ≫ completedBlowdown = _ ≫ completedBlowdown
    simp only [Category.assoc, completedPlaneZero_blowdown,
      completedBlowupIota_second, completedPlaneZeroChart_second]
    rw [← Category.assoc, planeIota_scalar]

lemma planeZero_chart_preimage (i : Fin 3) :
    completedPlaneZero ⁻¹ᵁ (completedBlowupIota i).opensRange = (planeIota i).opensRange := by
  rw [completedBlowupIota_opensRange, ← Scheme.Hom.comp_preimage, completedPlaneZero_fst]
  have hb : (blowupIota i).opensRange = direction ⁻¹ᵁ (planeIota i).opensRange := by
    dsimp only [blowupIota, planeIota]
    erw [Proj.opensRange_awayι, Proj.opensRange_awayι]
    rfl
  rw [hb, ← Scheme.Hom.comp_preimage, planeZero_direction, Scheme.Hom.id_preimage]

lemma completedPlaneZeroChart_isPullback (i : Fin 3) :
    IsPullback (planeIota i) (completedPlaneZeroChart i) completedPlaneZero (completedBlowupIota i) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact planeIota_completedPlaneZero i
  · exact planeZero_chart_preimage i

instance completedBlowupChart_noetherian (i : Fin 3) : IsNoetherianRing (completedBlowupChart i) := by
  have : IsLocallyNoetherian (Spec (.of (completedBlowupChart i))) :=
    LocallyOfFiniteType.isLocallyNoetherian (completedBlowupIota i)
  exact isLocallyNoetherian_Spec.mp this
end SourcePullbackChart

end

/-! The finite projection on the completed affine charts. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
namespace SourcePullbackChart
open KummerSourceModel SourceConeMorphism SourceZeroSections
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra
  originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra

def blowupInAlg (i : Fin 3) : chart i →ₐ[S] pullbackChart i :=
  { blowupIn i with commutes' := fun _ => rfl }

def completedProjectionMap (i : Fin 3) : completedBlowupChart i →+* completedSourceChart i :=
  (Algebra.TensorProduct.map (blowupInAlg i) (AlgHom.id S A)).toRingHom

@[simp] lemma completedProjectionMap_tmul (i : Fin 3) (b : chart i) (a : A) :
    completedProjectionMap i (b ⊗ₜ[S] a) = blowupIn i b ⊗ₜ[S] a := rfl

@[simp] lemma completedProjectionMap_fiber (i : Fin 3) :
    completedProjectionMap i (completedBlowupFiber i) = completedFiberParameter i := rfl

abbrev completedProjection (i : Fin 3) :
    Spec (.of (completedSourceChart i)) ⟶ Spec (.of (completedBlowupChart i)) :=
  Spec.map (CommRingCat.ofHom (completedProjectionMap i))

@[reassoc] lemma completedProjection_first (i : Fin 3) :
    completedProjection i ≫ baseChartFirst i =
      completedChartFirst i ≫ Spec.map (CommRingCat.ofHom (blowupIn i)) := by
  rw [baseChartFirst, completedChartFirst, ← Spec.map_comp, ← Spec.map_comp]
  rfl

@[reassoc] lemma completedProjection_second (i : Fin 3) :
    completedProjection i ≫ baseChartSecond i = completedChartSecond i := by
  rw [baseChartSecond, completedChartSecond, ← Spec.map_comp]
  congr 1

@[reassoc] lemma completedIota_projection (i : Fin 3) :
    completedIota i ≫ g = completedProjection i ≫ completedBlowupIota i := by
  apply pullback.hom_ext
  · rw [Category.assoc, ← forgetCompletion_blowup, ← Category.assoc,
      completedIota_forget, Category.assoc, pullbackIota_blowup,
      Category.assoc, completedBlowupIota_first, completedProjection_first_assoc]
  · change (completedIota i ≫ g) ≫ completedBlowdown = _ ≫ completedBlowdown
    rw [Category.assoc, completedIota_base, Category.assoc,
      completedBlowupIota_second, completedProjection_second]

lemma completedProjection_chart_preimage (i : Fin 3) :
    g ⁻¹ᵁ (completedBlowupIota i).opensRange = (completedIota i).opensRange := by
  rw [completedBlowupIota_opensRange, ← Scheme.Hom.comp_preimage,
    ← forgetCompletion_blowup, Scheme.Hom.comp_preimage, completedIota_opensRange,
    pullbackIota_opensRange]

lemma completedProjection_isPullback (i : Fin 3) :
    IsPullback (completedIota i) (completedProjection i) g (completedBlowupIota i) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact completedIota_projection i
  · exact completedProjection_chart_preimage i

lemma completedProjection_zero (i : Fin 3) :
    (completedZeroEvaluation i).comp (completedProjectionMap i) =
      (surfaceDirectionMap i).comp (completedPlaneEvaluation i) := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul b a =>
    change completedZeroEvaluation i (blowupIn i b ⊗ₜ[S] a) =
      surfaceDirectionMap i (completedPlaneEvaluation i (b ⊗ₜ[S] a))
    rw [completedZeroEvaluation_tmul, completedPlaneEvaluation_tmul, map_mul]
    have hb := RingHom.congr_fun (zeroEvaluation_blowup i) b
    simp only [RingHom.comp_apply] at hb
    rw [hb]
    congr 1
    exact (SectionCompletion.linearChartMap_scalar ExplicitCone.pieces
      ExplicitCone.projectiveParameter ExplicitCone.projectiveParameter_mem i _).symm
end SourcePullbackChart

end

/-! The closed base-change square induces a tensor-product square of coordinate rings. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace SourcePullbackChart
open KummerSourceModel SourceConeMorphism SourceZeroSections
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra
  originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra

@[reassoc] lemma completedClosedChart_commute (i : Fin 3) :
    completedZeroChart i ≫ completedProjection i =
      Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)) ≫ completedPlaneZeroChart i := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (completedProjection_zero i)

lemma completedClosedChart_isPullback (i : Fin 3) :
    IsPullback (completedZeroChart i) (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)))
      (completedProjection i) (completedPlaneZeroChart i) := by
  have h := (surface_isPullback i).paste_horiz completedSourceZero_isPullback
  rw [surfaceIota_completedSourceZero, planeIota_completedPlaneZero] at h
  exact h.of_right (completedClosedChart_commute i) (completedProjection_isPullback i)

lemma completedClosedChart_isPushout (i : Fin 3) :
    IsPushout (CommRingCat.ofHom (completedProjectionMap i))
      (CommRingCat.ofHom (completedPlaneEvaluation i))
      (CommRingCat.ofHom (completedZeroEvaluation i))
      (CommRingCat.ofHom (surfaceDirectionMap i)) := by
  exact (IsPullback.of_map_of_faithful Scheme.Spec
    (completedClosedChart_isPullback i)).unop.flip
end SourcePullbackChart

end

/-! Affine base change for modules and quasicoherent sheaves, needed for the closed X/D square.
Invertibility is proved from the pushout. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry TensorProduct
namespace AffineClosedBaseChange
variable {B C D E : CommRingCat.{0}}
  (f : B ⟶ C) (z : B ⟶ D) (w : C ⟶ E) (q : D ⟶ E)
  (h : IsPushout f z w q)

/-- The coordinate-ring base-change isomorphism, with the restriction and extension of scalars in
both corners. -/
def moduleIso (M : ModuleCat C) :
    (ModuleCat.extendScalars z.hom).obj ((ModuleCat.restrictScalars f.hom).obj M) ≅
      (ModuleCat.restrictScalars q.hom).obj ((ModuleCat.extendScalars w.hom).obj M) := by
  letI : Algebra B C := f.hom.toAlgebra
  letI : Algebra B D := z.hom.toAlgebra
  letI : Algebra C E := w.hom.toAlgebra
  letI : Algebra D E := q.hom.toAlgebra
  letI : Algebra B E := (w.hom.comp f.hom).toAlgebra
  letI : IsScalarTower B C E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower B D E :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  letI : Algebra.IsPushout B D C E :=
    CommRingCat.isPushout_iff_isPushout.mp h.flip
  letI : Module B M := Module.compHom M f.hom
  letI : IsScalarTower B C M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact (Algebra.IsPushout.cancelBaseChange B D C E M).symm.toModuleIso

/-- The base-change isomorphism for quasicoherent sheaves on spectra. -/
def tildeIso (M : ModuleCat C) :
    (Scheme.Modules.pullback (Spec.map z)).obj
      ((Scheme.Modules.pushforward (Spec.map f)).obj (tilde M)) ≅
    (Scheme.Modules.pushforward (Spec.map q)).obj
      ((Scheme.Modules.pullback (Spec.map w)).obj (tilde M)) :=
  (Scheme.Modules.pullback (Spec.map z)).mapIso (AffinePullback.pushforwardTildeIso f M) ≪≫
    (AffinePullback.pullbackTildeIso z).app _ ≪≫
    (tilde.functor D).mapIso (moduleIso f z w q h M) ≪≫
    (AffinePullback.pushforwardTildeIso q _).symm ≪≫
    (Scheme.Modules.pushforward (Spec.map q)).mapIso ((AffinePullback.pullbackTildeIso w).app M).symm

def sheafIso (M : (Spec C).Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pullback (Spec.map z)).obj
      ((Scheme.Modules.pushforward (Spec.map f)).obj M) ≅
    (Scheme.Modules.pushforward (Spec.map q)).obj
      ((Scheme.Modules.pullback (Spec.map w)).obj M) := by
  have : IsIso (Scheme.Modules.fromTildeΓ M) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact (Scheme.Modules.pullback (Spec.map z)).mapIso
        ((Scheme.Modules.pushforward (Spec.map f)).mapIso
          (@asIso _ _ _ _ (Scheme.Modules.fromTildeΓ M) this).symm) ≪≫
      tildeIso f z w q h (moduleSpecΓFunctor.obj M) ≪≫
      (Scheme.Modules.pushforward (Spec.map q)).mapIso
        ((Scheme.Modules.pullback (Spec.map w)).mapIso (@asIso _ _ _ _ (Scheme.Modules.fromTildeΓ M) this))
end AffineClosedBaseChange

end

end OAI
