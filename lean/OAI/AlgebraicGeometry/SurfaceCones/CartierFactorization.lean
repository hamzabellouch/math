import OAI.AlgebraicGeometry.SurfaceCones.CartierGluing

namespace OAI

private local instance factorizationSectionModule {Z : AlgebraicGeometry.Scheme.{0}}
    (M : Z.Modules) (U : Z.Opensᵒᵖ) : Module (Z.sheaf.obj.obj U) (M.val.obj U) :=
  (M.val.obj U).isModule

private local instance factorizationCoherentSectionModule {Z : AlgebraicGeometry.Scheme.{0}}
    (M : CoherentGlobal.Coh Z) (U : Z.Opensᵒᵖ) : Module (Z.sheaf.obj.obj U) (M.obj.val.obj U) :=
  (M.obj.val.obj U).isModule

private noncomputable local instance factorizationFreeSectionModule (Z : AlgebraicGeometry.Scheme.{0})
    (I : Type) (U : Z.Opensᵒᵖ) :
    Module (Z.sheaf.obj.obj U) ((SheafOfModules.free (R := Z.ringCatSheaf) I).val.obj U) :=
  ((SheafOfModules.free (R := Z.ringCatSheaf) I).val.obj U).isModule

/-!
# Cartier lattices on completed surface cones

This development accompanies *A Complete Local Domain without a Small
Cohen–Macaulay Module* (OpenAI, 2026).
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
open ActualSheafTensor CartierImageFiltration CoherentGlobal Scheme.Modules
variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
  (g : X ⟶ Y) [IsClosedImmersion g] [CompactSpace Y]
  (d : LineTrivialization Y.sheaf (idealSheaf g))
include d

/-- The two cleared maps are inverse up to the indicated ideal power.
Torsion freeness extends the equality from the puncture to the whole scheme. -/
lemma global_power_sandwich_factorization
    (n : ℕ) {M N : Y.Modules} [N.IsFinitePresentation]
    (hN : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (N.val.obj U))
    (e : M.over (ActualOpenSupport.complement g) ≅
      N.over (ActualOpenSupport.complement g))
    (f : (power (tensorLeft Y.sheaf (idealSheaf g)) n).obj M ⟶ N)
    (a : (power (tensorLeft Y.sheaf (idealSheaf g)) n).obj N ⟶ M)
    (hf : f.over (ActualOpenSupport.complement g) =
      ((powerAction (tensorLeft Y.sheaf (idealSheaf g))
        (idealAction Y.sheaf (idealι g)) n).app M).over
          (ActualOpenSupport.complement g) ≫ e.hom)
    (ha : a.over (ActualOpenSupport.complement g) =
      ((powerAction (tensorLeft Y.sheaf (idealSheaf g))
        (idealAction Y.sheaf (idealι g)) n).app N).over
          (ActualOpenSupport.complement g) ≫ e.inv) :
    (powerAddIso (tensorLeft Y.sheaf (idealSheaf g)) n n N).hom ≫
        (power (tensorLeft Y.sheaf (idealSheaf g)) n).map a ≫ f =
      (powerAction (tensorLeft Y.sheaf (idealSheaf g))
        (idealAction Y.sheaf (idealι g)) (n + n)).app N := by
  let T := tensorLeft Y.sheaf (idealSheaf g)
  let act := idealAction Y.sheaf (idealι g)
  let U := ActualOpenSupport.complement g
  let A : Coh Y := ⟨(power T (n + n)).obj N,
    coherent_power_tensor_line (idealSheaf g) d (n + n) N⟩
  let B : Coh Y := ⟨N, inferInstance⟩
  let p : A ⟶ B := ObjectProperty.homMk
    ((powerAddIso T n n N).hom ≫ (power T n).map a ≫ f)
  let q : A ⟶ B := ObjectProperty.homMk ((powerAction T act (n + n)).app N)
  have hpq : p = q := by
    apply hom_ext_of_puncture g d p q hN
    have hh : p.hom.over U = q.hom.over U :=
      power_sandwich_map T act (SheafOfModules.overFunctor Y.ringCatSheaf U)
        n e f a hf ha
    have : Epi ((overFunctorEquiv U).hom.app A.obj) :=
      @IsIso.epi_of_iso _ _ _ _ _ ((overFunctorEquiv U).app A.obj).isIso_hom
    apply (cancel_epi ((overFunctorEquiv U).hom.app A.obj)).mp
    calc
      _ = (overEquiv U).functor.map (p.hom.over U) ≫
          (overFunctorEquiv U).hom.app B.obj :=
        ((overFunctorEquiv U).hom.naturality p.hom).symm
      _ = (overEquiv U).functor.map (q.hom.over U) ≫
          (overFunctorEquiv U).hom.app B.obj := by rw [hh]
      _ = _ := (overFunctorEquiv U).hom.naturality q.hom
  exact congrArg (fun k : A ⟶ B => k.hom) hpq
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
open ActualSheafTensor CartierImageFiltration CoherentGlobal CoherentK0 Scheme.Modules
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (g : X ⟶ Y) [IsClosedImmersion g] [CompactSpace Y]
  (d : LineTrivialization Y.sheaf (idealSheaf g))

omit [IsLocallyNoetherian X] [IsClosedImmersion g] [CompactSpace Y] in
/-- An ideal-power factorization annihilates the coherent quotient by the same exponent. -/
lemma idealMultiple_isZero_of_raw_factorization
    {S : ShortComplex (Coh Y)} (hS : S.ShortExact) (n : ℕ)
    (a : (power (tensorLeft Y.sheaf (idealSheaf g)) n).obj S.X₂.obj ⟶ S.X₁.obj)
    (ha : a ≫ S.f.hom =
      (powerAction (tensorLeft Y.sheaf (idealSheaf g))
        (idealAction Y.sheaf (idealι g)) n).app S.X₂.obj) :
    IsZero (idealMultiple g d n S.X₃) := by
  let T := coherentTensorLine (idealSheaf g) d
  let V : Y.Modules ⥤ Y.Modules := tensorLeft Y.sheaf (idealSheaf g)
  have : PreservesColimits V := CoherentDual.tensorLeft_preservesColimits _ _
  have : V.PreservesEpimorphisms := preservesEpimorphisms_of_preservesColimitsOfShape V
  let F := cohInclusion Y
  let c : T ⋙ F ≅ F ⋙ V := Iso.refl _
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  apply iterated_isZero_of_powerAction_zero
  apply F.map_injective
  rw [Functor.map_zero]
  apply map_powerAction_zero_of_comparison T V F c (action g d)
    (idealAction Y.sheaf (idealι g)) (fun _ => Category.id_comp _) n S.X₃
  exact powerAction_quotient_zero V (idealAction Y.sheaf (idealι g))
    (hS.map F) n a ha

/-- The coherent lattice construction with the twice-clearing exponent,
conormal-layer epimorphisms and divisor Grothendieck identity. -/
lemma exists_cleared_lattice_twice_bound
    (M N : Y.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hM : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (M.val.obj U))
    (hN : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (N.val.obj U))
    (e : M.over (ActualOpenSupport.complement g) ≅
      N.over (ActualOpenSupport.complement g)) :
    let L : Coh Y := ⟨N, inferInstance⟩
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      ∃ a : clearedLattice g d n M ⟶ L,
        Mono a ∧
        ((cohInclusion Y).map a).over (ActualOpenSupport.complement g) =
          ((powerAction (tensorLeft Y.sheaf (idealSheaf g))
            (idealAction Y.sheaf (idealι g)) n).app M).over
              (ActualOpenSupport.complement g) ≫ e.hom ∧
        IsZero (idealMultiple g d (n + n) (cokernel a)) ∧
        cls ((restriction g d).obj (clearedLattice g d n M)) =
          cls ((restriction g d).obj L) +
            ((idealLayers g d (n + n) (cokernel a)).map fun Q =>
              cls (conormalTensor g d Q) - cls Q).sum ∧
        ∀ j : ℕ, Epi (twistedLayerQuotient g d (cokernel.π a) j) := by
  dsimp only
  let L : Coh Y := ⟨N, inferInstance⟩
  obtain ⟨k, hk⟩ := exists_global_power_sandwich g d M N hM hN e
  refine ⟨k, fun n hn => ?_⟩
  obtain ⟨a, b, ha, hb, hae, hbe, hai, hbi⟩ := hk n hn
  let := ha
  let a' : clearedLattice g d n M ⟶ L := ObjectProperty.homMk a
  have ha' : Mono a' := (cohInclusion Y).mono_of_mono_map (f := a') (by
    change Mono a
    infer_instance)
  let S : ShortComplex (Coh Y) :=
    ShortComplex.mk a' (cokernel.π a') (cokernel.condition a')
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel a' }
  have hnil : IsZero (idealMultiple g d (n + n) (cokernel a')) := by
    apply idealMultiple_isZero_of_raw_factorization g d hS (n + n)
      ((powerAddIso (tensorLeft Y.sheaf (idealSheaf g)) n n N).hom ≫
        (power (tensorLeft Y.sheaf (idealSheaf g)) n).map b)
    exact (Category.assoc _ _ _).trans
      (global_power_sandwich_factorization g d n hN e a b hae hbe)
  refine ⟨a', ha', hae, hnil, ?_, fun _ => inferInstance⟩
  apply lattice_nilpotent_identity g d hS _ hN (n + n) hnil
  exact SheafTorsion.subobject ((cohInclusion Y).map a') hN
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
open ActualSheafTensor CartierImageFiltration CoherentGlobal CoherentK0 Scheme.Modules

/-- The finite free coherent module sheaf. -/
def coherentFree (Y : Scheme.{0}) (I : Type) [Finite I] : Coh Y :=
  ⟨SheafOfModules.free (R := Y.ringCatSheaf) I,
    CoherentLocality.finitePresentation_free Y.ringCatSheaf I⟩

/-- On an integral scheme, the finite free sheaf is sectionwise
torsion free, including empty opens. -/
lemma free_sections_torsionFree (Y : Scheme.{0}) [IsIntegral Y]
    (I : Type) [Finite I] (U : Y.Opensᵒᵖ) :
    Module.IsTorsionFree (Y.sheaf.obj.obj U)
      ((SheafOfModules.free (R := Y.ringCatSheaf) I).val.obj U) := by
  let e := CoherentDual.dualFiniteFreeIso Y.sheaf I
  have hm : Mono e.inv := @IsIso.mono_of_iso _ _ _ _ _ e.isIso_inv
  exact @SheafTorsion.subobject _ _ _ e.inv hm
    (fun V => CoherentDual.dual_sections_torsionFree _ V.unop) U

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (g : X ⟶ Y) [IsClosedImmersion g]
  (d : LineTrivialization Y.sheaf (idealSheaf g))

/-- The coherent restriction used by the Cartier resolution sends
the finite free sheaf to the same finite free sheaf on the divisor. -/
def restriction_freeIso (I : Type) [Finite I] :
    (restriction g d).obj (coherentFree Y I) ≅ coherentFree X I :=
  by
  let : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  let F := TopologicalSpace.Opens.map g.base
  let : F.Final := Functor.final_of_exists_of_isFiltered F
    (fun U => ⟨⊤, ⟨homOfLE (by change U ≤ ⊤; exact le_top)⟩⟩)
    (fun {U V} s t => ⟨V, 𝟙 _, Subsingleton.elim _ _⟩)
  exact ObjectProperty.isoMk _ ((restrictionPullbackIso g d (coherentFree Y I)).symm ≪≫
    SheafOfModules.pullbackObjFreeIso g.toRingCatSheafHom I)

/-- The quotient map from the jth conormal twist of O_D^N to the jth quotient layer. -/
def freeTwistedLayerQuotient {Q : Coh Y} {I : Type} [Finite I]
    (q : coherentFree Y I ⟶ Q) (j : ℕ) :
    (power (conormalFunctor g d) j).obj (coherentFree X I) ⟶ layer g d j Q :=
  (power (conormalFunctor g d) j).map (restriction_freeIso g d I).inv ≫
    twistedLayerQuotient g d q j

instance freeTwistedLayerQuotient_epi {Q : Coh Y} {I : Type} [Finite I]
    (q : coherentFree Y I ⟶ Q) [Epi q] (j : ℕ) :
    Epi (freeTwistedLayerQuotient g d q j) := by
  dsimp only [freeTwistedLayerQuotient]
  infer_instance

/-- The sheaf-theoretic content of the divisor lattice construction for the finite
free ambient lattice: a fixed puncture trivialization constructs the
embedding, the finite twice-bound filtration, the divisor K₀ identity,
and all the required quotients of conormal-twisted free sheaves. -/
lemma exists_free_cleared_lattice [CompactSpace Y] [IsIntegral Y]
    (M : Y.Modules) [M.IsFinitePresentation]
    (hM : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (M.val.obj U))
    (N : ℕ)
    (e : M.over (ActualOpenSupport.complement g) ≅
      (SheafOfModules.free (R := Y.ringCatSheaf) (Fin N)).over
        (ActualOpenSupport.complement g)) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      ∃ a : clearedLattice g d n M ⟶ coherentFree Y (Fin N),
        Mono a ∧
        ((cohInclusion Y).map a).over (ActualOpenSupport.complement g) =
          ((powerAction (tensorLeft Y.sheaf (idealSheaf g))
            (idealAction Y.sheaf (idealι g)) n).app M).over
              (ActualOpenSupport.complement g) ≫ e.hom ∧
        IsZero (idealMultiple g d (n + n) (cokernel a)) ∧
        cls ((restriction g d).obj (clearedLattice g d n M)) =
          cls (coherentFree X (Fin N)) +
            ((idealLayers g d (n + n) (cokernel a)).map fun Q =>
              cls (conormalTensor g d Q) - cls Q).sum ∧
        ∀ j : ℕ, Epi (freeTwistedLayerQuotient g d (cokernel.π a) j) := by
  let L := SheafOfModules.free (R := Y.ringCatSheaf) (Fin N)
  let : L.IsFinitePresentation :=
    CoherentLocality.finitePresentation_free Y.ringCatSheaf (Fin N)
  obtain ⟨k, hk⟩ := exists_cleared_lattice_twice_bound g d M L hM
    (free_sections_torsionFree Y (Fin N)) e
  refine ⟨k, fun n hn => ?_⟩
  obtain ⟨a, ha, hae, hnil, heq, hepi⟩ := hk n hn
  refine ⟨a, ha, hae, hnil, ?_, fun j => ?_⟩
  · exact heq.trans (congrArg (fun z => z + _)
      (cls_iso (restriction_freeIso g d (Fin N))))
  · have hπ : Epi (cokernel.π a) :=
      inferInstanceAs (Epi (cokernel.π (C := Coh Y) a))
    exact @freeTwistedLayerQuotient_epi X Y _ _ g _ d _ _ _ (cokernel.π a) hπ j
end ActualCartier

end

/-! The framed open is the complement of the completed exceptional plane. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Scheme.Modules
namespace SourceZeroSections
open KummerSourceModel SourceConeMorphism

lemma seriesOrigin_kernel : RingHom.ker (MvPowerSeries.constantCoeff : A →+* ℂ) =
    Ideal.span (Set.range (MvPowerSeries.X : Fin 3 → A)) := by
  apply le_antisymm
  · intro a ha
    exact mvPowerSeries_constantCoeff_zero_mem_vars a ha
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact MvPowerSeries.constantCoeff_X i

lemma seriesOrigin_range_compl : (Set.range seriesOrigin)ᶜ = (seriesPuncture : Set (Spec (.of A))) := by
  change (Set.range (PrimeSpectrum.comap (MvPowerSeries.constantCoeff : A →+* ℂ)))ᶜ = _
  rw [range_comap_of_surjective ℂ _
    (fun a => ⟨MvPowerSeries.C a, MvPowerSeries.constantCoeff_C a⟩), seriesOrigin_kernel,
    PrimeSpectrum.zeroLocus_span]
  ext q
  simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Set.range_subset_iff,
    SetLike.mem_coe, seriesPuncture]
  simp only [not_forall]
  erw [TopologicalSpace.Opens.mem_iSup]
  rfl

lemma completedPlaneZero_range : Set.range completedPlaneZero =
    completedBlowdown ⁻¹' Set.range seriesOrigin := by
  have he : Set.range completedPlaneZero =
      Set.range (pullback.fst completedBlowdown seriesOrigin) := by
    let e := completedPlaneZero_isPullback.isoPullback
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨e.hom y, ?_⟩
      change (e.hom ≫ pullback.fst completedBlowdown seriesOrigin) y = _
      rw [IsPullback.isoPullback_hom_fst]
    · rintro ⟨y, rfl⟩
      refine ⟨e.inv y, ?_⟩
      change (e.inv ≫ completedPlaneZero) y = _
      rw [IsPullback.isoPullback_inv_fst]
  rw [he, Scheme.Pullback.range_fst]

lemma planeComplement_eq : ActualOpenSupport.complement completedPlaneZero = baseModelPuncture := by
  apply TopologicalSpace.Opens.ext
  change (Set.range completedPlaneZero)ᶜ = completedBlowdown ⁻¹' (seriesPuncture : Set (Spec (.of A)))
  rw [completedPlaneZero_range, ← Set.preimage_compl, seriesOrigin_range_compl]
end SourceZeroSections
namespace SourceConeMorphism
open KummerSourceModel SourcePullbackChart SourceZeroSections
variable (M : ModuleCat.{0} ExplicitCone.completedRing)
  [Module.Finite ExplicitCone.completedRing M] [Nontrivial M]
  (hdepth : SmallCM.localDepth ExplicitCone.completedRing M = 3)

def modelPushforwardComplementFreeIso :
    (restrictFunctor (ActualOpenSupport.complement completedPlaneZero).ι).obj (modelPushforward M) ≅
      SheafOfModules.free (basisIndex M hdepth) := by
  rw [planeComplement_eq]
  exact modelPushforwardFreeIso M hdepth

/-- The slice-site framing for the generic lattice construction. -/
def modelPushforwardOverFreeIso :
    (modelPushforward M).over (ActualOpenSupport.complement completedPlaneZero) ≅
      (SheafOfModules.free (R := V.ringCatSheaf) (basisIndex M hdepth)).over
        (ActualOpenSupport.complement completedPlaneZero) := by
  let U := ActualOpenSupport.complement completedPlaneZero
  exact (overEquiv U).functor.preimageIso
    ((overFunctorEquiv U).app (modelPushforward M) ≪≫
      modelPushforwardComplementFreeIso M hdepth ≪≫
      (IsoPuncturePushforward.restrictFreeIso U.ι _).symm ≪≫
      ((overFunctorEquiv U).app (SheafOfModules.free (R := V.ringCatSheaf) (basisIndex M hdepth))).symm)
end SourceConeMorphism

end

/-! The kernel ideal of the completed plane zero section is invertible. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace SourceZeroSections
open KummerSourceModel SourcePullbackChart Scheme.Modules ActualCartier ActualSheafTensor
attribute [local instance] originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra

def planeIdealChartIso (i : Fin 3) :
    (restrictFunctor (completedBlowupIota i)).obj (idealSheaf completedPlaneZero) ≅
      SheafOfModules.unit (Spec (.of (completedBlowupChart i))).ringCatSheaf :=
  chartAffinePrincipalIdealUnitIso completedPlaneZero
    (CommRingCat.ofHom (completedPlaneEvaluation i)) (planeIota i) (completedBlowupIota i)
    (planeIota_completedPlaneZero i) (by
      simpa only [Scheme.Hom.image_top_eq_opensRange] using (planeZero_chart_preimage i).symm)
    (completedBlowupFiber i) (completedBlowupFiber_regular i)
    (completedPlaneEvaluation_kernel i)

def planeIdealLine : LineTrivialization V.sheaf (idealSheaf completedPlaneZero) :=
  lineTrivializationOfCharts _ (fun i => Spec (.of (completedBlowupChart i)))
    completedBlowupIota completedBlowupCover planeIdealChartIso

lemma planeIdeal_coherent : (idealSheaf completedPlaneZero).IsFinitePresentation :=
  idealSheaf_coherent _
end SourceZeroSections

end

/-! Coherent lattices for full-depth modules on the completed cone,
with their conormal layers and Cartier restriction identity. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Scheme.Modules
namespace SourceConeMorphism
open KummerSourceModel SourcePullbackChart SourceZeroSections
  ActualCartier ActualSheafTensor CartierImageFiltration CoherentK0 CoherentGlobal

attribute [local instance] originPlaneCommRing originPlaneSemiring

local instance planeChart_noetherian (i : Fin 3) : IsNoetherianRing (planeChart i) :=
  isNoetherianRing_of_surjective KummerSourceModel.S (planeChart i)
    (SectionCompletion.polynomialChartDehom i).toRingHom (polynomialChartDehom_surjective i)

instance sourcePlane_noetherian : IsLocallyNoetherian ExplicitCone.plane := by
  have (i : planeCover.I₀) : IsLocallyNoetherian (planeCover.X i) := by
    change Fin 3 at i
    change IsLocallyNoetherian (Spec (.of (planeChart i)))
    infer_instance
  exact (isLocallyNoetherian_iff_openCover planeCover).mpr (fun i => inferInstance)

instance sourceV_compact : CompactSpace V :=
  QuasiCompact.compactSpace_of_compactSpace completedBlowdown

variable (M : ModuleCat.{0} ExplicitCone.completedRing)
  [Module.Finite ExplicitCone.completedRing M] [Nontrivial M]
  (hdepth : SmallCM.localDepth ExplicitCone.completedRing M = 3)

local instance pushforward_coherent : (modelPushforward M).IsFinitePresentation :=
  modelPushforward_coherent M

noncomputable instance basisIndex_fintype : Fintype (basisIndex M hdepth) := Fintype.ofFinite _
abbrev sourceFreeRank : ℕ := Fintype.card (basisIndex M hdepth)

lemma sourceFreeRank_pos : 0 < sourceFreeRank M hdepth := by
  let := parameterModule_free M hdepth
  let : Nontrivial (parameterModule M) := show Nontrivial M from inferInstance
  have : Nonempty (basisIndex M hdepth) :=
    (Module.Free.chooseBasis A (parameterModule M)).index_nonempty
  exact Fintype.card_pos_iff.mpr this

def modelPushforwardOverFinIso :
    (modelPushforward M).over (ActualOpenSupport.complement completedPlaneZero) ≅
      (SheafOfModules.free (R := V.ringCatSheaf) (Fin (sourceFreeRank M hdepth))).over
        (ActualOpenSupport.complement completedPlaneZero) :=
  modelPushforwardOverFreeIso M hdepth ≪≫
    (SheafOfModules.overFunctor V.ringCatSheaf (ActualOpenSupport.complement completedPlaneZero)).mapIso
      (SheafOfModules.freeFunctor.mapIso (Fintype.equivFin (basisIndex M hdepth)).toIso)

/-- Coherent lattice, finite conormal layers, K₀ identity, and
quotients of conormal-twisted free sheaves for the finite pushforward.
Every premise of the reused lattice theorem is supplied by the source. -/
theorem exists_source_free_lattice :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      ∃ a : clearedLattice completedPlaneZero planeIdealLine n (modelPushforward M) ⟶
          coherentFree V (Fin (sourceFreeRank M hdepth)),
        Mono a ∧
        ((cohInclusion V).map a).over (ActualOpenSupport.complement completedPlaneZero) =
          ((powerAction (tensorLeft V.sheaf (idealSheaf completedPlaneZero))
            (idealAction V.sheaf (idealι completedPlaneZero)) n).app (modelPushforward M)).over
              (ActualOpenSupport.complement completedPlaneZero) ≫
                (modelPushforwardOverFinIso M hdepth).hom ∧
        IsZero (idealMultiple completedPlaneZero planeIdealLine (n + n) (cokernel a)) ∧
        cls ((restriction completedPlaneZero planeIdealLine).obj
          (clearedLattice completedPlaneZero planeIdealLine n (modelPushforward M))) =
          cls (coherentFree ExplicitCone.plane (Fin (sourceFreeRank M hdepth))) +
            ((idealLayers completedPlaneZero planeIdealLine (n + n) (cokernel a)).map fun Q =>
              cls (conormalTensor completedPlaneZero planeIdealLine Q) - cls Q).sum ∧
        ∀ j : ℕ, Epi (freeTwistedLayerQuotient completedPlaneZero planeIdealLine (cokernel.π a) j) := by
  let := modelPushforward_coherent M
  exact exists_free_cleared_lattice completedPlaneZero planeIdealLine (modelPushforward M)
    (modelPushforward_torsionFree M) (sourceFreeRank M hdepth) (modelPushforwardOverFinIso M hdepth)
end SourceConeMorphism

end

/-! Elementary transformations along the exceptional divisor of the completed model. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace SourceConeMorphism
open KummerSourceModel SourceZeroSections CoherentGlobal ActualCartier ActualSheafTensor
  Scheme.Modules
instance sourceSurface_noetherian : IsLocallyNoetherian ExplicitCone.projectiveSurface :=
  LocallyOfFiniteType.isLocallyNoetherian completedSourceZero

abbrev sourceRestriction := restriction completedSourceZero sourceIdealLine
abbrev coherentModel (M : ModuleCat ExplicitCone.completedRing)
    [Module.Finite ExplicitCone.completedRing M] : Coh W := ⟨E M, E_coherent M⟩

def sourceRestrictionIso (B : Coh W) :
    (Scheme.Modules.pullback completedSourceZero).obj B.obj ≅ (sourceRestriction.obj B).obj :=
  restrictionPullbackIso completedSourceZero sourceIdealLine B

lemma modelRestriction_torsionFree (M : ModuleCat ExplicitCone.completedRing)
    [Module.Finite ExplicitCone.completedRing M] (U : ExplicitCone.projectiveSurface.Opensᵒᵖ) :
    Module.IsTorsionFree (ExplicitCone.projectiveSurface.sheaf.obj.obj U)
      ((sourceRestriction.obj (coherentModel M)).obj.val.obj U) :=
  @SheafTorsion.subobject _ _ _ (sourceRestrictionIso (coherentModel M)).inv
    (@IsIso.mono_of_iso _ _ _ _ _ (sourceRestrictionIso (coherentModel M)).isIso_inv)
    (fun V => SourceExceptionalRestriction.P_torsionFree M V.unop) U

abbrev elementaryTransform {B : Coh W} {G : Coh ExplicitCone.projectiveSurface}
    (q : sourceRestriction.obj B ⟶ G) : Coh W :=
  kernel (modificationMap completedSourceZero sourceIdealLine q)

lemma elementaryTransform_torsionFree {B : Coh W} {G : Coh ExplicitCone.projectiveSurface}
    (q : sourceRestriction.obj B ⟶ G)
    (hB : ∀ U, Module.IsTorsionFree (W.sheaf.obj.obj U) (B.obj.val.obj U))
    (U : W.Opensᵒᵖ) : Module.IsTorsionFree (W.sheaf.obj.obj U)
      ((elementaryTransform q).obj.val.obj U) :=
  SheafTorsion.subobject ((cohInclusion W).map
    (kernel.ι (modificationMap completedSourceZero sourceIdealLine q))) hB U

/-- The divisor restriction of an elementary transform is torsion-free
when the chosen quotient is torsion-free. -/
lemma elementaryTransform_restriction_torsionFree
    {B : Coh W} {G : Coh ExplicitCone.projectiveSurface}
    (q : sourceRestriction.obj B ⟶ G) [Epi q]
    (hB : ∀ U, Module.IsTorsionFree (W.sheaf.obj.obj U) (B.obj.val.obj U))
    (hP : ∀ U, Module.IsTorsionFree (ExplicitCone.projectiveSurface.sheaf.obj.obj U)
      ((sourceRestriction.obj B).obj.val.obj U))
    (hG : ∀ U, Module.IsTorsionFree (ExplicitCone.projectiveSurface.sheaf.obj.obj U)
      (G.obj.val.obj U))
    (U : ExplicitCone.projectiveSurface.Opensᵒᵖ) :
    Module.IsTorsionFree (ExplicitCone.projectiveSurface.sheaf.obj.obj U)
      ((sourceRestriction.obj (elementaryTransform q)).obj.val.obj U) := by
  let S := transformSequence completedSourceZero sourceIdealLine q
  have hs := transformSequence_shortExact completedSourceZero sourceIdealLine q hB
  have : Mono S.f := hs.mono_f
  apply SheafTorsion.coherent_extension S hs.exact
  · intro V
    exact SheafTorsion.tensor_line _ _
      (sourceIdealLine.pullback completedSourceZero _) hG V
  · intro V
    exact SheafTorsion.subobject ((cohInclusion ExplicitCone.projectiveSurface).map
      (kernel.ι q)) hP V

lemma elementaryTransform_puncture {B : Coh W} {G : Coh ExplicitCone.projectiveSurface}
    (q : sourceRestriction.obj B ⟶ G) [Epi q] :
    IsIso ((restrictFunctor (ActualOpenSupport.complement completedSourceZero).ι).map
      ((cohInclusion W).map (kernel.ι
        (modificationMap completedSourceZero sourceIdealLine q)))) := by
  apply modification_puncture_isIso completedSourceZero sourceIdealLine q
  exact ActualCartier.preimage_complement _
end SourceConeMorphism

end

/-! Extensions obtained by successive elementary transformations in the balancing argument. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace SourceConeMorphism
open KummerSourceModel SourceZeroSections SourcePullbackChart CoherentGlobal ActualCartier
  ActualSheafTensor Scheme.Modules
abbrev sourceFramedOpen : W.Opens := g ⁻¹ᵁ ActualOpenSupport.complement completedPlaneZero
lemma sourceZero_preimage_framed : completedSourceZero ⁻¹ᵁ sourceFramedOpen = ⊥ := by
  change completedSourceZero ⁻¹ᵁ (g ⁻¹ᵁ ActualOpenSupport.complement completedPlaneZero) = ⊥
  rw [← Scheme.Hom.comp_preimage, completedSourceZero_isPullback.w, Scheme.Hom.comp_preimage,
    ActualCartier.preimage_complement, Scheme.Hom.preimage_bot]

structure ExtensionState (M : ModuleCat ExplicitCone.completedRing) where
  sheaf : Coh W
  ambient_tf : ∀ U, Module.IsTorsionFree (W.sheaf.obj.obj U) (sheaf.obj.val.obj U)
  divisor_tf : ∀ U, Module.IsTorsionFree (ExplicitCone.projectiveSurface.sheaf.obj.obj U)
    ((sourceRestriction.obj sheaf).obj.val.obj U)
  punctureIso : (restrictFunctor sourceFramedOpen.ι).obj sheaf.obj ≅
    (restrictFunctor sourceFramedOpen.ι).obj (E M)

namespace ExtensionState
variable {M : ModuleCat ExplicitCone.completedRing}

def initial [Module.Finite ExplicitCone.completedRing M] : ExtensionState M where
  sheaf := coherentModel M
  ambient_tf U := E_torsionFree M U.unop
  divisor_tf := modelRestriction_torsionFree M
  punctureIso := Iso.refl _

/-- The elementary transform constructs another admissible extension
and preserves its punctured framing. -/
def transform (B : ExtensionState M) {G : Coh ExplicitCone.projectiveSurface}
    (q : sourceRestriction.obj B.sheaf ⟶ G) [Epi q]
    (hG : ∀ U, Module.IsTorsionFree (ExplicitCone.projectiveSurface.sheaf.obj.obj U)
      (G.obj.val.obj U)) : ExtensionState M where
  sheaf := elementaryTransform q
  ambient_tf := elementaryTransform_torsionFree q B.ambient_tf
  divisor_tf := elementaryTransform_restriction_torsionFree q B.ambient_tf B.divisor_tf hG
  punctureIso := by
    have := modification_puncture_isIso completedSourceZero sourceIdealLine q
      sourceFramedOpen sourceZero_preimage_framed
    exact asIso ((restrictFunctor sourceFramedOpen.ι).map
      ((cohInclusion W).map (kernel.ι
        (modificationMap completedSourceZero sourceIdealLine q)))) ≪≫ B.punctureIso

def pushforward (B : ExtensionState M) : Coh V := (cohPushforward g).obj B.sheaf

lemma pushforward_torsionFree (B : ExtensionState M) (U : V.Opensᵒᵖ) :
    Module.IsTorsionFree (V.sheaf.obj.obj U) (B.pushforward.obj.val.obj U) :=
  SheafTorsion.pushforward g B.sheaf.obj B.ambient_tf U

variable [Module.Finite ExplicitCone.completedRing M] [Nontrivial M]
  (hdepth : SmallCM.localDepth ExplicitCone.completedRing M = 3)

def pushforwardFraming (B : ExtensionState M) :
    (restrictFunctor (ActualOpenSupport.complement completedPlaneZero).ι).obj B.pushforward.obj ≅
      SheafOfModules.free (basisIndex M hdepth) :=
  CoherentBaseChange.pushforwardRestrictIso g _ B.sheaf.obj ≪≫
    (Scheme.Modules.pushforward (g ∣_ ActualOpenSupport.complement completedPlaneZero)).mapIso
      B.punctureIso ≪≫
    (CoherentBaseChange.pushforwardRestrictIso g _ (E M)).symm ≪≫
    modelPushforwardComplementFreeIso M hdepth

def pushforwardOverFinIso (B : ExtensionState M) :
    B.pushforward.obj.over (ActualOpenSupport.complement completedPlaneZero) ≅
      (SheafOfModules.free (R := V.ringCatSheaf) (Fin (sourceFreeRank M hdepth))).over
        (ActualOpenSupport.complement completedPlaneZero) := by
  let U := ActualOpenSupport.complement completedPlaneZero
  exact (overEquiv U).functor.preimageIso
    ((overFunctorEquiv U).app B.pushforward.obj ≪≫
      B.pushforwardFraming hdepth ≪≫
      SheafOfModules.freeFunctor.mapIso (Fintype.equivFin (basisIndex M hdepth)).toIso ≪≫
      (IsoPuncturePushforward.restrictFreeIso U.ι _).symm ≪≫
      ((overFunctorEquiv U).app (SheafOfModules.free
        (R := V.ringCatSheaf) (Fin (sourceFreeRank M hdepth)))).symm)
end ExtensionState
end SourceConeMorphism

end

/-! Lattices associated to extensions obtained by elementary transformations. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Scheme.Modules
namespace SourceConeMorphism.ExtensionState
open KummerSourceModel SourceZeroSections ActualCartier ActualSheafTensor CoherentGlobal
  CartierImageFiltration CoherentK0
variable {M : ModuleCat.{0} ExplicitCone.completedRing}
  [Module.Finite ExplicitCone.completedRing M] [Nontrivial M]
  (hdepth : SmallCM.localDepth ExplicitCone.completedRing M = 3)

local instance (B : ExtensionState M) : B.pushforward.obj.IsFinitePresentation :=
  B.pushforward.property

/-- The exact coherent K₀ statement and conormal-twisted quotient
layers needed by the lattice inequality, for any constructed extension. -/
theorem exists_free_lattice (B : ExtensionState M) :
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      ∃ a : clearedLattice completedPlaneZero planeIdealLine n B.pushforward.obj ⟶
          coherentFree V (Fin (sourceFreeRank M hdepth)),
        Mono a ∧
        ((cohInclusion V).map a).over (ActualOpenSupport.complement completedPlaneZero) =
          ((powerAction (tensorLeft V.sheaf (idealSheaf completedPlaneZero))
            (idealAction V.sheaf (idealι completedPlaneZero)) n).app B.pushforward.obj).over
              (ActualOpenSupport.complement completedPlaneZero) ≫
                (B.pushforwardOverFinIso hdepth).hom ∧
        IsZero (idealMultiple completedPlaneZero planeIdealLine (n + n) (cokernel a)) ∧
        cls ((restriction completedPlaneZero planeIdealLine).obj
          (clearedLattice completedPlaneZero planeIdealLine n B.pushforward.obj)) =
          cls (coherentFree ExplicitCone.plane (Fin (sourceFreeRank M hdepth))) +
            ((idealLayers completedPlaneZero planeIdealLine (n + n) (cokernel a)).map fun Q =>
              cls (conormalTensor completedPlaneZero planeIdealLine Q) - cls Q).sum ∧
        ∀ j : ℕ, Epi (freeTwistedLayerQuotient completedPlaneZero planeIdealLine (cokernel.π a) j) := by
  exact exists_free_cleared_lattice completedPlaneZero planeIdealLine B.pushforward.obj
    B.pushforward_torsionFree (sourceFreeRank M hdepth) (B.pushforwardOverFinIso hdepth)
end SourceConeMorphism.ExtensionState

end

/-! Finite pushforward commutes with restriction for every admissible extension,
identifying the restricted lattice with the pushforward of the exceptional sheaf. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Scheme.Modules
namespace SourceConeMorphism.ExtensionState
open KummerSourceModel SourceZeroSections SourcePullbackChart CoherentGlobal ActualCartier
  CoherentK0
attribute [local instance] ExplicitCone.projectiveNormalization_finite
variable {M : ModuleCat ExplicitCone.completedRing} (B : ExtensionState M)

def restrictionPushforwardIso :
    (restriction completedPlaneZero planeIdealLine).obj B.pushforward ≅
      (cohPushforward ExplicitCone.projectiveNormalization).obj (sourceRestriction.obj B.sheaf) := by
  have := B.sheaf.property
  exact ObjectProperty.isoMk _
    ((restrictionPullbackIso completedPlaneZero planeIdealLine B.pushforward).symm ≪≫
      actualClosedBaseChangeIso B.sheaf.obj ≪≫
      (Scheme.Modules.pushforward ExplicitCone.projectiveNormalization).mapIso (sourceRestrictionIso B.sheaf))

lemma restrictionPushforward_class :
    cls ((restriction completedPlaneZero planeIdealLine).obj B.pushforward) =
      cls ((cohPushforward ExplicitCone.projectiveNormalization).obj (sourceRestriction.obj B.sheaf)) :=
  cls_iso (restrictionPushforwardIso B)
end SourceConeMorphism.ExtensionState

end

/-! Compatibility of canonical mates with object maps in a Cartier base-change square. -/
noncomputable section
open CategoryTheory
namespace ActualMateUnit
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {C₁ : Type u₁} {D₁ : Type u₂} {C₂ : Type u₃} {D₂ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} D₁] [Category.{v₃} C₂] [Category.{v₄} D₂]
  {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) {T : C₁ ⥤ C₂} {B : D₁ ⥤ D₂}
  (δ : R₁ ⋙ T ⟶ B ⋙ R₂)

lemma chosen_units {M : C₁} {N : C₂} {P : D₁} {Q : D₂}
    (a : N ⟶ T.obj M) (b : Q ⟶ B.obj P) (e₁ : L₁.obj M ⟶ P) (e₂ : L₂.obj N ⟶ Q)
    (h : a ≫ T.map (a₁.unit.app M ≫ R₁.map e₁) ≫ δ.app P =
      (a₂.unit.app N ≫ R₂.map e₂) ≫ R₂.map b) :
    L₂.map a ≫ (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ δ)).natTrans.app M) ≫
      B.map e₁ = e₂ ≫ b := by
  apply (a₂.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [a₂.unit_naturality_assoc a]
  rw [← reassoc_of% (unit_mateEquiv_symm a₁ a₂ (TwoSquare.mk _ _ _ _ δ) M)]
  change a ≫ T.map (a₁.unit.app M) ≫ δ.app (L₁.obj M) ≫ R₂.map (B.map e₁) = _
  erw [← δ.naturality e₁]
  simp only [Functor.comp_map]
  rw [← reassoc_of% (T.map_comp (a₁.unit.app M) (R₁.map e₁))]
  simpa only [Category.assoc] using h
lemma three_iso_chain {C : Type*} [Category C] {A B D E F G : C}
    (s : A ⟶ B) (t : B ⟶ D) (e : D ≅ E) (k : E ≅ F) (l : G ≅ F)
    (u : A ⟶ G) (x : A ⟶ E) (y : A ⟶ F)
    (hc : s ≫ t ≫ e.hom = x) (hk : x ≫ k.hom = y) (hl : u ≫ l.hom = y) :
    s ≫ t ≫ (e.hom ≫ k.hom ≫ l.inv) = u := by
  apply (cancel_mono l.hom).mp
  simp only [Category.assoc, l.inv_hom_id, Category.comp_id]
  rw [← Category.assoc t, ← Category.assoc s, hc, hk, hl]

end ActualMateUnit

end

/-! The base-change mate respects the structure-sheaf maps,
identifying the source Cartier ideal with the pullback of the base Cartier ideal. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace ActualCartier
open Scheme.Modules ActualSheafTensor ActualSheafBaseChange
variable {B C D E : Scheme.{0}}

lemma structure_comp (f : C ⟶ B) (w : E ⟶ C) :
    structureMap f ≫ (pushforward f).map (structureMap w) ≫
      (pushforwardComp w f).hom.app (SheafOfModules.unit _) = structureMap (w ≫ f) := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.ext
  intro r
  rfl

lemma structure_congr {f g : C ⟶ B} (h : f = g) :
    structureMap f ≫ (pushforwardCongr h).hom.app (SheafOfModules.unit _) =
      structureMap g := by
  subst g
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.ext
  intro r
  change C.presheaf.map (eqToHom (rfl : f ⁻¹ᵁ U = f ⁻¹ᵁ U)).op (f.app U r) = f.app U r
  simp

lemma structure_square (f : C ⟶ B) (z : D ⟶ B) (w : E ⟶ C) (q : E ⟶ D)
    (h : w ≫ f = q ≫ z) :
    structureMap f ≫ (pushforward f).map (structureMap w) ≫
      (rightIso f z w q h).hom.app (SheafOfModules.unit _) =
    structureMap z ≫ (pushforward z).map (structureMap q) := by
  exact ActualMateUnit.three_iso_chain (structureMap f)
    ((pushforward f).map (structureMap w)) ((pushforwardComp w f).app _)
    ((pushforwardCongr h).app _) ((pushforwardComp q z).app _)
    (structureMap z ≫ (pushforward z).map (structureMap q))
    (structureMap (w ≫ f)) (structureMap (q ≫ z))
    (structure_comp f w) (structure_congr h) (by
      change (structureMap z ≫ (pushforward z).map (structureMap q)) ≫
        (pushforwardComp q z).hom.app (SheafOfModules.unit _) = _
      exact (Category.assoc _ _ _).trans (structure_comp z q))

lemma pullbackUnit_adj (z : D ⟶ B) :
    (pullbackPushforwardAdjunction z).unit.app (SheafOfModules.unit _) ≫
      (pushforward z).map (sheafPullbackUnitIso z).hom = structureMap z := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.ext
  intro r
  exact sheafPullbackUnitIso_unit z U r

lemma baseChange_structure (f : C ⟶ B) (z : D ⟶ B) (w : E ⟶ C) (q : E ⟶ D)
    (h : w ≫ f = q ≫ z) :
    (Scheme.Modules.pullback z).map (structureMap f) ≫
      (mate f z w q h).app (SheafOfModules.unit _) ≫
        (pushforward q).map (sheafPullbackUnitIso w).hom =
      (sheafPullbackUnitIso z).hom ≫ structureMap q := by
  apply ActualMateUnit.chosen_units (pullbackPushforwardAdjunction w)
    (pullbackPushforwardAdjunction z) (rightIso f z w q h).hom
    (structureMap f) (structureMap q)
    (sheafPullbackUnitIso w).hom (sheafPullbackUnitIso z).hom
  rw [pullbackUnit_adj, pullbackUnit_adj]
  exact structure_square f z w q h

end ActualCartier

end

/-! The closed structure map is an epimorphism by the cokernel property of Cartier restriction. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace ActualCartier
open Scheme.Modules CoherentGlobal ActualSheafTensor
variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsClosedImmersion f]
  (d : LineTrivialization Y.sheaf (idealSheaf f))

lemma restrictionPullbackIso_unit (M : Coh Y) :
    (pullbackPushforwardAdjunction f).unit.app M.obj ≫
      (pushforward f).map (restrictionPullbackIso f d M).hom =
        ((restrictionUnit f d).app M).hom := by
  change (pullbackPushforwardAdjunction f).unit.app M.obj ≫
    (pushforward f).map
      (((pullbackPushforwardAdjunction f).homEquiv M.obj _).symm
        ((restrictionUnit f d).app M).hom) = _
  exact ((pullbackPushforwardAdjunction f).homEquiv M.obj _).apply_symm_apply _

include d in
lemma coherent_adjUnit_epi (M : Coh Y) :
    Epi ((pullbackPushforwardAdjunction f).unit.app M.obj) := by
  have : Epi ((cohInclusion Y).map ((restrictionUnit f d).app M)) := inferInstance
  have hE : Epi (((restrictionUnit f d).app M).hom) := this
  have he := restrictionPullbackIso_unit f d M
  have hI : IsIso ((pushforward f).map (restrictionPullbackIso f d M).hom) :=
    ((pushforward f).mapIso (restrictionPullbackIso f d M)).isIso_hom
  have hc : Epi ((pullbackPushforwardAdjunction f).unit.app M.obj ≫
      (pushforward f).map (restrictionPullbackIso f d M).hom) := he.symm ▸ hE
  exact (epi_comp_iff_of_isIso _
    ((pushforward f).map (restrictionPullbackIso f d M).hom)).mp hc

include d in
lemma structureMap_epi : Epi (structureMap f) := by
  let M : Coh Y := ⟨SheafOfModules.unit _, CoherentLocality.finitePresentation_unit _⟩
  have hE : Epi ((pullbackPushforwardAdjunction f).unit.app (SheafOfModules.unit _)) :=
    coherent_adjUnit_epi f d M
  have hI : IsIso ((pushforward f).map (sheafPullbackUnitIso f).hom) :=
    ((pushforward f).mapIso (sheafPullbackUnitIso f)).isIso_hom
  have hc := epi_comp' hE (@IsIso.epi_of_iso _ _ _ _ _ hI)
  erw [pullbackUnit_adj] at hc
  exact hc
end ActualCartier

end

/-! A right-exact pullback induces an epimorphism of kernel ideals
when the quotient square is identified. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ActualRightExactIdeal
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
  [PreservesFiniteColimits F]

lemma kernelComparison_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    Epi (kernelComparison f F) := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hc : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
    (ShortComplex.exact_kernel f).gIsCokernel
  have he : (S.map F).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.mapIsColimit _ hc F)
  exact ((S.map F).exact_iff_epi_kernel_lift).mp he

def comparison {X Y : C} (f : X ⟶ Y) {X' Y' : D} (g : X' ⟶ Y')
    (a : F.obj X ≅ X') (b : F.obj Y ≅ Y') (h : F.map f ≫ b.hom = a.hom ≫ g) :
    F.obj (kernel f) ⟶ kernel g :=
  kernelComparison f F ≫ (kernel.mapIso (F.map f) g a b h).hom

instance comparison_epi {X Y : C} (f : X ⟶ Y) [Epi f] {X' Y' : D} (g : X' ⟶ Y')
    (a : F.obj X ≅ X') (b : F.obj Y ≅ Y') (h : F.map f ≫ b.hom = a.hom ≫ g) :
    Epi (comparison F f g a b h) := by
  have := kernelComparison_epi F f
  dsimp only [comparison]
  infer_instance

omit [PreservesFiniteColimits F] in
lemma comparison_ι {X Y : C} (f : X ⟶ Y) {X' Y' : D} (g : X' ⟶ Y')
    (a : F.obj X ≅ X') (b : F.obj Y ≅ Y') (h : F.map f ≫ b.hom = a.hom ≫ g) :
    comparison F f g a b h ≫ kernel.ι g = F.map (kernel.ι f) ≫ a.hom := by
  simp [comparison]
end ActualRightExactIdeal

end

end OAI
