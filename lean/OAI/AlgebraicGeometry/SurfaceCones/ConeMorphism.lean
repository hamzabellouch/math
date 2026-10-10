import OAI.AlgebraicGeometry.SurfaceCones.OriginTensor

namespace OAI


/-! The manuscript's actual source evaluation p : W → Spec R, where W is
literally X ×[P²] (Bl₀(A³) ×[A³] Spec C[[x₀,x₁,x₂]]).
The construction uses the proved canonical scalar-completion comparison;
no identification with an ordinary Rees blowup of R is assumed. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourceConeMorphism
open KummerSourceModel
abbrev sectionRing := SourcePullbackChart.sectionRing
abbrev parameterMap := SourcePullbackChart.parameterMap
local instance sectionParameterAlgebra : Algebra S sectionRing := parameterMap.toRingHom.toAlgebra
local instance completedParameterAlgebra : Algebra A ExplicitCone.completedRing :=
  ExplicitCone.projectiveCompletedParameterHom.toRingHom.toAlgebra

/-- The literal source's forget-completion morphism. -/
def forgetCompletion : W ⟶ W₀ :=
  pullback.lift (pullback.fst _ _) (g ≫ pullback.fst _ _) (by
    change pullback.fst _ _ ≫ ExplicitCone.projectiveNormalization =
      pullback.snd _ _ ≫ pullback.fst _ _ ≫ direction
    exact pullback.condition)

@[reassoc] lemma forgetCompletion_surface :
    forgetCompletion ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc] lemma forgetCompletion_blowup :
    forgetCompletion ≫ g₀ = g ≫ pullback.fst _ _ := pullback.lift_snd _ _ _

@[reassoc] lemma forgetCompletion_base :
    forgetCompletion ≫ g₀ ≫ blowdown =
      (g ≫ completedBlowdown) ≫ completionToPolynomial := by
  rw [forgetCompletion_blowup_assoc]
  simp only [completedBlowdown, Category.assoc, pullback.condition]

/-- Evaluation into the exact scalar-extended affine cone. -/
def tensorEvaluation : W ⟶
    pullback completionToPolynomial (Spec.map (CommRingCat.ofHom parameterMap.toRingHom)) :=
  pullback.lift (g ≫ completedBlowdown)
    (forgetCompletion ≫ SourcePullbackChart.coneMorphism) (by
      simp only [Category.assoc, SourcePullbackChart.coneMorphism_parameters]
      exact forgetCompletion_base.symm)

/-- The source map in the obstruction proof, with its faithful completed
section-cone target. -/
def p : W ⟶ Spec (.of ExplicitCone.completedRing) :=
  tensorEvaluation ≫ (pullbackSpecIso S A sectionRing).hom ≫
    Spec.map (CommRingCat.ofHom ExplicitCone.projectiveTensorEquiv.symm.toRingHom)

lemma completion_parameter_identity :
    ExplicitCone.projectiveTensorEquiv.symm.toRingHom.comp
      ExplicitCone.projectiveCompletedParameterHom.toRingHom =
      (Algebra.TensorProduct.includeLeft : A →ₐ[A] A ⊗[S] sectionRing).toRingHom := by
  ext a
  exact ExplicitCone.projectiveTensorEquiv.symm.commutes a

@[reassoc] lemma p_parameters :
    p ≫ Spec.map (CommRingCat.ofHom ExplicitCone.projectiveCompletedParameterHom.toRingHom) =
      g ≫ completedBlowdown := by
  dsimp only [p]
  erw [Category.assoc, Category.assoc, ← Spec.map_comp]
  change tensorEvaluation ≫ (pullbackSpecIso S A sectionRing).hom ≫
    Spec.map (CommRingCat.ofHom (ExplicitCone.projectiveTensorEquiv.symm.toRingHom.comp
      ExplicitCone.projectiveCompletedParameterHom.toRingHom)) = _
  rw [completion_parameter_identity]
  change tensorEvaluation ≫ (pullbackSpecIso S A sectionRing).hom ≫
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = _
  exact (congrArg (fun f => tensorEvaluation ≫ f)
    (pullbackSpecIso_hom_fst S A sectionRing)).trans (pullback.lift_fst _ _ _)

/-- Properness of the actual source map, using the actual S-compatible
completion and the already proved properness over Spec A. -/
instance : IsProper p := by
  have : IsProper
      (p ≫ Spec.map (CommRingCat.ofHom ExplicitCone.projectiveCompletedParameterHom.toRingHom)) := by
    rw [p_parameters]
    exact W_proper
  exact IsProper.of_comp p
    (Spec.map (CommRingCat.ofHom ExplicitCone.projectiveCompletedParameterHom.toRingHom))

end SourceConeMorphism

end


/-! The newly constructed source map is the genuine base change of its
uncompleted counterpart, on the literal manuscript W and completed ring. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourceConeMorphism
open KummerSourceModel
attribute [local instance] sectionParameterAlgebra completedParameterAlgebra

lemma forgetCompletion_isPullback :
    IsPullback forgetCompletion g g₀ (pullback.fst blowdown completionToPolynomial) := by
  have hh : IsPullback (forgetCompletion ≫ pullback.fst _ _) g
      ExplicitCone.projectiveNormalization (pullback.fst blowdown completionToPolynomial ≫ direction) := by
    rw [forgetCompletion_surface]
    exact IsPullback.of_hasPullback ExplicitCone.projectiveNormalization completedDirection
  exact hh.of_right forgetCompletion_blowup
    (IsPullback.of_hasPullback ExplicitCone.projectiveNormalization direction)

lemma sourceCompletion_isPullback :
    IsPullback forgetCompletion (g ≫ completedBlowdown)
      (g₀ ≫ blowdown) completionToPolynomial :=
  forgetCompletion_isPullback.paste_vert (IsPullback.of_hasPullback blowdown completionToPolynomial)

/-- Exact affine-cone base-change comparison. -/
def completionSpecIso : Spec (.of ExplicitCone.completedRing) ≅
    pullback completionToPolynomial (Spec.map (CommRingCat.ofHom parameterMap.toRingHom)) :=
  Scheme.Spec.mapIso ExplicitCone.projectiveTensorEquiv.toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso S A sectionRing).symm

/-- The canonical map from the completed cone to the uncompleted cone. -/
def toUncompleted : Spec (.of ExplicitCone.completedRing) ⟶ Spec (.of sectionRing) :=
  completionSpecIso.hom ≫ pullback.snd _ _

def toPowerSeries : Spec (.of ExplicitCone.completedRing) ⟶ Spec (.of A) :=
  completionSpecIso.hom ≫ pullback.fst _ _

lemma tensor_right_identity :
    ExplicitCone.projectiveTensorEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : sectionRing →ₐ[S] A ⊗[S] sectionRing).toRingHom =
      (SectionCompletion.polynomialToSeries ExplicitCone.pieces).toRingHom := by
  apply RingHom.ext
  intro b
  change ExplicitCone.projectiveTensorEquiv (1 ⊗ₜ[S] b) = _
  have hh := ExplicitCone.projectiveTensorEquiv_tmul 1 b
  rw [map_one, one_mul] at hh
  exact hh

lemma toUncompleted_eq : toUncompleted =
    Spec.map (CommRingCat.ofHom (SectionCompletion.polynomialToSeries ExplicitCone.pieces).toRingHom) := by
  change Spec.map (CommRingCat.ofHom ExplicitCone.projectiveTensorEquiv.toRingHom) ≫
    (pullbackSpecIso S A sectionRing).inv ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S A)))
        (Spec.map (CommRingCat.ofHom (algebraMap S sectionRing))) = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) tensor_right_identity

lemma p_eq_comparison : p = tensorEvaluation ≫ completionSpecIso.inv := rfl

@[reassoc] lemma p_toUncompleted :
    p ≫ toUncompleted = forgetCompletion ≫ SourcePullbackChart.coneMorphism := by
  simp only [p_eq_comparison, toUncompleted, Category.assoc, Iso.inv_hom_id_assoc]
  exact pullback.lift_snd _ _ _

@[reassoc] lemma p_toPowerSeries : p ≫ toPowerSeries = g ≫ completedBlowdown := by
  simp only [p_eq_comparison, toPowerSeries, Category.assoc, Iso.inv_hom_id_assoc]
  exact pullback.lift_fst _ _ _

lemma coneCompletion_isPullback :
    IsPullback toPowerSeries toUncompleted completionToPolynomial
      (Spec.map (CommRingCat.ofHom parameterMap.toRingHom)) := by
  apply (IsPullback.of_hasPullback completionToPolynomial
    (Spec.map (CommRingCat.ofHom parameterMap.toRingHom))).of_iso'
    completionSpecIso (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]; rfl
  · simp only [Iso.refl_hom, Category.comp_id]; rfl
  · simp
  · simp

/-- The actual source completion square is cartesian, hence the punctured
isomorphism can be transferred without any assumptions about flatness. -/
lemma p_isPullback : IsPullback p forgetCompletion toUncompleted
    SourcePullbackChart.coneMorphism := by
  have hh : IsPullback (p ≫ toPowerSeries) forgetCompletion completionToPolynomial
      (SourcePullbackChart.coneMorphism ≫ Spec.map (CommRingCat.ofHom parameterMap.toRingHom)) := by
    rw [p_toPowerSeries, SourcePullbackChart.coneMorphism_parameters]
    exact sourceCompletion_isPullback.flip
  exact hh.of_right p_toUncompleted coneCompletion_isPullback

end SourceConeMorphism

end


/-! Actual zero sections in the manuscript's V₀,W₀,V,W.  These are closed
immersions from the actual plane/surface, proved cartesian over the origin;
no identification with an ordinary cone Rees blowup is used. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace SourceZeroSections
open KummerSourceModel SourcePullbackChart

def planeZero : ExplicitCone.plane ⟶ V₀ := originFiberIso.inv ≫ pullback.snd _ _
def planeScalar : ExplicitCone.plane ⟶ Spec (.of ℂ) := originFiberIso.inv ≫ pullback.fst _ _

@[reassoc] lemma planeZero_direction : planeZero ≫ direction = 𝟙 _ := by
  change originFiberIso.inv ≫ fiberDirection = _
  exact originFiberIso.inv_hom_id

@[reassoc] lemma planeZero_blowdown : planeZero ≫ blowdown = planeScalar ≫ originPoint := by
  simp only [planeZero, planeScalar, Category.assoc, pullback.condition]

lemma planeZero_isPullback : IsPullback planeScalar planeZero originPoint blowdown := by
  apply (IsPullback.of_hasPullback originPoint blowdown).of_iso'
    originFiberIso.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]; rfl
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]; rfl
  · simp
  · simp

instance originPoint_closed : IsClosedImmersion originPoint :=
  IsClosedImmersion.spec_of_surjective _ (fun a => ⟨MvPolynomial.C a,
    by simp⟩)

instance planeZero_closed : IsClosedImmersion planeZero := by
  rw [← planeZero_isPullback.isoPullback_hom_snd]
  infer_instance

def sourceZero : ExplicitCone.projectiveSurface ⟶ W₀ :=
  pullback.lift (𝟙 _) (ExplicitCone.projectiveNormalization ≫ planeZero) (by
    rw [Category.id_comp, Category.assoc, planeZero_direction, Category.comp_id])

@[reassoc] lemma sourceZero_fst : sourceZero ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
@[reassoc] lemma sourceZero_g₀ : sourceZero ≫ g₀ = ExplicitCone.projectiveNormalization ≫ planeZero :=
  pullback.lift_snd _ _ _

lemma sourceZero_isPullback : IsPullback sourceZero ExplicitCone.projectiveNormalization g₀ planeZero := by
  have h : IsPullback (sourceZero ≫ pullback.fst _ _) ExplicitCone.projectiveNormalization
      ExplicitCone.projectiveNormalization (planeZero ≫ direction) := by
    rw [sourceZero_fst, planeZero_direction]
    exact IsPullback.of_id_fst
  exact h.of_right sourceZero_g₀
    (IsPullback.of_hasPullback ExplicitCone.projectiveNormalization direction)

instance sourceZero_closed : IsClosedImmersion sourceZero := by
  rw [← sourceZero_isPullback.isoPullback_hom_fst]
  infer_instance

abbrev seriesOrigin : Spec (.of ℂ) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff : A →+* ℂ))

@[reassoc] lemma seriesOrigin_toPolynomial : seriesOrigin ≫ completionToPolynomial = originPoint := by
  rw [completionToPolynomial, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    rfl
  · intro i
    change MvPowerSeries.constantCoeff (MvPolynomial.toMvPowerSeries (MvPolynomial.X i)) =
      MvPolynomial.constantCoeff (MvPolynomial.X i)
    simp

instance seriesOrigin_closed : IsClosedImmersion seriesOrigin :=
  IsClosedImmersion.spec_of_surjective _ (fun a => ⟨MvPowerSeries.C a,
    MvPowerSeries.constantCoeff_C a⟩)

def completedPlaneZero : ExplicitCone.plane ⟶ V :=
  pullback.lift planeZero (planeScalar ≫ seriesOrigin) (by
    rw [Category.assoc, seriesOrigin_toPolynomial, planeZero_blowdown])

@[reassoc] lemma completedPlaneZero_fst : completedPlaneZero ≫ pullback.fst _ _ = planeZero :=
  pullback.lift_fst _ _ _
@[reassoc] lemma completedPlaneZero_blowdown : completedPlaneZero ≫ completedBlowdown =
    planeScalar ≫ seriesOrigin := pullback.lift_snd _ _ _
@[reassoc] lemma completedPlaneZero_direction : completedPlaneZero ≫ completedDirection = 𝟙 _ := by
  rw [completedDirection, completedPlaneZero_fst_assoc, planeZero_direction]

lemma completedPlaneZero_isPullback :
    IsPullback completedPlaneZero planeScalar completedBlowdown seriesOrigin := by
  have h : IsPullback (completedPlaneZero ≫ pullback.fst blowdown completionToPolynomial)
      planeScalar blowdown (seriesOrigin ≫ completionToPolynomial) := by
    rw [completedPlaneZero_fst, seriesOrigin_toPolynomial]
    exact planeZero_isPullback.flip
  exact h.of_right completedPlaneZero_blowdown
    (IsPullback.of_hasPullback blowdown completionToPolynomial)

instance completedPlaneZero_closed : IsClosedImmersion completedPlaneZero := by
  rw [← completedPlaneZero_isPullback.isoPullback_hom_fst]
  infer_instance

def completedSourceZero : ExplicitCone.projectiveSurface ⟶ W :=
  pullback.lift (𝟙 _) (ExplicitCone.projectiveNormalization ≫ completedPlaneZero) (by
    rw [Category.id_comp, Category.assoc, completedPlaneZero_direction, Category.comp_id])

@[reassoc] lemma completedSourceZero_fst : completedSourceZero ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _
@[reassoc] lemma completedSourceZero_g : completedSourceZero ≫ g =
    ExplicitCone.projectiveNormalization ≫ completedPlaneZero := pullback.lift_snd _ _ _

/-- The exact left-hand square in the manuscript, lines 275--277. -/
lemma completedSourceZero_isPullback :
    IsPullback completedSourceZero ExplicitCone.projectiveNormalization g completedPlaneZero := by
  have h : IsPullback (completedSourceZero ≫ pullback.fst _ _) ExplicitCone.projectiveNormalization
      ExplicitCone.projectiveNormalization (completedPlaneZero ≫ completedDirection) := by
    rw [completedSourceZero_fst, completedPlaneZero_direction]
    exact IsPullback.of_id_fst
  exact h.of_right completedSourceZero_g
    (IsPullback.of_hasPullback ExplicitCone.projectiveNormalization completedDirection)

instance completedSourceZero_closed : IsClosedImmersion completedSourceZero := by
  rw [← completedSourceZero_isPullback.isoPullback_hom_fst]
  infer_instance

/-- The entire actual closed fiber of W over A, with no extra components. -/
lemma completedSourceZero_origin_isPullback :
    IsPullback completedSourceZero (ExplicitCone.projectiveNormalization ≫ planeScalar)
      (g ≫ completedBlowdown) seriesOrigin :=
  completedSourceZero_isPullback.paste_vert completedPlaneZero_isPullback

end SourceZeroSections

end


noncomputable section
namespace ExplicitCone
lemma projectiveCompletedParameterHom_finite : projectiveCompletedParameterHom.Finite := by
  let : Algebra.FiniteType ℂ (SectionCompletion.polynomials pieces) :=
    GradedNormalization.polynomialPiece_finiteType polynomialAlgebra polynomialAlgebra_scale
  exact SectionCompletion.finite_linear_substitution pieces projectiveParameter
    projectiveParameter_mem zero_piece projectiveParameter_finite

lemma projectiveCompletedParameterHom_injective :
    Function.Injective projectiveCompletedParameterHom := by
  apply SectionGenerated.substHom_injective_linear
  have he : (SectionCompletion.polynomials pieces).val.comp
      (SectionCompletion.linearPolynomialMap pieces projectiveParameter projectiveParameter_mem) =
      MvPolynomial.aeval (fun i => Polynomial.monomial 1 (projectiveParameter i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [SectionCompletion.linearPolynomialMap]
  intro a b hab
  apply projectiveParameter_injective
  apply Subtype.ext
  change ((SectionCompletion.polynomials pieces).val.comp
    (SectionCompletion.linearPolynomialMap pieces projectiveParameter projectiveParameter_mem)) a =
    ((SectionCompletion.polynomials pieces).val.comp
    (SectionCompletion.linearPolynomialMap pieces projectiveParameter projectiveParameter_mem)) b
  simpa only [he] using hab

/-- The original polynomial cone and the actual projective-parameter
power-series map have a commuting square, not just abstract isomorphic bases. -/
lemma projectiveCompletedParameterHom_polynomial :
    (SectionCompletion.polynomialToSeries pieces).comp
      (SectionCompletion.linearPolynomialMap pieces projectiveParameter projectiveParameter_mem) =
      projectiveCompletedParameterHom.comp (MvPolynomial.aeval MvPowerSeries.X) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
  exact SectionCompletion.polynomial_subst_X pieces projectiveParameter projectiveParameter_mem i

/-- For every arbitrary hypothetical CM module, source freeness holds over
this compatible parameter base as well. The module is not assumed graded,
and no equality with another chosen parameter homomorphism is asserted. -/
theorem projective_parameters_free_of_CM
    (M : Type) [AddCommGroup M] [Module completedRing M]
    [Module.Finite completedRing M] [Nontrivial M]
    (hdepth : SmallCM.localDepth completedRing M = 3) :
    letI : Algebra (MvPowerSeries (Fin 3) ℂ) completedRing :=
      projectiveCompletedParameterHom.toRingHom.toAlgebra
    letI := Module.restrictScalars (MvPowerSeries (Fin 3) ℂ) completedRing M
    Module.Free (MvPowerSeries (Fin 3) ℂ) M := by
  let : Algebra.FiniteType ℂ (SectionCompletion.polynomials pieces) :=
    GradedNormalization.polynomialPiece_finiteType polynomialAlgebra polynomialAlgebra_scale
  let : IsNoetherianRing completedRing :=
    SectionCompletion.isNoetherianRing_of_finiteType pieces zero_piece
  let : Algebra (MvPowerSeries (Fin 3) ℂ) completedRing :=
    projectiveCompletedParameterHom.toRingHom.toAlgebra
  let : Module.Finite (MvPowerSeries (Fin 3) ℂ) completedRing :=
    projectiveCompletedParameterHom_finite
  let := Module.restrictScalars (MvPowerSeries (Fin 3) ℂ) completedRing M
  let : IsScalarTower (MvPowerSeries (Fin 3) ℂ) completedRing M :=
    IsScalarTower.restrictScalars (MvPowerSeries (Fin 3) ℂ) completedRing M
  exact SmallCM.free_over_powerSeries_of_depth_three hdepth

end ExplicitCone


/-! The three projective parameters detect the punctured completed spectrum. -/
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory
namespace ExplicitCone

abbrev completedProjectiveSection (i : Fin 3) : completedRing :=
  SectionCompletion.polynomialToSeries pieces (SourcePullbackChart.coneSection i)

lemma completedProjectiveSection_eq (i : Fin 3) :
    completedProjectiveSection i = projectiveCompletedParameterHom (MvPowerSeries.X i) := by
  exact (SectionCompletion.substHom_variable pieces projectiveParameter (fun _ => 1)
    (fun _ => one_ne_zero) projectiveParameter_mem i).symm

lemma completedProjectiveIdeal_radical :
    (Ideal.span (Set.range completedProjectiveSection)).radical =
      IsLocalRing.maximalIdeal completedRing := by
  let : Algebra (MvPowerSeries (Fin 3) ℂ) completedRing :=
    projectiveCompletedParameterHom.toRingHom.toAlgebra
  let : Module.Finite (MvPowerSeries (Fin 3) ℂ) completedRing :=
    projectiveCompletedParameterHom_finite
  have hs : Ideal.span (Set.range completedProjectiveSection) =
      Ideal.map (algebraMap (MvPowerSeries (Fin 3) ℂ) completedRing)
        (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 3) ℂ)) := by
    rw [← mvPowerSeries_vars_eq_maximal, Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    exact completedProjectiveSection_eq i
  rw [hs]
  exact SmallCM.radical_map_maximalIdeal_of_integral

lemma completedProjectiveSection_mem_maximal (i : Fin 3) :
    completedProjectiveSection i ∈ IsLocalRing.maximalIdeal completedRing := by
  rw [← completedProjectiveIdeal_radical]
  exact Ideal.le_radical (Ideal.subset_span (Set.mem_range_self i))

lemma exists_completedProjectiveSection_notMem (P : Ideal completedRing) [P.IsPrime]
    (hP : P ≠ IsLocalRing.maximalIdeal completedRing) :
    ∃ i : Fin 3, completedProjectiveSection i ∉ P := by
  by_contra! h
  have hI : Ideal.span (Set.range completedProjectiveSection) ≤ P := by
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact h i
  have hmax : IsLocalRing.maximalIdeal completedRing ≤ P := by
    rw [← completedProjectiveIdeal_radical]
    exact (Ideal.radical_mono hI).trans_eq (Ideal.IsPrime.radical inferInstance)
  exact hP (le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) hmax)

lemma completedProjectiveCover :
    (⋃ i : Fin 3, (PrimeSpectrum.basicOpen (completedProjectiveSection i) :
      Set (PrimeSpectrum completedRing))) = {completedClosedPoint}ᶜ := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi⟩ hp
    subst p
    exact hi (completedProjectiveSection_mem_maximal i)
  · intro hp
    apply exists_completedProjectiveSection_notMem p.asIdeal
    intro he
    exact hp (PrimeSpectrum.ext he)

lemma completedProjectiveOpen_eq :
    (⨆ i : Fin 3, PrimeSpectrum.basicOpen (completedProjectiveSection i)) = completedPunctureOpen := by
  apply TopologicalSpace.Opens.ext
  exact (TopologicalSpace.Opens.coe_iSup _).trans
    (completedProjectiveCover.trans completedPunctureOpen_coe.symm)

end ExplicitCone

end


/-! Base change preserves the actual restricted isomorphism used in the
completed source model. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Hom
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

lemma isIso_restrict_of_isPullback {W X Y Z : _root_.AlgebraicGeometry.Scheme} {p : W ⟶ X} {q : W ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback p q f g)
    (U : Z.Opens) [IsIso (g ∣_ U)] : IsIso (p ∣_ (f ⁻¹ᵁ U)) := by
  have he : p ⁻¹ᵁ (f ⁻¹ᵁ U) = p ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ q ⁻¹ᵁ (g ⁻¹ᵁ U) := by
    rw [← _root_.AlgebraicGeometry.Scheme.Hom.comp_preimage, ← _root_.AlgebraicGeometry.Scheme.Hom.comp_preimage, h.w, inf_idem]
  have hh := _root_.AlgebraicGeometry.Scheme.Hom.isPullback_resLE h (le_refl (g ⁻¹ᵁ U)) (le_refl (f ⁻¹ᵁ U)) he
  simp only [_root_.AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict] at hh
  exact hh.isIso_fst_of_isIso

end AlgebraicGeometry.Scheme.Hom

end


/-! The cone morphism is an isomorphism over the complement of the unique closed point. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory
namespace SourceConeMorphism

lemma toUncompleted_preimage_puncture :
    toUncompleted ⁻¹ᵁ SourcePullbackChart.conePuncturedOpen = ExplicitCone.completedPunctureOpen := by
  erw [SourcePullbackChart.conePuncturedOpen, toUncompleted_eq, Scheme.Hom.preimage_iSup]
  exact ExplicitCone.completedProjectiveOpen_eq

/-- Literal completed source isomorphism off the actual closed cone point. -/
instance p_puncture_isIso : IsIso (p ∣_ ExplicitCone.completedPunctureOpen) := by
  rw [← toUncompleted_preimage_puncture]
  exact Scheme.Hom.isIso_restrict_of_isPullback p_isPullback
    SourcePullbackChart.conePuncturedOpen

def puncturedIso : (p ⁻¹ᵁ ExplicitCone.completedPunctureOpen).toScheme ≅
    ExplicitCone.completedPunctureOpen.toScheme := asIso (p ∣_ ExplicitCone.completedPunctureOpen)

@[reassoc] lemma puncturedIso_hom_ι :
    puncturedIso.hom ≫ ExplicitCone.completedPunctureOpen.ι =
      (p ⁻¹ᵁ ExplicitCone.completedPunctureOpen).ι ≫ p :=
  morphismRestrict_ι p ExplicitCone.completedPunctureOpen

end SourceConeMorphism

end


/-! Integrality descends along a quasi-compact schematically dominant map.
Used solely on the proved punctured isomorphism of the literal source W. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory TopologicalSpace
namespace AlgebraicGeometry.IsSchemeTheoreticallyDominant
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.IsSchemeTheoreticallyDominant
lemma isIntegral {X Y : _root_.AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    [_root_.AlgebraicGeometry.IsSchemeTheoreticallyDominant f] [_root_.AlgebraicGeometry.QuasiCompact f] [_root_.AlgebraicGeometry.IsIntegral X] : _root_.AlgebraicGeometry.IsIntegral Y := by
  have hi : IsIrreducible (Set.range f) := by
    simpa using (IrreducibleSpace.isIrreducible_univ X).image f f.continuous.continuousOn
  have hj := hi.closure
  rw [f.denseRange.closure_eq] at hj
  have : IrreducibleSpace Y :=
    { isPreirreducible_univ := hj.2
      toNonempty := ⟨hj.1.choose⟩ }
  have : _root_.AlgebraicGeometry.IsReduced Y := _root_.AlgebraicGeometry.IsSchemeTheoreticallyDominant.isReduced f
  exact _root_.AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced Y
end AlgebraicGeometry.IsSchemeTheoreticallyDominant

end


/-! Integrality of the manuscript's literal completed W, without assuming
its regularity or global smoothness of the surface. The puncture is integral
by the exact completed-cone model and schematically dense by flat completion. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory TopologicalSpace
namespace SourceConeMorphism
open KummerSourceModel

instance completion_flat : Flat completionToPolynomial := by
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

instance sourceCompletion_flat : Flat forgetCompletion := by
  rw [← sourceCompletion_isPullback.isoPullback_hom_fst]
  infer_instance

instance completed_noetherian : IsLocallyNoetherian W := by
  let := ExplicitCone.actualCompletion_noetherian
  exact LocallyOfFiniteType.isLocallyNoetherian p

lemma sourcePuncture_preimage :
    forgetCompletion ⁻¹ᵁ SourcePullbackChart.sourcePuncture =
      p ⁻¹ᵁ ExplicitCone.completedPunctureOpen := by
  change forgetCompletion ⁻¹ᵁ (SourcePullbackChart.coneMorphism ⁻¹ᵁ
    SourcePullbackChart.conePuncturedOpen) = _
  rw [← Scheme.Hom.comp_preimage, ← p_toUncompleted,
    Scheme.Hom.comp_preimage, toUncompleted_preimage_puncture]

instance completedPuncture_schematicallyDominant :
    IsSchemeTheoreticallyDominant (p ⁻¹ᵁ ExplicitCone.completedPunctureOpen).ι := by
  rw [← sourcePuncture_preimage]
  exact IsSchemeTheoreticallyDominant.of_isPullback
    (isPullback_morphismRestrict forgetCompletion SourcePullbackChart.sourcePuncture)

instance completedConePuncture_nonempty : Nonempty ExplicitCone.completedPunctureOpen.toScheme := by
  have hn : ExplicitCone.completedProjectiveSection 0 ≠ 0 := by
    rw [ExplicitCone.completedProjectiveSection_eq]
    apply (map_ne_zero_iff _ ExplicitCone.projectiveCompletedParameterHom_injective).mpr
    intro h
    have he := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)) h
    simp at he
  have hne : (PrimeSpectrum.basicOpen (ExplicitCone.completedProjectiveSection 0) :
      Set (PrimeSpectrum ExplicitCone.completedRing)).Nonempty := by
    rw [← Opens.ne_bot_iff_nonempty]
    intro he
    exact hn ((PrimeSpectrum.basicOpen_eq_bot_iff _).mp he).eq_zero
  obtain ⟨x, hx⟩ := hne
  refine ⟨⟨x, ?_⟩⟩
  rw [← ExplicitCone.completedProjectiveOpen_eq]
  exact Opens.mem_iSup.mpr ⟨0, hx⟩

instance completedConePuncture_integral : IsIntegral ExplicitCone.completedPunctureOpen.toScheme :=
  isIntegral_of_isOpenImmersion ExplicitCone.completedPunctureOpen.ι

instance sourcePuncture_integral : IsIntegral (p ⁻¹ᵁ ExplicitCone.completedPunctureOpen).toScheme :=
  IsIntegral.of_isIso puncturedIso.inv

/-- The completed cone model supporting the pullback double dual is integral and Noetherian. -/
instance completed_integral : IsIntegral W :=
  IsSchemeTheoreticallyDominant.isIntegral (p ⁻¹ᵁ ExplicitCone.completedPunctureOpen).ι

end SourceConeMorphism

end


/-! Actual affine charts of the manuscript's completed W. The rings are the
literal B_i tensor_S A, and the maps form the actual completion square. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
open KummerSourceModel SourceConeMorphism
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring completedSourceAlgebra

def completedChartFirst (i : Fin 3) : Spec (.of (completedSourceChart i)) ⟶ Spec (.of (pullbackChart i)) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : pullbackChart i →+* completedSourceChart i))

def completedChartSecond (i : Fin 3) : Spec (.of (completedSourceChart i)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A →+* completedSourceChart i))

lemma completedChartTensor_isPullback (i : Fin 3) :
    IsPullback (completedChartFirst i) (completedChartSecond i)
      (Spec.map (CommRingCat.ofHom (pullbackBaseMap i))) completionToPolynomial := by
  apply (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (pullbackBaseMap i)))
    completionToPolynomial).of_iso'
      (pullbackSpecIso S (pullbackChart i) A).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    exact pullbackSpecIso_inv_fst S (pullbackChart i) A
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    exact pullbackSpecIso_inv_snd S (pullbackChart i) A
  · simp
  · simp

def completedIota (i : Fin 3) : Spec (.of (completedSourceChart i)) ⟶ W :=
  pullback.lift (completedChartFirst i ≫ pullbackIota i) (completedChartSecond i)
    (by rw [Category.assoc, pullbackIota_base]; exact (completedChartTensor_isPullback i).w) ≫
      sourceCompletion_isPullback.isoPullback.inv

@[reassoc] lemma completedIota_forget (i : Fin 3) : completedIota i ≫ forgetCompletion =
    completedChartFirst i ≫ pullbackIota i := by
  simp only [completedIota, Category.assoc, IsPullback.isoPullback_inv_fst, pullback.lift_fst]

@[reassoc] lemma completedIota_base (i : Fin 3) : completedIota i ≫ (g ≫ completedBlowdown) =
    completedChartSecond i := by
  simp only [completedIota, Category.assoc, IsPullback.isoPullback_inv_snd, pullback.lift_snd]

lemma completedIota_isPullback (i : Fin 3) :
    IsPullback (completedIota i) (completedChartFirst i) forgetCompletion (pullbackIota i) := by
  have hh : IsPullback (completedIota i ≫ (g ≫ completedBlowdown)) (completedChartFirst i)
      completionToPolynomial (pullbackIota i ≫ (g₀ ≫ blowdown)) := by
    rw [completedIota_base, pullbackIota_base]
    exact (completedChartTensor_isPullback i).flip
  exact hh.of_right (completedIota_forget i) sourceCompletion_isPullback.flip

instance (i : Fin 3) : IsOpenImmersion (completedIota i) := by
  rw [← (completedIota_isPullback i).isoPullback_hom_fst]
  infer_instance

lemma completedIota_opensRange (i : Fin 3) : (completedIota i).opensRange =
    forgetCompletion ⁻¹ᵁ (pullbackIota i).opensRange := by
  have hh := (Scheme.Hom.opensRange_comp_of_isIso
    (completedIota_isPullback i).isoPullback.hom
    (pullback.fst forgetCompletion (pullbackIota i))).trans
      (Scheme.Hom.opensRange_pullbackFst (pullbackIota i) forgetCompletion)
  simpa only [(completedIota_isPullback i).isoPullback_hom_fst] using hh

def completedCover : W.OpenCover where
  I₀ := Fin 3
  X i := Spec (.of (completedSourceChart i))
  f := completedIota
  mem₀ := by
    have (i : Fin 3) : IsOpenImmersion (completedIota i) := by
      rw [← (completedIota_isPullback i).isoPullback_hom_fst]
      infer_instance
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun i => ?_⟩
    swap
    · change IsOpenImmersion (completedIota i)
      infer_instance
    intro x
    obtain ⟨i,y,hy⟩ := sourceCover.exists_eq (forgetCompletion x)
    change Fin 3 at i
    have hx : x ∈ (completedIota i).opensRange := by
      rw [completedIota_opensRange]
      exact ⟨y,hy⟩
    obtain ⟨z,hz⟩ := hx
    exact ⟨i,z,hz⟩

end SourcePullbackChart

end


/-! The zero-evaluation ring maps are precisely the affine charts
of the actual zero-section immersion, not quotient maps on replacement schemes. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct _root_.Polynomial _root_.OAI.Polynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourceZeroSections
open KummerSourceModel SourcePullbackChart
attribute [local instance] originScalar originChart
  originTensorChartCommRing originTensorChartSemiring originTensorPlaneCommRing
  originTensorPlaneSemiring originTensorCommRing originTensorSemiring
  integralSurfaceCommRing integralSurfaceSemiring integralPullbackCommRing integralPullbackSemiring

lemma planeIota_originFiber (i : Fin 3) :
    planeIota i ≫ originFiberIso.inv =
      Spec.map (CommRingCat.ofHom (originTensorEquiv i).toRingHom) ≫ originFiberIota i := by
  apply (cancel_mono originFiberIso.hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change planeIota i = _ ≫ fiberDirection
  rw [Category.assoc, originFiberIota_direction, ← Category.assoc, ← Spec.map_comp]
  have hh : CommRingCat.ofHom (originTensorInverse i) ≫
      CommRingCat.ofHom (originTensorEquiv i).toRingHom = 𝟙 _ := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (originTensor_right_inverse i)
  rw [hh, Spec.map_id, Category.id_comp]

lemma planeIota_zero (i : Fin 3) :
    planeIota i ≫ planeZero = Spec.map (CommRingCat.ofHom (zeroEvaluation i)) ≫ blowupIota i := by
  rw [planeZero, ← Category.assoc, planeIota_originFiber, Category.assoc, originFiberIota_snd,
    ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro e
  change originTensorMap i ((1 : ℂ) ⊗ₜ[SourcePullbackChart.S] e) = zeroEvaluation i e
  rw [originTensorMap_tmul, map_one, one_mul]

lemma planeIota_scalar (i : Fin 3) :
    planeIota i ≫ planeScalar = Spec.map (CommRingCat.ofHom (algebraMap ℂ (planeChart i))) := by
  rw [planeScalar, ← Category.assoc, planeIota_originFiber, Category.assoc, originFiberIota_fst,
    ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change originTensorMap i (a ⊗ₜ[SourcePullbackChart.S] (1 : chart i)) = algebraMap ℂ (planeChart i) a
  rw [originTensorMap_tmul, map_one, mul_one]

lemma zeroEvaluation_blowup (i : Fin 3) :
    (pullbackZeroEvaluation i).comp (blowupIn i) =
      (surfaceDirectionMap i).comp (zeroEvaluation i) := by
  have hh : ((pullbackZeroEvaluation i).comp (blowupIn i)).comp
      (planePolynomialEquiv i).toRingHom =
      ((surfaceDirectionMap i).comp (zeroEvaluation i)).comp
      (planePolynomialEquiv i).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      change pullbackZeroEvaluation i (blowupIn i (planePolynomialEquiv i (C a))) =
        surfaceDirectionMap i (zeroEvaluation i (planePolynomialEquiv i (C a)))
      rw [planePolynomialEquiv_C, ← tensor_balance i a, pullbackZeroEvaluation_surface,
        zeroEvaluation_direction]
    · change pullbackZeroEvaluation i (blowupIn i (planePolynomialEquiv i X)) =
        surfaceDirectionMap i (zeroEvaluation i (planePolynomialEquiv i X))
      rw [planePolynomialEquiv_X, zeroEvaluation_fiber, map_zero]
      exact pullbackZeroEvaluation_fiber i
  apply RingHom.ext
  intro e
  have hx := RingHom.congr_fun hh ((planePolynomialEquiv i).symm e)
  change pullbackZeroEvaluation i (blowupIn i (planePolynomialEquiv i ((planePolynomialEquiv i).symm e))) =
    surfaceDirectionMap i (zeroEvaluation i (planePolynomialEquiv i ((planePolynomialEquiv i).symm e))) at hx
  rw [AlgEquiv.apply_symm_apply] at hx
  change pullbackZeroEvaluation i (blowupIn i e) = surfaceDirectionMap i (zeroEvaluation i e)
  exact hx

@[reassoc] lemma surfaceIota_sourceZero (i : Fin 3) :
    surfaceIota i ≫ sourceZero = Spec.map (CommRingCat.ofHom (pullbackZeroEvaluation i)) ≫ pullbackIota i := by
  apply pullback.hom_ext
  · rw [Category.assoc, sourceZero_fst, Category.comp_id, Category.assoc,
      pullbackIota_surface, ← Category.assoc, ← Spec.map_comp]
    have hh : CommRingCat.ofHom (surfaceIn i) ≫ CommRingCat.ofHom (pullbackZeroEvaluation i) = 𝟙 _ := by
      apply CommRingCat.hom_ext
      exact RingHom.ext (pullbackZeroEvaluation_surface i)
    rw [hh, Spec.map_id, Category.id_comp]
  · change surfaceIota i ≫ sourceZero ≫ g₀ =
      Spec.map (CommRingCat.ofHom (pullbackZeroEvaluation i)) ≫ pullbackIota i ≫ g₀
    rw [sourceZero_g₀, ← Category.assoc, surface_chart_square, Category.assoc,
      planeIota_zero, pullbackIota_blowup, ← Category.assoc, ← Category.assoc]
    have hh : CommRingCat.ofHom (zeroEvaluation i) ≫
        CommRingCat.ofHom (surfaceDirectionMap i) =
      CommRingCat.ofHom (blowupIn i) ≫ CommRingCat.ofHom (pullbackZeroEvaluation i) :=
      CommRingCat.hom_ext (zeroEvaluation_blowup i).symm
    have hm : Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)) ≫
        Spec.map (CommRingCat.ofHom (zeroEvaluation i)) =
      Spec.map (CommRingCat.ofHom (pullbackZeroEvaluation i)) ≫
        Spec.map (CommRingCat.ofHom (blowupIn i)) :=
      (Spec.map_comp (CommRingCat.ofHom (zeroEvaluation i))
        (CommRingCat.ofHom (surfaceDirectionMap i))).symm.trans
          ((congrArg Spec.map hh).trans
            (Spec.map_comp (CommRingCat.ofHom (blowupIn i))
              (CommRingCat.ofHom (pullbackZeroEvaluation i))))
    exact congrArg (fun f : Spec (.of (surfaceChart i)) ⟶ Spec (.of (chart i)) =>
      f ≫ blowupIota i) hm

@[reassoc] lemma surfaceIota_scalar (i : Fin 3) :
    surfaceIota i ≫ (ExplicitCone.projectiveNormalization ≫ planeScalar) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (surfaceChart i))) := by
  rw [← Category.assoc, surface_chart_square, Category.assoc, planeIota_scalar, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext fun a => (SectionCompletion.linearChartMap_scalar
    ExplicitCone.pieces ExplicitCone.projectiveParameter ExplicitCone.projectiveParameter_mem i a)

@[reassoc] lemma completedSourceZero_forget : completedSourceZero ≫ SourceConeMorphism.forgetCompletion = sourceZero := by
  apply pullback.hom_ext
  · rw [Category.assoc, SourceConeMorphism.forgetCompletion_surface, completedSourceZero_fst, sourceZero_fst]
  · change completedSourceZero ≫ SourceConeMorphism.forgetCompletion ≫ g₀ = sourceZero ≫ g₀
    rw [SourceConeMorphism.forgetCompletion_blowup, completedSourceZero_g_assoc,
      completedPlaneZero_fst, sourceZero_g₀]

end SourceZeroSections

end


/-! The actual exceptional immersion has exactly the regular
principal quotient as its affine coordinate map on the genuine source charts. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
open KummerSourceModel SourceConeMorphism SourceZeroSections
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra

lemma completedZeroEvaluation_left (i : Fin 3) :
    (completedZeroEvaluation i).comp
      (Algebra.TensorProduct.includeLeftRingHom : pullbackChart i →+* completedSourceChart i) =
    pullbackZeroEvaluation i := by
  apply RingHom.ext
  intro q
  change completedZeroEvaluation i (q ⊗ₜ[S] 1) = _
  rw [completedZeroEvaluation_tmul, map_one, map_one, mul_one]

lemma completedZeroEvaluation_right (i : Fin 3) :
    (completedZeroEvaluation i).comp
      (Algebra.TensorProduct.includeRight.toRingHom : A →+* completedSourceChart i) =
    (algebraMap ℂ (surfaceChart i)).comp MvPowerSeries.constantCoeff := by
  apply RingHom.ext
  intro a
  change completedZeroEvaluation i ((1 : pullbackChart i) ⊗ₜ[S] a) = _
  rw [completedZeroEvaluation_tmul, map_one, one_mul]
  rfl

abbrev completedZeroChart (i : Fin 3) : Spec (.of (surfaceChart i)) ⟶ Spec (.of (completedSourceChart i)) :=
  Spec.map (CommRingCat.ofHom (completedZeroEvaluation i))

@[reassoc] lemma completedZeroChart_first (i : Fin 3) :
    completedZeroChart i ≫ completedChartFirst i = Spec.map (CommRingCat.ofHom (pullbackZeroEvaluation i)) := by
  rw [completedChartFirst, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (completedZeroEvaluation_left i)

@[reassoc] lemma completedZeroChart_second (i : Fin 3) :
    completedZeroChart i ≫ completedChartSecond i =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (surfaceChart i))) ≫ seriesOrigin := by
  rw [completedChartSecond, ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (completedZeroEvaluation_right i)

/-- Exact commutative square for the actual completed zero immersion. -/
@[reassoc] lemma surfaceIota_completedSourceZero (i : Fin 3) :
    surfaceIota i ≫ completedSourceZero = completedZeroChart i ≫ completedIota i := by
  apply sourceCompletion_isPullback.hom_ext
  · rw [Category.assoc, completedSourceZero_forget, Category.assoc, completedIota_forget,
      completedZeroChart_first_assoc, surfaceIota_sourceZero]
  · simp only [Category.assoc, completedSourceZero_g_assoc, completedPlaneZero_blowdown,
      surfaceIota_scalar_assoc, completedIota_base, completedZeroChart_second]

lemma surfaceIota_opensRange (i : Fin 3) : (surfaceIota i).opensRange =
    ExplicitCone.projectiveNormalization ⁻¹ᵁ (planeIota i).opensRange := by
  have hh := (Scheme.Hom.opensRange_comp_of_isIso (surface_isPullback i).isoPullback.hom
    (pullback.fst ExplicitCone.projectiveNormalization (planeIota i))).trans
      (Scheme.Hom.opensRange_pullbackFst (planeIota i) ExplicitCone.projectiveNormalization)
  simpa only [(surface_isPullback i).isoPullback_hom_fst] using hh

lemma surfaceIota_cover : (⨆ i, (surfaceIota i).opensRange) = ⊤ := by
  simp_rw [surfaceIota_opensRange]
  rw [← Scheme.Hom.preimage_iSup]
  have hh := planeCover.iSup_opensRange
  change (⨆ i, (planeIota i).opensRange) = ⊤ at hh
  rw [hh, Scheme.Hom.preimage_top]

lemma surfaceZero_chart_preimage (i : Fin 3) :
    completedSourceZero ⁻¹ᵁ (completedIota i).opensRange = (surfaceIota i).opensRange := by
  rw [completedIota_opensRange, ← Scheme.Hom.comp_preimage, completedSourceZero_forget,
    pullbackIota_opensRange, ← Scheme.Hom.comp_preimage, sourceZero_g₀]
  have hb : (blowupIota i).opensRange = direction ⁻¹ᵁ (planeIota i).opensRange := by
    dsimp only [blowupIota, planeIota]
    erw [Proj.opensRange_awayι, Proj.opensRange_awayι]
    rfl
  rw [hb, ← Scheme.Hom.comp_preimage, Category.assoc, planeZero_direction, Category.comp_id,
    surfaceIota_opensRange]

lemma completedZero_isPullback (i : Fin 3) :
    IsPullback (surfaceIota i) (completedZeroChart i) completedSourceZero (completedIota i) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact surfaceIota_completedSourceZero i
  · exact surfaceZero_chart_preimage i

instance completedSourceChart_noetherian (i : Fin 3) : IsNoetherianRing (completedSourceChart i) := by
  have : IsLocallyNoetherian (Spec (.of (completedSourceChart i))) :=
    LocallyOfFiniteType.isLocallyNoetherian (completedIota i)
  exact isLocallyNoetherian_Spec.mp this

end SourcePullbackChart

end

end OAI
