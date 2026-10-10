import OAI.AlgebraicGeometry.SurfaceCones.AffineLineEpiIso

namespace OAI

private local instance scalarCoherentSectionModule {Z : AlgebraicGeometry.Scheme.{0}}
    (M : CoherentGlobal.Coh Z) (U : Z.Opensᵒᵖ) : Module (Z.sheaf.obj.obj U) (M.obj.val.obj U) :=
  (M.obj.val.obj U).isModule

/-!
# Conormal coordinates, regularity and ranks

This development accompanies *A Complete Local Domain without a Small
Cohen–Macaulay Module* (OpenAI, 2026).
-/

/-! Pullback transports scalar endomorphisms by the map on global functions. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
open Scheme.Modules ActualCartier ActualSheafTensor
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

lemma scalar_structure (r : Γ(Y,⊤)) :
    scalar r ≫ structureMap f =
      structureMap f ≫ (pushforward f).map (scalar (f.appTop r)) := by
  apply unitHom_ext_top
  change f.app ⊤ ((scalar r).val.app (op ⊤) (1 : Γ(Y,⊤))) =
    (scalar (f.appTop r)).val.app (op (f ⁻¹ᵁ ⊤)) (f.app ⊤ 1)
  erw [fromUnit_top, one_smul, map_one, fromUnit_app, one_smul]
  change f.app ⊤ r = X.presheaf.map (homOfLE (show f ⁻¹ᵁ ⊤ ≤ ⊤ from le_top)).op (f.appTop r)
  have he : (homOfLE (show f ⁻¹ᵁ ⊤ ≤ ⊤ from le_top)).op = 𝟙 (op (⊤ : X.Opens)) :=
    Subsingleton.elim _ _
  rw [he]
  erw [X.presheaf.map_id]
  rfl

lemma pullback_scalar (r : Γ(Y,⊤)) :
    (Scheme.Modules.pullback f).map (scalar r) ≫ (sheafPullbackUnitIso f).hom =
      (sheafPullbackUnitIso f).hom ≫ scalar (f.appTop r) := by
  let F : Y.Modules ⥤ X.Modules := Scheme.Modules.pullback f
  let G : X.Modules ⥤ Y.Modules := pushforward f
  let adj : F ⊣ G := pullbackPushforwardAdjunction f
  let UY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let UX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let e : F.obj UY ≅ UX := sheafPullbackUnitIso f
  let a : UY ⟶ UY := scalar r
  let b : UX ⟶ UX := scalar (f.appTop r)
  have hu : adj.unit.app UY ≫ G.map e.hom =
      structureMap f := pullbackUnit_adj f
  have hl : adj.homEquiv _ _ (F.map a ≫ e.hom) = a ≫ structureMap f := by
    change adj.unit.app _ ≫ G.map (F.map a ≫ e.hom) = _
    exact (congrArg (adj.unit.app UY ≫ ·) (G.map_comp (F.map a) e.hom)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ G.map e.hom) (adj.unit_naturality a)).trans
          ((Category.assoc _ _ _).trans (congrArg (a ≫ ·) hu))))
  have hr : adj.homEquiv _ _ (e.hom ≫ b) = structureMap f ≫ G.map b := by
    change adj.unit.app _ ≫ G.map (e.hom ≫ b) = _
    exact (congrArg (adj.unit.app UY ≫ ·) (G.map_comp e.hom b)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ G.map b) hu))
  exact (adj.homEquiv _ _).injective
    (hl.trans ((scalar_structure f r).trans hr.symm))

end ActualSections

end

/-! On each standard projective plane chart, the conormal frames
have coordinates x_j/x_i induced by the three ideal generators. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
open Scheme.Modules ActualSheafTensor
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

lemma pullback_scalar_inv (r : Γ(Y,⊤)) :
    (sheafPullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map (scalar r) =
      scalar (f.appTop r) ≫ (sheafPullbackUnitIso f).inv := by
  apply (Iso.inv_comp_eq (sheafPullbackUnitIso f)).mpr
  exact ((Iso.eq_comp_inv (sheafPullbackUnitIso f)).mpr (pullback_scalar f r)).trans
    (Category.assoc _ _ _)

end ActualSections
namespace SourcePullbackChart
open KummerSourceModel SourceZeroSections Scheme.Modules ActualCartier ActualSections ActualSheafTensor
attribute [local instance] originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra

/-- The exact inverse image of the global conormal on this chart. -/
def planeConormalChartTransport (i : Fin 3) :
    (restrictFunctor (planeIota i)).obj
      ((Scheme.Modules.pullback completedPlaneZero).obj (idealSheaf completedPlaneZero)) ≅
    (Scheme.Modules.pullback (completedPlaneZeroChart i)).obj
      ((restrictFunctor (completedBlowupIota i)).obj (idealSheaf completedPlaneZero)) :=
  (ActualChartPullback.squareIso (planeIota i) completedPlaneZero
    (completedPlaneZeroChart i) (completedBlowupIota i) (planeIota_completedPlaneZero i)).app _

def planeConormalChartSection (i j : Fin 3) :
    SheafOfModules.unit (Spec (.of (planeChart i))).ringCatSheaf ⟶
    (restrictFunctor (planeIota i)).obj
      ((Scheme.Modules.pullback completedPlaneZero).obj (idealSheaf completedPlaneZero)) :=
  (sheafPullbackUnitIso (completedPlaneZeroChart i)).inv ≫
    (Scheme.Modules.pullback (completedPlaneZeroChart i)).map
      (chartGenerator completedPlaneZero (completedBlowupIota i)
        (planeParameter j) (planeParameter_killed j)) ≫
      (planeConormalChartTransport i).inv

lemma planeConormalChartSection_isIso (i : Fin 3) : IsIso (planeConormalChartSection i i) := by
  have hG : IsIso (chartGenerator completedPlaneZero (completedBlowupIota i)
      (planeParameter i) (planeParameter_killed i)) := by
    have hI : IsIso ((restrictFunctor (completedBlowupIota i)).map (planeIdealGenerator i)) :=
      planeIdealGenerator_chart_isIso i
    change IsIso ((restrictUnitIso (completedBlowupIota i)).inv ≫
      (restrictFunctor (completedBlowupIota i)).map (planeIdealGenerator i))
    exact IsIso.comp_isIso' (restrictUnitIso (completedBlowupIota i)).isIso_inv hI
  have hF : IsIso ((Scheme.Modules.pullback (completedPlaneZeroChart i)).map
      (chartGenerator completedPlaneZero (completedBlowupIota i)
        (planeParameter i) (planeParameter_killed i))) :=
    ((Scheme.Modules.pullback (completedPlaneZeroChart i)).mapIso
      (@asIso _ _ _ _ _ hG)).isIso_hom
  dsimp only [planeConormalChartSection]
  exact IsIso.comp_isIso' (sheafPullbackUnitIso (completedPlaneZeroChart i)).isIso_inv
    (IsIso.comp_isIso' hF (planeConormalChartTransport i).isIso_inv)

lemma planeZeroChart_transition (i j : Fin 3) :
    (completedPlaneZeroChart i).appTop
      ((Scheme.ΓSpecIso (.of (completedBlowupChart i))).inv (planeTransitionCoefficient i j)) =
    (Scheme.ΓSpecIso (.of (planeChart i))).inv
      (SectionCompletion.polynomialChartDehom i (MvPolynomial.X j)) := by
  have he := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (completedPlaneEvaluation i))).symm (planeTransitionCoefficient i j)
  change (completedPlaneZeroChart i).appTop _ = _ at he
  exact he.trans (congrArg (Scheme.ΓSpecIso (.of (planeChart i))).inv
    (planeTransitionCoefficient_residue i j))

/-- The conormal chart coordinates are the standard projective ratios. -/
lemma planeConormalChartSection_ratio (i j : Fin 3) :
    planeConormalChartSection i j =
      scalar ((Scheme.ΓSpecIso (.of (planeChart i))).inv
        (SectionCompletion.polynomialChartDehom i (MvPolynomial.X j))) ≫
      planeConormalChartSection i i := by
  have he := chartGenerator_ratio completedPlaneZero (completedBlowupIota i)
    (planeParameter i) (planeParameter j) (planeParameter_killed i) (planeParameter_killed j)
    _ (planeParameter_chart_ratio i j)
  let F : (Spec (.of (completedBlowupChart i))).Modules ⥤ (Spec (.of (planeChart i))).Modules :=
    Scheme.Modules.pullback (completedPlaneZeroChart i)
  let UY : (Spec (.of (completedBlowupChart i))).Modules := SheafOfModules.unit _
  let UX : (Spec (.of (planeChart i))).Modules := SheafOfModules.unit _
  let e : F.obj UY ≅ UX := sheafPullbackUnitIso (completedPlaneZeroChart i)
  let a : UY ⟶ UY := scalar ((Scheme.ΓSpecIso (.of (completedBlowupChart i))).inv
    (planeTransitionCoefficient i j))
  let b : UX ⟶ UX := scalar ((Scheme.ΓSpecIso (.of (planeChart i))).inv
    (SectionCompletion.polynomialChartDehom i (MvPolynomial.X j)))
  let d := planeConormalChartTransport i
  let v := chartGenerator completedPlaneZero (completedBlowupIota i)
    (planeParameter i) (planeParameter_killed i)
  let w := chartGenerator completedPlaneZero (completedBlowupIota i)
    (planeParameter j) (planeParameter_killed j)
  have hm : F.map w = F.map a ≫ F.map v :=
    (congrArg F.map he).trans (F.map_comp a v)
  have hc : e.inv ≫ F.map a = b ≫ e.inv := by
    have h := pullback_scalar_inv (completedPlaneZeroChart i)
      ((Scheme.ΓSpecIso (.of (completedBlowupChart i))).inv (planeTransitionCoefficient i j))
    erw [planeZeroChart_transition] at h
    exact h
  change e.inv ≫ F.map w ≫ d.inv = b ≫ e.inv ≫ F.map v ≫ d.inv
  exact (congrArg (fun k => e.inv ≫ k ≫ d.inv) hm).trans
    ((congrArg (e.inv ≫ ·) (Category.assoc (F.map a) (F.map v) d.inv)).trans
      ((Category.assoc e.inv (F.map a) (F.map v ≫ d.inv)).symm.trans
        ((congrArg (· ≫ F.map v ≫ d.inv) hc).trans (Category.assoc _ _ _))))

end SourcePullbackChart

end

/-! Every standard chart of Proj C[x₀,x₁,x₂] is a polynomial algebra
in the remaining two variables. -/
noncomputable section
open _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization _root_.MvPolynomial _root_.OAI.MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
abbrev planeVariables (i : Fin 3) := {j : Fin 3 // j ≠ i}
abbrev planePolynomial (i : Fin 3) := MvPolynomial (planeVariables i) ℂ

def planeSubstitution (i : Fin 3) : S →ₐ[ℂ] planePolynomial i :=
  MvPolynomial.aeval (fun j => if h : j = i then 1 else MvPolynomial.X ⟨j,h⟩)
@[simp] lemma planeSubstitution_self (i : Fin 3) :
    planeSubstitution i (MvPolynomial.X i) = 1 := by
  simp [planeSubstitution]
@[simp] lemma planeSubstitution_other (i : Fin 3) (j : planeVariables i) :
    planeSubstitution i (MvPolynomial.X j.val) = MvPolynomial.X j := by
  simp [planeSubstitution, j.property]

def planeToPolynomial (i : Fin 3) : planeChart i →+* planePolynomial i :=
  (Localization.awayLift (planeSubstitution i).toRingHom (MvPolynomial.X i)
    (by simp)).comp (algebraMap (planeChart i) (Localization.Away (MvPolynomial.X i)))

lemma planeToPolynomial_mk (i : Fin 3) (n : ℕ) (a : S)
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℂ (n • 1)) :
    planeToPolynomial i (Away.mk (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)
      (MvPolynomial.isHomogeneous_X ℂ i) n a ha) = planeSubstitution i a := by
  dsimp only [planeToPolynomial, RingHom.comp_apply]
  erw [HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  rw [Localization.awayLift_mk _ _ _ (1 : planePolynomial i) (by simp)]
  simp

lemma planeToPolynomial_ratio (i j : Fin 3) :
    planeToPolynomial i (SectionCompletion.polynomialChartDehom i (MvPolynomial.X j)) =
      planeSubstitution i (MvPolynomial.X j) := by
  simp only [SectionCompletion.polynomialChartDehom, MvPolynomial.aeval_X, planeToPolynomial_mk]

lemma planeToPolynomial_scalar (i : Fin 3) (a : ℂ) :
    planeToPolynomial i (algebraMap ℂ (planeChart i) a) = algebraMap ℂ (planePolynomial i) a := by
  have hs : algebraMap ℂ (planeChart i) a =
      Away.mk (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)
        (MvPolynomial.isHomogeneous_X ℂ i) 0 (algebraMap ℂ S a)
        (by simp) := by
    apply HomogeneousLocalization.val_injective
    rfl
  erw [hs, planeToPolynomial_mk]
  exact (planeSubstitution i).commutes a

def planeToPolynomialAlg (i : Fin 3) : planeChart i →ₐ[ℂ] planePolynomial i :=
  { planeToPolynomial i with commutes' := planeToPolynomial_scalar i }

def polynomialToPlane (i : Fin 3) : planePolynomial i →ₐ[ℂ] planeChart i :=
  MvPolynomial.aeval (fun j => SectionCompletion.polynomialChartDehom i (MvPolynomial.X j.val))

lemma polynomialChartDehom_self (i : Fin 3) :
    SectionCompletion.polynomialChartDehom (k := ℂ) i (MvPolynomial.X i) = 1 := by
  apply planeField_injective i
  rw [planeField_ratio, div_self (coordinate_ne_zero i), map_one]

lemma planeToPolynomial_left (i : Fin 3) :
    (planeToPolynomialAlg i).comp (polynomialToPlane i) = AlgHom.id ℂ (planePolynomial i) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, polynomialToPlane, MvPolynomial.aeval_X, AlgHom.id_apply]
  change planeToPolynomial i _ = _
  rw [planeToPolynomial_ratio, planeSubstitution_other]

lemma planeToPolynomial_right (i : Fin 3) :
    (polynomialToPlane i).comp (planeToPolynomialAlg i) = AlgHom.id ℂ (planeChart i) := by
  apply AlgHom.coe_ringHom_injective
  apply RingHom.ext
  intro a
  obtain ⟨v, rfl⟩ := polynomialChartDehom_surjective i a
  have hh : ((polynomialToPlane i).comp (planeToPolynomialAlg i)).comp
      (SectionCompletion.polynomialChartDehom i) = SectionCompletion.polynomialChartDehom i := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply]
    change polynomialToPlane i (planeToPolynomial i _) = _
    rw [planeToPolynomial_ratio]
    by_cases h : j = i
    · subst j
      rw [planeSubstitution_self, map_one, polynomialChartDehom_self]
    · simp only [planeSubstitution, MvPolynomial.aeval_X, dite_eq_right h,
        polynomialToPlane, MvPolynomial.aeval_X]
  exact congrArg (fun f : S →ₐ[ℂ] planeChart i => f v) hh

def planePolynomialEquivalence (i : Fin 3) : planePolynomial i ≃ₐ[ℂ] planeChart i :=
  AlgEquiv.ofAlgHom (polynomialToPlane i) (planeToPolynomialAlg i)
    (planeToPolynomial_right i) (planeToPolynomial_left i)

instance planeChart_regular (i : Fin 3) : IsRegularRing (planeChart i) :=
  IsRegularRing.of_ringEquiv (planePolynomialEquivalence i).toRingEquiv
instance planeChart_smooth (i : Fin 3) : Algebra.Smooth ℂ (planeChart i) := by
  let : Algebra.Smooth ℂ (planePolynomial i) := ⟨inferInstance, inferInstance⟩
  exact
  Algebra.Smooth.of_equiv (planePolynomialEquivalence i)
end SourcePullbackChart

end

/-! Ambient local rings along the closed exceptional fiber are regular. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace SourcePullbackChart
open KummerSourceModel SourceZeroSections
attribute [local instance] originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra
instance completedBlowupChart_nontrivial (i : Fin 3) : Nontrivial (completedBlowupChart i) :=
  (completedPlaneEvaluation_surjective i).nontrivial
instance completedBlowupChart_integral (i : Fin 3) :
    IsIntegral (Spec (.of (completedBlowupChart i))) :=
  isIntegral_of_isOpenImmersion (completedBlowupIota i)
instance completedBlowupChart_domain (i : Fin 3) : IsDomain (completedBlowupChart i) :=
  (affine_isIntegral_iff (.of (completedBlowupChart i))).mp inferInstance

def completedPlanePrincipalQuotient (i : Fin 3) :
    (completedBlowupChart i ⧸ Ideal.span {completedBlowupFiber i}) ≃+* planeChart i :=
  (Ideal.quotientEquiv _ _ (RingEquiv.refl _) (by simp [completedBlowupZeroIdeal_eq])).trans
    (completedPlaneQuotient i)

instance completedPlanePrincipalQuotient_regular (i : Fin 3) :
    IsRegularRing (completedBlowupChart i ⧸ Ideal.span {completedBlowupFiber i}) :=
  IsRegularRing.of_ringEquiv (completedPlanePrincipalQuotient i).symm

/-- Every point of the exceptional fiber has a regular ambient local ring
on each of the three completed charts. -/
lemma completedBlowup_regular_at_fiber (i : Fin 3) (p : Ideal (completedBlowupChart i))
    [p.IsPrime] (hp : completedBlowupFiber i ∈ p) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  apply RegularCartierLocalization.regular_at_prime (completedBlowupFiber i) _ p hp
  intro h
  have hh := completedBlowupFiber_regular i
  rw [h] at hh
  exact one_ne_zero (hh (by simp : (0 : completedBlowupChart i) • (1 : completedBlowupChart i) =
    (0 : completedBlowupChart i) • (0 : completedBlowupChart i)))
end SourcePullbackChart

end

/-! Rank inequalities for quotients of conormal-twisted free sheaves. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Scheme.Modules
namespace CoherentChartRank
open CoherentGlobal ActualCartier
variable {X : Scheme.{0}} [IsLocallyNoetherian X] {R : CommRingCat.{0}}
  [IsNoetherianRing R] [IsDomain R] (j : Spec R ⟶ X) [IsOpenImmersion j]

lemma chart_epi_le {B G : Coh X} (q : B ⟶ G) [Epi q] :
    Module.finrank R (chartSections j G) ≤ Module.finrank R (chartSections j B) := by
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hs : S.ShortExact := { exact := ShortComplex.exact_kernel q }
  have h := chart_add j S hs
  exact h.symm ▸ Nat.le_add_left _ _

def chartFreeSectionsIso (I : Type) [Finite I] :
    chartSections j (coherentFree X I) ≅ ModuleCat.of R (I →₀ R) :=
  (moduleSpecΓFunctor (R := R)).mapIso
    (IsoPuncturePushforward.restrictFreeIso j I ≪≫ (tildeFinsupp (R := R) I).symm) ≪≫
      (tilde.toTildeΓNatIso (R := R)).symm.app _

omit [IsLocallyNoetherian X] [IsNoetherianRing R] in
lemma chart_free_rank (I : Type) [Fintype I] :
    Module.finrank R (chartSections j (coherentFree X I)) = Fintype.card I := by
  rw [(chartFreeSectionsIso j I).toLinearEquiv.finrank_eq]
  exact Module.finrank_finsupp_self R
end CoherentChartRank

end

/-! The plane-conormal line has rank one on each standard chart.
The lattice layers therefore satisfy 0 ≤ rank Q_j ≤ N. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Scheme.Modules
namespace SourceConeMorphism
open KummerSourceModel SourcePullbackChart SourceZeroSections CoherentGlobal ActualCartier
  ActualSheafTensor CartierImageFiltration
attribute [local instance] originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra

attribute [local instance] planeChart_noetherian

abbrev planeChartRank (B : Coh ExplicitCone.plane) (i : Fin 3) : ℕ :=
  Module.finrank (planeChart i) (CoherentChartRank.chartSections (planeIota i) B)

def planeConormalChartUnitIso (i : Fin 3) :
    (restrictFunctor (planeIota i)).obj
      ((Scheme.Modules.pullback completedPlaneZero).obj (idealSheaf completedPlaneZero)) ≅
        SheafOfModules.unit (Spec (.of (planeChart i))).ringCatSheaf :=
  (restrictFunctorIsoPullback (planeIota i)).app _ ≪≫
    (pullbackComp (planeIota i) completedPlaneZero).app _ ≪≫
    (pullbackCongr (planeIota_completedPlaneZero i)).app _ ≪≫
    ((pullbackComp (completedPlaneZeroChart i) (completedBlowupIota i)).app _).symm ≪≫
    (Scheme.Modules.pullback (completedPlaneZeroChart i)).mapIso
      (((restrictFunctorIsoPullback (completedBlowupIota i)).app _).symm ≪≫
        planeIdealChartIso i) ≪≫ sheafPullbackUnitIso (completedPlaneZeroChart i)

def planeConormalChartIso (B : Coh ExplicitCone.plane) (i : Fin 3) :
    (restrictFunctor (planeIota i)).obj
      (conormalTensor completedPlaneZero planeIdealLine B).obj ≅
      (restrictFunctor (planeIota i)).obj B.obj :=
  (tensorOpenRestrictNatIso (planeIota i)
    ((Scheme.Modules.pullback completedPlaneZero).obj (idealSheaf completedPlaneZero))).app B.obj ≪≫
    (trivialTensorIso (Spec (.of (planeChart i))).sheaf (planeConormalChartUnitIso i)).app _

lemma planeConormal_rank (B : Coh ExplicitCone.plane) (i : Fin 3) :
    planeChartRank ((conormalFunctor completedPlaneZero planeIdealLine).obj B) i =
      planeChartRank B i :=
  ((moduleSpecΓFunctor (R := CommRingCat.of (planeChart i))).mapIso
    (planeConormalChartIso B i)).toLinearEquiv.finrank_eq

lemma planeConormalPower_rank (B : Coh ExplicitCone.plane) (i : Fin 3) (j : ℕ) :
    planeChartRank ((power (conormalFunctor completedPlaneZero planeIdealLine) j).obj B) i =
      planeChartRank B i := by
  induction j generalizing B with
  | zero => rfl
  | succ j ih =>
    change planeChartRank ((power (conormalFunctor completedPlaneZero planeIdealLine) j).obj
      ((conormalFunctor completedPlaneZero planeIdealLine).obj B)) i = _
    rw [ih, planeConormal_rank]

lemma planeFree_rank (N : ℕ) (i : Fin 3) :
    planeChartRank (coherentFree ExplicitCone.plane (Fin N)) i = N := by
  simpa using CoherentChartRank.chart_free_rank (planeIota i) (Fin N)

lemma planeLayer_rank_le {Q : Coh V} {N : ℕ}
    (q : coherentFree V (Fin N) ⟶ Q) [Epi q] (j : ℕ) (i : Fin 3) :
    planeChartRank (layer completedPlaneZero planeIdealLine j Q) i ≤ N := by
  have h := CoherentChartRank.chart_epi_le (planeIota i)
    (freeTwistedLayerQuotient completedPlaneZero planeIdealLine q j)
  change planeChartRank (layer completedPlaneZero planeIdealLine j Q) i ≤
    planeChartRank ((power (conormalFunctor completedPlaneZero planeIdealLine) j).obj
      (coherentFree ExplicitCone.plane (Fin N))) i at h
  rwa [planeConormalPower_rank, planeFree_rank] at h
end SourceConeMorphism

end

/-! Rank as an additive invariant of the coherent Grothendieck group. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Scheme.Modules
namespace CoherentChartRank
open CoherentGlobal CoherentK0
variable {X : Scheme.{0}} [IsLocallyNoetherian X] {R : CommRingCat.{0}}
  [IsNoetherianRing R] [IsDomain R] (j : Spec R ⟶ X) [IsOpenImmersion j]

omit [IsLocallyNoetherian X] [IsNoetherianRing R] [IsDomain R] in
lemma chart_iso_rank {B G : Coh X} (e : B ≅ G) :
    Module.finrank R (chartSections j B) = Module.finrank R (chartSections j G) :=
  ((moduleSpecΓFunctor (R := R)).mapIso
    ((restrictFunctor j).mapIso ((cohInclusion X).mapIso e))).toLinearEquiv.finrank_eq

def rankHom : CoherentK0.Group (Coh X) →+ ℤ :=
  CoherentK0.lift (fun B => (Module.finrank R (chartSections j B) : ℤ))
    (fun e => congrArg (Nat.cast : ℕ → ℤ) (chart_iso_rank j e))
    (fun {S} hS => by exact_mod_cast chart_add j S hS)

@[simp] lemma rankHom_cls (B : Coh X) :
    rankHom j (cls B) = Module.finrank R (chartSections j B) :=
  by
    unfold rankHom
    apply CoherentK0.lift_cls
    · intro B G e
      exact congrArg (Nat.cast : ℕ → ℤ) (chart_iso_rank j e)
    · intro S hS
      exact_mod_cast chart_add j S hS
end CoherentChartRank

end

/-! Rank is preserved along finite sequences of elementary transformations. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace SourceConeMorphism.ExtensionState
open SourceConeMorphism CoherentGlobal
variable {M : ModuleCat ExplicitCone.completedRing}
  [Module.Finite ExplicitCone.completedRing M]

/-- These are precisely the extensions generated from the double-dual
model by finitely many torsion-free divisor quotients. -/
inductive Reachable : ExtensionState M → Prop
  | initial : Reachable (initial (M := M))
  | transform {B : ExtensionState M} (hB : Reachable B)
      {G : Coh ExplicitCone.projectiveSurface}
      (q : sourceRestriction.obj B.sheaf ⟶ G) [CategoryTheory.Epi q]
      (hG : ∀ U, Module.IsTorsionFree (ExplicitCone.projectiveSurface.sheaf.obj.obj U)
        (G.obj.val.obj U)) : Reachable (B.transform q hG)

lemma Reachable.rank_eq {B : ExtensionState M} (hB : Reachable B) (i : Fin 3) :
    surfaceChartRank (sourceRestriction.obj B.sheaf) i =
      Module.finrank ExplicitCone.completedRing M := by
  induction hB with
  | initial => exact initial_restriction_rank M i
  | @transform B hB G q hepi hG ih =>
    exact (elementaryTransform_rank q B.ambient_tf i).trans ih

lemma Reachable.rank_pos [Nontrivial M]
    (hdepth : SmallCM.localDepth ExplicitCone.completedRing M = 3)
    {B : ExtensionState M} (hB : Reachable B) (i : Fin 3) :
    0 < surfaceChartRank (sourceRestriction.obj B.sheaf) i := by
  rw [hB.rank_eq i]
  exact (ExplicitCone.module_properties_from_depth_three M hdepth).2.1
end SourceConeMorphism.ExtensionState

end

/-! The free rank over the compatible source parameters equals the normalization
degree times the exceptional rank along each elementary-transform sequence. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace SourceConeMorphism
open KummerSourceModel
local instance : IsDomain A := NoZeroDivisors.to_isDomain _

def sourceParameterDegree : ℕ :=
  letI : Algebra A ExplicitCone.completedRing :=
    ExplicitCone.projectiveCompletedParameterHom.toRingHom.toAlgebra
  Module.finrank A ExplicitCone.completedRing

lemma sourceParameterDegree_pos : 0 < sourceParameterDegree := by
  let : Algebra A ExplicitCone.completedRing :=
    ExplicitCone.projectiveCompletedParameterHom.toRingHom.toAlgebra
  let : FaithfulSMul A ExplicitCone.completedRing :=
    (faithfulSMul_iff_algebraMap_injective A ExplicitCone.completedRing).mpr
      ExplicitCone.projectiveCompletedParameterHom_injective
  let : Module.Finite A ExplicitCone.completedRing :=
    ExplicitCone.projectiveCompletedParameterHom_finite
  change 0 < Module.finrank A ExplicitCone.completedRing
  exact Module.finrank_pos

lemma parameterModule_rank (M : ModuleCat.{0} ExplicitCone.completedRing)
    [Module.Finite ExplicitCone.completedRing M] :
    Module.finrank A (parameterModule M) =
      sourceParameterDegree * Module.finrank ExplicitCone.completedRing M := by
  let : Algebra A ExplicitCone.completedRing :=
    ExplicitCone.projectiveCompletedParameterHom.toRingHom.toAlgebra
  let : FaithfulSMul A ExplicitCone.completedRing :=
    (faithfulSMul_iff_algebraMap_injective A ExplicitCone.completedRing).mpr
      ExplicitCone.projectiveCompletedParameterHom_injective
  let : Module.Finite A ExplicitCone.completedRing :=
    ExplicitCone.projectiveCompletedParameterHom_finite
  let := Module.restrictScalars A ExplicitCone.completedRing M
  let : IsScalarTower A ExplicitCone.completedRing M :=
    IsScalarTower.restrictScalars A ExplicitCone.completedRing M
  have hx := (DomainModuleRank.tower_rank (A := A) (R := ExplicitCone.completedRing)
    (M := M)).symm
  exact hx

variable (M : ModuleCat.{0} ExplicitCone.completedRing)
  [Module.Finite ExplicitCone.completedRing M] [Nontrivial M]
  (hdepth : SmallCM.localDepth ExplicitCone.completedRing M = 3)

lemma sourceFreeRank_eq : sourceFreeRank M hdepth = Module.finrank A (parameterModule M) := by
  let := parameterModule_free M hdepth
  exact (Module.finrank_eq_card_basis (Module.Free.chooseBasis A (parameterModule M))).symm

lemma sourceFreeRank_rank : sourceFreeRank M hdepth =
    sourceParameterDegree * Module.finrank ExplicitCone.completedRing M := by
  rw [sourceFreeRank_eq, parameterModule_rank]

lemma sourceFreeRank_reached_rank {B : ExtensionState M} (hB : ExtensionState.Reachable B)
    (i : Fin 3) : sourceFreeRank M hdepth =
      sourceParameterDegree * surfaceChartRank (sourceRestriction.obj B.sheaf) i := by
  rw [hB.rank_eq, sourceFreeRank_rank]
end SourceConeMorphism

end

end OAI
