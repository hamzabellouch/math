import OAI.AlgebraicGeometry.SurfaceCones.KummerCMRestriction

namespace OAI

noncomputable section
open Polynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SectionCompletion
variable {k K σ : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]
variable (w : σ → K) (hw : ∀ i, w i ∈ T 1) (i : σ)

abbrev polynomialChart := Away (MvPolynomial.homogeneousSubmodule σ k) (MvPolynomial.X i)

instance polynomialChartScalarAlgebra : Algebra k (polynomialChart (k := k) i) :=
  ((algebraMap (MvPolynomial.homogeneousSubmodule σ k 0) (polynomialChart (k := k) i)).comp
    (algebraMap k (MvPolynomial.homogeneousSubmodule σ k 0))).toAlgebra

def polynomialChartDehom : MvPolynomial σ k →ₐ[k] polynomialChart (k := k) i :=
  MvPolynomial.aeval (fun j => Away.mk (MvPolynomial.homogeneousSubmodule σ k)
    (MvPolynomial.isHomogeneous_X k i) 1 (MvPolynomial.X j)
      (by simpa using MvPolynomial.isHomogeneous_X k j))

@[simp] lemma linearGradedMap_X (j : σ) :
    linearGradedMap T w hw (MvPolynomial.X j) = linearSection T (w j) (hw j) := by
  simp [linearGradedMap, GradedPolynomialMap.lift, linearPolynomialMap, linearSection]

def linearChartMap : polynomialChart (k := k) i →+* homogeneousChart T (w i) (hw i) :=
  HomogeneousLocalization.map (linearGradedMap T w hw).toGradedRingHom (by
    rintro _ ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    rw [map_pow]
    change linearSection T (w i) (hw i) ^ n = linearGradedMap T w hw (MvPolynomial.X i) ^ n
    rw [linearGradedMap_X])

lemma linearChartMap_scalar (a : k) :
    linearChartMap T w hw i (algebraMap k (polynomialChart (k := k) i) a) =
      (@algebraMap k (homogeneousChart T (w i) (hw i)) _ _
        (homogeneousChartScalarAlgebra T (w i) (hw i))) a := by
  let x : MvPolynomial.homogeneousSubmodule σ k 0 := algebraMap k _ a
  let y : homogeneous T 0 := algebraMap k _ a
  have hs : algebraMap k (polynomialChart (k := k) i) a =
      HomogeneousLocalization.mk ⟨0, x, 1, Submonoid.one_mem _⟩ := by
    apply HomogeneousLocalization.val_injective
    rfl
  have ht : (@algebraMap k (homogeneousChart T (w i) (hw i)) _ _
        (homogeneousChartScalarAlgebra T (w i) (hw i))) a =
      HomogeneousLocalization.mk ⟨0, y, 1, Submonoid.one_mem _⟩ := by
    apply HomogeneousLocalization.val_injective
    rfl
  rw [hs, ht]
  apply HomogeneousLocalization.val_injective
  simp only [linearChartMap, HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
  congr 1
  · exact (linearGradedMap T w hw).commutes a
  · apply Subtype.ext
    exact map_one (linearGradedMap T w hw)

/-- The actual ring map on an affine chart, including its scalar structure. -/
def linearChartAlgMap : polynomialChart (k := k) i →ₐ[k] homogeneousChart T (w i) (hw i) :=
  { linearChartMap T w hw i with commutes' := linearChartMap_scalar T w hw i }

lemma linearChartMap_dehom (hn : w i ≠ 0) :
    (linearChartAlgMap T w hw i).comp (polynomialChartDehom (k := k) i) =
      (dehomogenize T (w i) (hw i) hn).comp (linearPolynomialMap T w hw) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, polynomialChartDehom, MvPolynomial.aeval_X]
  change linearChartMap T w hw i (Away.mk _ _ 1 (MvPolynomial.X j) _) =
    dehomogenize T (w i) (hw i) hn (linearGradedMap T w hw (MvPolynomial.X j))
  rw [linearGradedMap_X]
  rw [dehomogenize_linearSection]
  apply HomogeneousLocalization.val_injective
  simp only [linearChartMap, Away.mk, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk]
  congr 1
  · exact linearGradedMap_X T w hw j
  · apply Subtype.ext
    simp only [pow_one]
    exact linearGradedMap_X T w hw i

/-- Every actual projective chart map of the finite normalized linear cone
is FINITE, proved through surjective dehomogenization of the section ring. -/
theorem linearChartMap_finite (hn : w i ≠ 0)
    (hfin : (linearPolynomialMap T w hw).Finite) : (linearChartMap T w hw i).Finite := by
  have hf := (AlgHom.Finite.of_surjective (dehomogenize T (w i) (hw i) hn)
    (dehomogenize_surjective T (w i) (hw i) hn)).comp hfin
  rw [← linearChartMap_dehom T w hw i hn] at hf
  exact AlgHom.Finite.of_comp_finite hf
end SectionCompletion

end


noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SectionCompletion
variable {k K σ : Type} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]
variable (w : σ → K) (hw : ∀ i, w i ∈ T 1)

omit [IsAlgClosed k] in
lemma polynomial_irrelevant_le :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule σ k)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ k)) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn p hp
  change p.IsHomogeneous n at hp
  change p ∈ MvPolynomial.idealOfVars σ k
  rw [← pow_one (MvPolynomial.idealOfVars σ k), MvPolynomial.mem_pow_idealOfVars_iff]
  intro x hx
  have he : x.degree = n := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hx) (hp.coeff_eq_zero h)
  rw [he]
  exact hn

omit [IsAlgClosed k] in
lemma awayMap_finite (i : σ) (hn : w i ≠ 0)
    (hfin : (linearPolynomialMap T w hw).Finite) :
    (HomogeneousLocalization.Away.map (linearGradedMap T w hw).toGradedRingHom
      (MvPolynomial.X i)).Finite := by
  have h := linearChartMap_finite T w hw i hn hfin
  have he : (linearGradedMap T w hw).toGradedRingHom (MvPolynomial.X i) =
      linearSection T (w i) (hw i) := linearGradedMap_X T w hw i
  unfold linearChartMap at h
  unfold HomogeneousLocalization.Away.map
  have haux (q : polynomials T) (hq : q = linearSection T (w i) (hw i))
      (hc : Submonoid.powers (MvPolynomial.X i) ≤
        (Submonoid.powers q).comap (linearGradedMap T w hw).toGradedRingHom) :
      (HomogeneousLocalization.map (linearGradedMap T w hw).toGradedRingHom hc).Finite := by
    subst q
    exact h
  exact haux _ he _

/-- Finiteness of the actual projective scheme map, from the finite
normalized homogeneous cone and chartwise surjective dehomogenization. -/
theorem linearProjectiveMap_finite (hn : ∀ i, w i ≠ 0)
    (hfin : (linearPolynomialMap T w hw).Finite) :
    IsFinite (linearProjectiveMap T w hw hfin) := by
  let C := Proj.affineOpenCoverOfIrrelevantLESpan
    (MvPolynomial.homogeneousSubmodule σ k) MvPolynomial.X
    (fun i => MvPolynomial.isHomogeneous_X k i) (fun _ => zero_lt_one)
    polynomial_irrelevant_le
  let : IsZariskiLocalAtTarget @AlgebraicGeometry.IsFinite.{0} :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop
  apply IsZariskiLocalAtTarget.of_openCover (P := @AlgebraicGeometry.IsFinite.{0})
    (f := linearProjectiveMap T w hw hfin) C.openCover
  change ∀ i : σ, IsFinite (pullback.snd (linearProjectiveMap T w hw hfin)
    (Proj.awayι (MvPolynomial.homogeneousSubmodule σ k) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X k i) zero_lt_one))
  intro i
  let v := Proj.awayι (MvPolynomial.homogeneousSubmodule σ k) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X k i) zero_lt_one
  let g := Spec.map (CommRingCat.ofHom
    (HomogeneousLocalization.Away.map (linearGradedMap T w hw).toGradedRingHom
      (MvPolynomial.X i)))
  let j := Proj.awayι (homogeneous T) (linearGradedMap T w hw (MvPolynomial.X i))
    ((linearGradedMap T w hw).map_mem (MvPolynomial.isHomogeneous_X k i)) zero_lt_one
  have hg : IsFinite g := (IsFinite.SpecMap_iff _).mpr (awayMap_finite T w hw i (hn i) hfin)
  let := hg
  have : IsOpenImmersion v := by dsimp only [v, Proj.awayι]; infer_instance
  have : IsOpenImmersion j := by dsimp only [j]; infer_instance
  have hp : IsPullback j g (linearProjectiveMap T w hw hfin) v := by
    apply IsPullback.flip
    apply IsOpenImmersion.isPullback g j v (linearProjectiveMap T w hw hfin)
    · exact linearProjectiveMap_chart T w hw hfin i
    · change linearProjectiveMap T w hw hfin ⁻¹ᵁ v.opensRange = j.opensRange
      dsimp only [v, j]
      erw [Proj.opensRange_awayι, Proj.opensRange_awayι]
      rfl
  change IsFinite (pullback.snd (linearProjectiveMap T w hw hfin) v)
  have hi : IsFinite (hp.isoPullback.inv ≫ g) := inferInstance
  exact hp.isoPullback_inv_snd ▸ hi
end SectionCompletion
namespace ExplicitCone
lemma projectiveParameter_injective :
    Function.Injective (SectionCompletion.linearPolynomialMap pieces projectiveParameter
      projectiveParameter_mem) :=
  exists_finite_linear_projective_parameters.choose_spec.choose_spec.2

lemma projectiveParameter_ne_zero (i : Fin 3) : projectiveParameter i ≠ 0 := by
  intro h
  have he : SectionCompletion.linearPolynomialMap pieces projectiveParameter
      projectiveParameter_mem (MvPolynomial.X i) = 0 := by
    apply Subtype.ext
    simp [SectionCompletion.linearPolynomialMap, h]
  exact MvPolynomial.X_ne_zero i (projectiveParameter_injective (he.trans (map_zero _).symm))

/-- The morphism from the normalized Kummer section-cone Proj to the projective plane is finite. -/
theorem projectiveNormalization_finite : IsFinite projectiveNormalization :=
  SectionCompletion.linearProjectiveMap_finite pieces projectiveParameter
    projectiveParameter_mem projectiveParameter_ne_zero projectiveParameter_finite
end ExplicitCone

end


noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace ExplicitCone

lemma projectiveParameter_section_ne_zero (i : Fin 3) :
    SectionCompletion.linearSection pieces (projectiveParameter i) (projectiveParameter_mem i) ≠ 0 := by
  intro h
  apply projectiveParameter_ne_zero i
  have he := congrArg (fun p : Polynomial L => p.coeff 1) (congrArg Subtype.val h)
  simpa [SectionCompletion.linearSection] using he

/-- Integrality is proved for the actual normalized section-cone Proj. This
still makes no unsupported claim of all-chart smoothness. -/
instance projectiveSurface_integral : IsIntegral projectiveSurface :=
  ProjDomain.integral (SectionCompletion.homogeneous pieces)
    (SectionCompletion.linearSection pieces (projectiveParameter 0) (projectiveParameter_mem 0))
    one_ne_zero (SectionCompletion.linearSection_homogeneous _ _ _)
    (projectiveParameter_section_ne_zero 0)

/-- The genuine projective normalization covers P², including every closed
point. Its generic-point dominance follows from the injective
homogeneous normalization, and finite closedness supplies surjectivity. -/
theorem projectiveNormalization_surjective : Function.Surjective projectiveNormalization := by
  let p : projectiveSurface := ProjDomain.genericPoint (SectionCompletion.homogeneous pieces)
    (SectionCompletion.linearSection pieces (projectiveParameter 0) (projectiveParameter_mem 0))
    one_ne_zero (SectionCompletion.linearSection_homogeneous _ _ _)
    (projectiveParameter_section_ne_zero 0)
  let q : plane := ProjDomain.genericPoint (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)
    (MvPolynomial.X 0) one_ne_zero (MvPolynomial.isHomogeneous_X ℂ 0) (MvPolynomial.X_ne_zero 0)
  have he : projectiveNormalization p = q := by
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.ext
    apply Ideal.ext
    intro a
    change SectionCompletion.linearPolynomialMap pieces projectiveParameter
      projectiveParameter_mem a = 0 ↔ a = 0
    exact map_eq_zero_iff _ projectiveParameter_injective
  let : IsFinite projectiveNormalization := projectiveNormalization_finite
  have hc : IsClosed (Set.range projectiveNormalization) :=
    projectiveNormalization.isClosedMap.isClosed_range
  intro y
  have hq : q ⤳ y := ProjDomain.genericPoint_specializes _ _ _ _ _ y
  exact hq.mem_closed hc ⟨p, he⟩
end ExplicitCone

end


noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
namespace KummerSourceModel
abbrev S := MvPolynomial (Fin 3) ℂ
abbrev A := MvPowerSeries (Fin 3) ℂ
abbrev m : Ideal S := Ideal.span (Set.range (MvPolynomial.X : Fin 3 → S))
abbrev B := reesAlgebra m
instance : Algebra ℂ B := ((reesAlgebra m).restrictScalars ℂ).algebra
instance : IsScalarTower ℂ S B := IsScalarTower.of_algebraMap_eq' rfl
abbrev grades (n : ℕ) : Submodule ℂ B := (ReesProj.homogeneous m n).restrictScalars ℂ
abbrev V₀ : Scheme := Proj grades

def projectionGradedMap : MvPolynomial.homogeneousSubmodule (Fin 3) ℂ →ₐᵍ[ℂ] grades :=
  GradedPolynomialMap.lift grades (MvPolynomial.aeval (ReesProj.chartSection (MvPolynomial.X : Fin 3 → S)))
    (by intro i; simpa only [MvPolynomial.aeval_X, grades, Submodule.restrictScalars_mem, ReesProj.chartSection] using
      ReesProj.linearSection_homogeneous m (MvPolynomial.X i) (Ideal.subset_span (Set.mem_range_self i)))

lemma sourceSections_cover :
    ⨆ i : Fin 3, Proj.basicOpen grades (projectionGradedMap (MvPolynomial.X i)) = ⊤ := by
  have he (i : Fin 3) : projectionGradedMap (MvPolynomial.X i) =
      ReesProj.chartSection (MvPolynomial.X : Fin 3 → S) i := MvPolynomial.aeval_X _ i
  simp_rw [he]
  apply Proj.iSup_basicOpen_eq_top'
  · intro i
    exact ⟨1, ReesProj.linearSection_homogeneous m (MvPolynomial.X i)
      (Ideal.subset_span (Set.mem_range_self i))⟩
  · exact ReesProj.chartSections_generate_over_zero (MvPolynomial.X : Fin 3 → S)


lemma irrelevant_le_radical :
    (HomogeneousIdeal.irrelevant grades).toIdeal ≤
      ((HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)).toIdeal.map
        projectionGradedMap.toAlgHom.toRingHom).radical := by
  rw [Ideal.radical_eq_sInf]
  apply le_sInf
  intro Q hQ
  let P := Q.homogeneousCore grades
  have hp : P.toIdeal.IsPrime := hQ.2.homogeneousCore
  have hmap : (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)).toIdeal.map
      projectionGradedMap.toAlgHom.toRingHom ≤ P.toIdeal := by
    have hc : ((HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)).map
        projectionGradedMap.toGradedRingHom).toIdeal ≤ Q := hQ.1
    exact ((HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)).map
      projectionGradedMap.toGradedRingHom).isHomogeneous.toIdeal_homogeneousCore_eq_self.symm.trans_le
        (Ideal.homogeneousCore_mono grades hc)
  apply le_trans ?_ (Q.toIdeal_homogeneousCore_le grades)
  change HomogeneousIdeal.irrelevant grades ≤ P
  by_contra hnot
  let p : ProjectiveSpectrum grades := ⟨P, hp, hnot⟩
  have hc : p ∈ (⨆ i : Fin 3, Proj.basicOpen grades (projectionGradedMap (MvPolynomial.X i))) := by
    rw [sourceSections_cover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
  apply hi
  apply hmap
  apply Ideal.mem_map_of_mem
  change MvPolynomial.X i ∈ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)
  rw [HomogeneousIdeal.mem_irrelevant_iff]
  exact DirectSum.decompose_of_mem_ne (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)
    (MvPolynomial.isHomogeneous_X ℂ i) one_ne_zero

/-- The projective direction of the literal blowup of affine 3-space at
its origin; no line-bundle or regularity identification is assumed. -/
def direction : V₀ ⟶ ExplicitCone.plane :=
  Proj.radicalMap projectionGradedMap.toGradedRingHom irrelevant_le_radical

def zeroSpecIso : Spec (.of (grades 0)) ≅ Spec (.of S) :=
  Scheme.Spec.mapIso (ReesProj.zeroEquiv m).toRingEquiv.toCommRingCatIso.op

def blowdown : V₀ ⟶ Spec (.of S) := Proj.toSpecZero grades ≫ zeroSpecIso.hom
instance : IsProper blowdown := by
  let : Algebra.FiniteType (grades 0) B := ReesProj.finiteType_over_degreeZero m
  let : IsProper (Proj.toSpecZero grades) := inferInstance
  change IsProper (Proj.toSpecZero grades ≫ zeroSpecIso.hom)
  infer_instance

def completionToPolynomial : Spec (.of A) ⟶ Spec (.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S A))

/-- The literal uncompleted fiber-product model, not a postulated total space. -/
abbrev W₀ : Scheme := pullback ExplicitCone.projectiveNormalization direction

def g₀ : W₀ ⟶ V₀ := pullback.snd _ _

theorem g₀_finite : IsFinite g₀ := by
  let := ExplicitCone.projectiveNormalization_finite
  dsimp [g₀]
  infer_instance

/-- The source's completed polynomial blowup V, as literal base change. -/
abbrev V : Scheme := pullback blowdown completionToPolynomial

def completedBlowdown : V ⟶ Spec (.of A) := pullback.snd _ _
instance : IsProper completedBlowdown := by dsimp [completedBlowdown]; infer_instance

def completedDirection : V ⟶ ExplicitCone.plane := pullback.fst _ _ ≫ direction

/-- The completed model is the fiber product of the normalized section-cone Proj with the completed polynomial blowup over the projective plane. -/
abbrev W : Scheme := pullback ExplicitCone.projectiveNormalization completedDirection

def g : W ⟶ V := pullback.snd _ _

theorem g_finite : IsFinite g := by
  let := ExplicitCone.projectiveNormalization_finite
  dsimp [g]
  infer_instance

instance : IsProper (g ≫ completedBlowdown) := by
  let := g_finite
  infer_instance

theorem g_surjective : Surjective g := by
  let : Surjective ExplicitCone.projectiveNormalization :=
    ⟨ExplicitCone.projectiveNormalization_surjective⟩
  dsimp [g]
  infer_instance

/-- The completed fiber-product model is proper. -/
theorem W_proper : IsProper (g ≫ completedBlowdown) := inferInstance

end KummerSourceModel


end


/-! Required local cone-evaluation maps for the manuscript, lines 243–268. These maps
use the actual homogeneous Proj chart, not a postulated coordinate ring. -/
noncomputable section
open Polynomial
namespace SectionCompletion
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]
variable (c : K) (hc : c ∈ T 1) (hn : c ≠ 0)

/-- Homogeneous rescaling of the literal section polynomial. -/
def scaledPolynomialMap : polynomials T →ₐ[k] Polynomial K :=
  ((Polynomial.aeval (C c⁻¹ * X)).restrictScalars k).comp (polynomials T).val

lemma coeff_scaledPolynomialMap (p : polynomials T) (n : ℕ) :
    (scaledPolynomialMap T c p).coeff n = p.val.coeff n / c ^ n := by
  change (p.val.comp (C c⁻¹ * X)).coeff n = _
  rw [comp_C_mul_X_coeff]
  simp only [div_eq_mul_inv, inv_pow]

lemma scaledPolynomialMap_mem_range (p : polynomials T) :
    scaledPolynomialMap T c p ∈
      (Polynomial.mapAlgHom (homogeneousChartAlgMap T c hc hn)).range := by
  change scaledPolynomialMap T c p ∈
    (Polynomial.mapRingHom (homogeneousChartMap T c hc hn)).rangeS
  rw [Polynomial.mem_map_rangeS]
  intro n
  rw [coeff_scaledPolynomialMap]
  exact scaledCoefficient_mem_range T c hc hn n _ (p.property n)

/-- The line-bundle-chart evaluation of the section ring, rescaling each
pure section by c^degree and retaining the fiber parameter X. -/
def chartEvaluation : polynomials T →ₐ[k] Polynomial (homogeneousChart T c hc) :=
  (AlgEquiv.ofInjective (Polynomial.mapAlgHom (homogeneousChartAlgMap T c hc hn))
    (Polynomial.map_injective _ (homogeneousChartMap_injective T c hc hn))).symm.toAlgHom.comp
      ((scaledPolynomialMap T c).codRestrict _ (scaledPolynomialMap_mem_range T c hc hn))

lemma map_chartEvaluation (p : polynomials T) :
    Polynomial.map (homogeneousChartMap T c hc hn) (chartEvaluation T c hc hn p) =
      scaledPolynomialMap T c p := by
  exact congrArg Subtype.val ((AlgEquiv.ofInjective
    (Polynomial.mapAlgHom (homogeneousChartAlgMap T c hc hn))
    (Polynomial.map_injective _ (homogeneousChartMap_injective T c hc hn))).apply_symm_apply
      ⟨scaledPolynomialMap T c p, scaledPolynomialMap_mem_range T c hc hn p⟩)

lemma coeff_chartEvaluation (p : polynomials T) (n : ℕ) :
    homogeneousChartMap T c hc hn ((chartEvaluation T c hc hn p).coeff n) =
      p.val.coeff n / c ^ n := by
  rw [← coeff_map, map_chartEvaluation, coeff_scaledPolynomialMap]

lemma chartEvaluation_injective : Function.Injective (chartEvaluation T c hc hn) := by
  intro p q he
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  have hh := congrArg (fun f => homogeneousChartMap T c hc hn (Polynomial.coeff f n)) he
  simp only [coeff_chartEvaluation] at hh
  exact (div_left_inj' (pow_ne_zero n hn)).mp hh

lemma chartEvaluation_homogeneous (n : ℕ) (p : polynomials T)
    (hp : p ∈ homogeneous T n) :
    chartEvaluation T c hc hn p =
      monomial n (dehomogenize T c hc hn p) := by
  apply Polynomial.map_injective _ (homogeneousChartMap_injective T c hc hn)
  rw [map_chartEvaluation, map_monomial, homogeneousChartMap_dehomogenize]
  apply Polynomial.ext
  intro m
  rw [coeff_scaledPolynomialMap]
  rw [show evaluateInv T c p = p.val.coeff n / c ^ n from
    evaluateInv_homogeneous T c n p (by simpa using hp)]
  rw [homogeneous_eq_monomial T hp]
  by_cases hm : n = m
  · subst m; simp
  · simp [coeff_monomial, hm]

lemma chartEvaluation_parameter :
    chartEvaluation T c hc hn (linearSection T c hc) = X := by
  apply Polynomial.map_injective _ (homogeneousChartMap_injective T c hc hn)
  rw [map_chartEvaluation, Polynomial.map_X]
  ext n
  rw [coeff_scaledPolynomialMap]
  change (monomial 1 c).coeff n / c ^ n = X.coeff n
  by_cases h : n = 1
  · subst n; simp [hn]
  · simp [coeff_monomial, coeff_X, Ne.symm h]

/-- Every degree-one section is its direction ratio times the fiber parameter. -/
lemma chartEvaluation_linearSection (a : K) (ha : a ∈ T 1) :
    chartEvaluation T c hc hn (linearSection T a ha) =
      C (dehomogenize T c hc hn (linearSection T a ha)) * X := by
  rw [chartEvaluation_homogeneous T c hc hn 1 _ (linearSection_homogeneous T a ha)]
  exact C_mul_X_eq_monomial.symm

end SectionCompletion

end


/-! The graded localization relation needed to evaluate cone sections in an
actual blowup chart. This holds for the literal homogeneous localization. -/
noncomputable section
namespace HomogeneousLocalization
open scoped _root_.HomogeneousLocalization
variable {R σ : Type*} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

lemma ratio_mul_fromZero (f : R) (hf : f ∈ 𝒜 1) (g : R) (hg : g ∈ 𝒜 1)
    (c d : 𝒜 0) (h : g * (c : R) = f * (d : R)) :
    _root_.HomogeneousLocalization.Away.mk 𝒜 hf 1 g (by simpa using hg) *
      algebraMap (𝒜 0) (_root_.HomogeneousLocalization.Away 𝒜 f) c = algebraMap (𝒜 0) (_root_.HomogeneousLocalization.Away 𝒜 f) d := by
  apply _root_.HomogeneousLocalization.val_injective
  rw [_root_.HomogeneousLocalization.val_mul, _root_.HomogeneousLocalization.Away.val_mk]
  change Localization.mk g ⟨f ^ 1, _⟩ * Localization.mk (c : R) ⟨((1 : 𝒜 0) : R), _⟩ =
    Localization.mk (d : R) ⟨((1 : 𝒜 0) : R), _⟩
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simpa only [Submonoid.coe_mul, pow_one, SetLike.GradeZero.coe_one, one_mul, mul_one] using h

end HomogeneousLocalization


/-! Affine-chart cone evaluation on the literal projective pullback used by
the manuscript, lines 245–268. No equality with the ordinary section-ideal blowup. -/
open Polynomial _root_.HomogeneousLocalization TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
abbrev S := KummerSourceModel.S
abbrev origin := KummerSourceModel.m
abbrev Rees : Type := KummerSourceModel.B
abbrev grades (n : ℕ) : Submodule ℂ Rees := KummerSourceModel.grades n
abbrev projectionGradedMap : MvPolynomial.homogeneousSubmodule (Fin 3) ℂ →ₐᵍ[ℂ] grades :=
  KummerSourceModel.projectionGradedMap

abbrev sourceSection (i : Fin 3) : Rees := projectionGradedMap (MvPolynomial.X i)
lemma sourceSection_eq (i : Fin 3) : sourceSection i = ReesProj.chartSection MvPolynomial.X i :=
  MvPolynomial.aeval_X _ i
lemma sourceSection_homogeneous (i : Fin 3) : sourceSection i ∈ grades 1 :=
  projectionGradedMap.map_mem (MvPolynomial.isHomogeneous_X ℂ i)

abbrev chart (i : Fin 3) := HomogeneousLocalization.Away (grades ) (sourceSection i)
abbrev planeChart (i : Fin 3) := SectionCompletion.polynomialChart (k := ℂ) i

def directionMap (i : Fin 3) : planeChart i →+* chart i :=
  HomogeneousLocalization.Away.map projectionGradedMap.toGradedRingHom (MvPolynomial.X i)

/-- Blowdown's exact degree-zero ring map on this Rees chart. -/
def baseToZero : S →+* grades 0 :=
  { (ReesProj.zeroEquiv (origin )).toRingHom with }

def baseMap (i : Fin 3) : S →+* chart i :=
 (algebraMap (grades 0) (chart i)).comp baseToZero

lemma directionMap_ratio (i j : Fin 3) :
    directionMap i
     (SectionCompletion.polynomialChartDehom i (MvPolynomial.X j)) =
    Away.mk grades (sourceSection_homogeneous i) 1 (sourceSection  j)
     (by simpa using sourceSection_homogeneous  j) := by
  simp only [SectionCompletion.polynomialChartDehom, MvPolynomial.aeval_X,
    directionMap]
  exact Away.map_mk projectionGradedMap.toGradedRingHom (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X ℂ i) 1 (MvPolynomial.X j)
    (by simpa using MvPolynomial.isHomogeneous_X ℂ j)

lemma directionMap_scalar (i : Fin 3) (a : ℂ) :
    directionMap i (algebraMap ℂ (planeChart i) a) =
      baseMap i (MvPolynomial.C a) := by
  let x : MvPolynomial.homogeneousSubmodule (Fin 3) ℂ 0 := algebraMap ℂ _ a
  have hs : algebraMap ℂ (planeChart i) a =
      HomogeneousLocalization.mk ⟨0, x, 1, Submonoid.one_mem _⟩ := by
    apply HomogeneousLocalization.val_injective
    rfl
  let y : grades 0 := baseToZero (MvPolynomial.C a)
  have ht : baseMap i (MvPolynomial.C a) =
      HomogeneousLocalization.mk ⟨0, y, 1, Submonoid.one_mem _⟩ := by
    rfl
  rw [hs, ht]
  apply HomogeneousLocalization.val_injective
  change Localization.mk (projectionGradedMap x.val) ⟨projectionGradedMap 1, _⟩ =
    Localization.mk y.val ⟨1, _⟩
  congr 1
  · exact projectionGradedMap.commutes a
  · apply Subtype.ext
    exact map_one projectionGradedMap

lemma baseMap_mk (i : Fin 3) (a : S) : baseMap i a =
    HomogeneousLocalization.mk ⟨0, baseToZero a, 1, Submonoid.one_mem _⟩ := rfl

lemma baseToZero_coe (a : S) : (baseToZero a).val = algebraMap S Rees a := rfl

lemma sourceSection_cross (i j : Fin 3) :
    sourceSection j * algebraMap S Rees (MvPolynomial.X i) =
      sourceSection i * algebraMap S Rees (MvPolynomial.X j) := by
  rw [sourceSection_eq, sourceSection_eq]
  apply Subtype.ext
  change monomial 1 (MvPolynomial.X j) * C (MvPolynomial.X i) =
    monomial 1 (MvPolynomial.X i) * C (MvPolynomial.X j)
  simp only [mul_comm, C_mul_monomial]

lemma ratio_relation (i j : Fin 3) :
    directionMap i
     (SectionCompletion.polynomialChartDehom i (MvPolynomial.X j)) *
        baseMap i (MvPolynomial.X i) = baseMap i (MvPolynomial.X j) := by
  rw [directionMap_ratio]
  exact HomogeneousLocalization.ratio_mul_fromZero grades (sourceSection i)
    (sourceSection_homogeneous i) (sourceSection j) (sourceSection_homogeneous j)
    (baseToZero (MvPolynomial.X i)) (baseToZero (MvPolynomial.X j))
    (by simpa only [baseToZero_coe] using sourceSection_cross i j)

end SourcePullbackChart

end


/-! A homogeneous substitution identity needed to identify the literal
Rees-Proj source chart with its line-bundle chart. -/
noncomputable section
open MvPolynomial
namespace MvPolynomial
open scoped _root_.MvPolynomial
variable {k F σ : Type*} [Field k] [Field F] [Algebra k F]

lemma homogeneous_aeval_div (a : σ → F) (c : F) (n : ℕ)
    (p : MvPolynomial σ k) (hp : p.IsHomogeneous n) :
    _root_.MvPolynomial.aeval (fun i => a i / c) p = _root_.MvPolynomial.aeval a p / c ^ n := by
  classical
  induction hp using _root_.MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add, hp, hq, add_div]
  | monomial d r hd =>
    simp only [_root_.MvPolynomial.aeval_monomial, Finsupp.prod]
    simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
    have he : ∑ i ∈ d.support, d i = n := by
      simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using hd
    rw [he]
    exact (mul_div_assoc _ _ _).symm

end MvPolynomial

end


/-! The actual projective-plane chart as its ring of homogeneous fractions.
This prepares the line-bundle presentation for the source's Rees chart. -/
noncomputable section
open _root_.HomogeneousLocalization _root_.MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
abbrev K := FractionRing S

def coordinate (i : Fin 3) : K := algebraMap S K (MvPolynomial.X i)
lemma coordinate_ne_zero (i : Fin 3) : coordinate i ≠ 0 := by
  exact (IsFractionRing.injective S K).ne (MvPolynomial.X_ne_zero i) |>.trans_eq (map_zero _)

def planeField (i : Fin 3) : planeChart i →+* K :=
  (Localization.awayLift (algebraMap S K) (MvPolynomial.X i)
    (isUnit_iff_ne_zero.mpr (coordinate_ne_zero i))).comp
      (algebraMap (planeChart i) (Localization.Away (MvPolynomial.X i)))

lemma planeField_mk (i : Fin 3) (n : ℕ) (a : S)
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℂ (n • 1)) :
    planeField i (Away.mk (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)
      (MvPolynomial.isHomogeneous_X ℂ i) n a ha) =
      algebraMap S K a / coordinate i ^ n := by
  simp only [planeField, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  erw [Away.val_mk]
  rw [Localization.awayLift_mk _ _ _ _ (by exact mul_inv_cancel₀ (coordinate_ne_zero i))]
  simp only [div_eq_mul_inv, inv_pow, coordinate]

lemma planeField_injective (i : Fin 3) : Function.Injective (planeField i) := by
  intro x y h
  apply sub_eq_zero.mp
  have hz : planeField i (x - y) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨n, a, ha, he⟩ := Away.mk_surjective
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ) (MvPolynomial.isHomogeneous_X ℂ i) (x-y)
  rw [← he, planeField_mk] at hz
  have haz : a = 0 := (IsFractionRing.injective S K) (by
    simpa only [map_zero] using (div_eq_zero_iff.mp hz).resolve_right
      (pow_ne_zero n (coordinate_ne_zero i)))
  rw [← he]
  subst a
  apply HomogeneousLocalization.val_injective
  erw [Away.val_mk]
  simp only [HomogeneousLocalization.val_zero]
  exact Localization.mk_zero _

lemma planeField_scalar (i : Fin 3) (a : ℂ) :
    planeField i (algebraMap ℂ (planeChart i) a) = algebraMap ℂ K a := by
  let x : MvPolynomial.homogeneousSubmodule (Fin 3) ℂ 0 := algebraMap ℂ _ a
  have hs : algebraMap ℂ (planeChart i) a =
      Away.mk (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)
        (MvPolynomial.isHomogeneous_X ℂ i) 0 (algebraMap ℂ S a)
        (by simp) := by
    apply HomogeneousLocalization.val_injective
    rfl
  rw [hs]
  erw [planeField_mk]
  simp only [pow_zero, div_one, IsScalarTower.algebraMap_apply ℂ S K]

def planeFieldAlg (i : Fin 3) : planeChart i →ₐ[ℂ] K :=
  { planeField i with commutes' := planeField_scalar i }

lemma planeField_ratio (i j : Fin 3) :
    planeField i (SectionCompletion.polynomialChartDehom i (MvPolynomial.X j)) =
      coordinate j / coordinate i := by
  simp only [SectionCompletion.polynomialChartDehom, MvPolynomial.aeval_X, planeField_mk,
    pow_one, coordinate]

lemma planeField_dehom (i : Fin 3) (a : S) :
    planeField i (SectionCompletion.polynomialChartDehom i a) =
      MvPolynomial.aeval (fun j => coordinate j / coordinate i) a := by
  have hh : (planeFieldAlg i).comp (SectionCompletion.polynomialChartDehom i) =
      MvPolynomial.aeval (fun j => coordinate j / coordinate i) := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X]
    change planeField i (SectionCompletion.polynomialChartDehom i (MvPolynomial.X j)) = _
    exact planeField_ratio i j
  exact congrArg (fun f : S →ₐ[ℂ] K => f a) hh

lemma polynomialChartDehom_surjective (i : Fin 3) :
    Function.Surjective (SectionCompletion.polynomialChartDehom (k := ℂ) i) := by
  intro x
  obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ) (MvPolynomial.isHomogeneous_X ℂ i) x
  refine ⟨a, planeField_injective i ?_⟩
  rw [planeField_dehom, planeField_mk]
  rw [MvPolynomial.homogeneous_aeval_div _ _ n a (by simpa using ha)]
  congr 1
  change (MvPolynomial.aeval (fun j => algebraMap S K (MvPolynomial.X j))) a = _
  have hh : MvPolynomial.aeval (fun j => algebraMap S K (MvPolynomial.X j)) =
      (IsScalarTower.toAlgHom ℂ S K) := by ext; simp
  exact congrArg (fun f : S →ₐ[ℂ] K => f a) hh

lemma planeField_range (i : Fin 3) :
    (planeFieldAlg i).range = Algebra.adjoin ℂ (Set.range fun j => coordinate j / coordinate i) := by
  have hh : (planeFieldAlg i).comp (SectionCompletion.polynomialChartDehom i) =
      MvPolynomial.aeval (fun j => coordinate j / coordinate i) := by
    ext j
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X]
    change planeField i (SectionCompletion.polynomialChartDehom i (MvPolynomial.X j)) = _
    exact planeField_ratio i j
  rw [Algebra.adjoin_range_eq_range_aeval, ← hh]
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    obtain ⟨b,rfl⟩ := polynomialChartDehom_surjective i a
    exact ⟨b,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨SectionCompletion.polynomialChartDehom i a,rfl⟩

end SourcePullbackChart

end


/-! An embedding of the Rees chart into the field of rational functions
of affine three-space. -/
noncomputable section
open _root_.HomogeneousLocalization _root_.MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SourcePullbackChart
local instance reesFieldRing : Ring K := (inferInstance : CommRing K).toRing

lemma sourceSection_literal (i : Fin 3) : sourceSection i =
    ReesProj.linearSection origin (MvPolynomial.X i) (Ideal.subset_span (Set.mem_range_self i)) :=
  sourceSection_eq i

lemma evaluateOne_sourceSection (i : Fin 3) :
    ReesProj.evaluateOne (K := K) origin (sourceSection i) = coordinate i := by
  rw [sourceSection_literal]
  exact ReesProj.evaluateOne_linearSection origin (MvPolynomial.X i)
    (Ideal.subset_span (Set.mem_range_self i))

def reesField (i : Fin 3) : chart i →+* K :=
  (Localization.awayLift (ReesProj.evaluateOne (K := K) origin) (sourceSection i)
    (by rw [evaluateOne_sourceSection]; exact isUnit_iff_ne_zero.mpr (coordinate_ne_zero i))).comp
    (algebraMap (chart i) (Localization.Away (sourceSection i)))

lemma reesField_mk (i : Fin 3) (n : ℕ) (a : Rees) (ha : a ∈ grades (n • 1)) :
    reesField i (Away.mk grades (sourceSection_homogeneous i) n a ha) =
      algebraMap S K (a.val.coeff n) / coordinate i ^ n := by
  simp only [reesField, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk]
  rw [Localization.awayLift_mk _ _ _ _ (by
    rw [evaluateOne_sourceSection]; exact mul_inv_cancel₀ (coordinate_ne_zero i))]
  have he := ReesProj.homogeneous_eq_monomial origin (by simpa using ha : a ∈ ReesProj.homogeneous origin n)
  change a.val.eval₂ (algebraMap S K) 1 * (coordinate i)⁻¹ ^ n = _
  conv_lhs => rw [he]
  simp only [Polynomial.eval₂_monomial, one_pow, mul_one, inv_pow, div_eq_mul_inv]

lemma reesField_injective (i : Fin 3) : Function.Injective (reesField i) := by
  intro x y h
  apply sub_eq_zero.mp
  have hz : reesField i (x-y) = 0 := by
    calc
      reesField i (x-y) = reesField i x - reesField i y := (reesField i).map_sub x y
      _ = 0 := by rw [h, sub_self]
  obtain ⟨n,a,ha,he⟩ := Away.mk_surjective grades (sourceSection_homogeneous i) (x-y)
  rw [← he, reesField_mk] at hz
  have hcoeff : a.val.coeff n = 0 := (IsFractionRing.injective S K) (by
    simpa only [map_zero] using (div_eq_zero_iff.mp hz).resolve_right
      (pow_ne_zero n (coordinate_ne_zero i)))
  have haz : a = 0 := by
    apply Subtype.ext
    rw [ReesProj.homogeneous_eq_monomial origin (by simpa using ha : a ∈ ReesProj.homogeneous origin n),
      hcoeff, map_zero]
    rfl
  rw [← he]
  subst a
  apply HomogeneousLocalization.val_injective
  erw [Away.val_mk]
  simp only [HomogeneousLocalization.val_zero]
  exact Localization.mk_zero _

lemma reesField_base (i : Fin 3) (a : S) :
    reesField i (baseMap i a) = algebraMap S K a := by
  have ha : algebraMap S Rees a ∈ grades (0 • 1) := by
    intro m hm
    change (Polynomial.C a).coeff m = 0
    simp only [smul_eq_mul, zero_mul] at hm
    simp [Polynomial.coeff_C, hm]
  have hs : baseMap i a = Away.mk grades (sourceSection_homogeneous i) 0
      (algebraMap S Rees a) ha := by
    apply HomogeneousLocalization.val_injective
    rfl
  rw [hs, reesField_mk]
  change algebraMap S K ((Polynomial.C a).coeff 0) / coordinate i ^ 0 = _
  simp

lemma reesField_direction (i : Fin 3) (a : planeChart i) :
    reesField i (directionMap i a) = planeField i a := by
  obtain ⟨p,rfl⟩ := polynomialChartDehom_surjective i a
  have hh : ((reesField i).comp (directionMap i)).comp
        (SectionCompletion.polynomialChartDehom i).toRingHom =
      (planeField i).comp (SectionCompletion.polynomialChartDehom i).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change reesField i (directionMap i
        ((SectionCompletion.polynomialChartDehom i) (algebraMap ℂ S c))) =
        planeField i ((SectionCompletion.polynomialChartDehom i) (algebraMap ℂ S c))
      rw [(SectionCompletion.polynomialChartDehom i).commutes c, directionMap_scalar,
        reesField_base]
      rw [planeField_scalar]
      exact IsScalarTower.algebraMap_apply ℂ S K c
    · intro j
      change reesField i (directionMap i
        (SectionCompletion.polynomialChartDehom i (MvPolynomial.X j))) =
        planeField i (SectionCompletion.polynomialChartDehom i (MvPolynomial.X j))
      rw [planeField_ratio]
      apply (eq_div_iff (coordinate_ne_zero i)).mpr
      change _ * algebraMap S K (MvPolynomial.X i) = _
      rw [← reesField_base i (MvPolynomial.X i), ← (reesField i).map_mul,
        ratio_relation, reesField_base]
      rfl
  exact congrArg (fun f : S →+* K => f p) hh

end SourcePullbackChart

end

end OAI
