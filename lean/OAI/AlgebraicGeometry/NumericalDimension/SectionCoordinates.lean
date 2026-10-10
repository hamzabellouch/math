import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.CurveCoordinates

namespace OAI

/-! Section Coordinates. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

lemma homogeneous_eval₂_scale {I R B : Type*} [CommSemiring R] [CommSemiring B]
    (c : R →+* B) (v : I → B) (a : B) {p : MvPolynomial I R} {n : ℕ}
    (hp : p.IsHomogeneous n) :
    p.eval₂ c (fun i => a * v i) = a^n * p.eval₂ c v := by
  classical
  simp only [MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hp.degree_eq_sum_deg_support hd]
  simp only [mul_pow, Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum]
  ring

section AwayEval
variable {A B : Type*} [CommRing A] [CommRing B]
variable {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

def homogeneousAwayEval (e : A →+* B) (t : A) (ht : IsUnit (e t)) :
    HomogeneousLocalization.Away 𝒜 t →+* B :=
  (Localization.awayLift e t ht).comp (algebraMap _ (Localization.Away t))

lemma homogeneousAwayEval_mk_mul (e : A →+* B) (t : A) (ht : IsUnit (e t))
    {d : ℕ} (hd : t ∈ 𝒜 d) (n : ℕ) (p : A) (hp : p ∈ 𝒜 (n • d)) :
    homogeneousAwayEval 𝒜 e t ht (HomogeneousLocalization.Away.mk 𝒜 hd n p hp) *
      (e t)^n = e p := by
  let l := Localization.awayLift e t ht
  have hEq :
      (HomogeneousLocalization.Away.mk 𝒜 hd n p hp).val *
        algebraMap A (Localization.Away t) (t^n) =
      algebraMap A (Localization.Away t) p := by
    simp only [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec (M := Submonoid.powers t) (Localization.Away t) p ⟨t^n,⟨n,rfl⟩⟩
  have he := congrArg l hEq
  simpa [homogeneousAwayEval,l, Localization.awayLift, map_mul, map_pow,
    IsLocalization.Away.lift_eq] using he

lemma homogeneousAwayEval_postcomp {C : Type*} [CommRing C]
    (e : A →+* B) (h : B →+* C) (t : A) (ht : IsUnit (e t))
    {d : ℕ} (hd : t ∈ 𝒜 d) :
    h.comp (homogeneousAwayEval 𝒜 e t ht) =
      homogeneousAwayEval 𝒜 (h.comp e) t (ht.map h) := by
  ext z
  obtain ⟨n,p,hp,rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hd z
  apply ((ht.map h).pow n).mul_right_cancel
  have he := congrArg h (homogeneousAwayEval_mk_mul 𝒜 e t ht hd n p hp)
  have hf := homogeneousAwayEval_mk_mul 𝒜 (h.comp e) t (ht.map h) hd n p hp
  simpa only [RingHom.comp_apply, map_mul, map_pow] using he.trans hf.symm

lemma homogeneousAwayEval_awayMap (e : A →+* B) {t u : A}
    {d k : ℕ} (htd : t ∈ 𝒜 d) (huk : u ∈ 𝒜 k)
    (ht : IsUnit (e t)) (hu : IsUnit (e u)) :
    (homogeneousAwayEval 𝒜 e (t*u) (by simpa using ht.mul hu)).comp
      (HomogeneousLocalization.awayMap 𝒜 huk rfl) =
      homogeneousAwayEval 𝒜 e t ht := by
  ext z
  obtain ⟨n,p,hp,rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 htd z
  apply ((ht.mul hu).pow n).mul_right_cancel
  simp only [RingHom.comp_apply, HomogeneousLocalization.awayMap_mk,
    ← map_mul]
  rw [homogeneousAwayEval_mk_mul, map_mul, map_pow]
  rw [map_mul, mul_pow, ← mul_assoc, homogeneousAwayEval_mk_mul]

lemma homogeneousAwayEval_fromZero (e : A →+* B) (t : A) (ht : IsUnit (e t)) :
    (homogeneousAwayEval 𝒜 e t ht).comp
      (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers t)) =
      e.comp (algebraMap (𝒜 0) A) := by
  ext a
  change (Localization.awayLift e t ht) (algebraMap A (Localization.Away t) a.1) = _
  exact IsLocalization.Away.lift_eq t ht a.1

lemma homogeneousAwayEval_awayMap' (e : A →+* B) {t u x : A}
    {d k : ℕ} (htd : t ∈ 𝒜 d) (huk : u ∈ 𝒜 k)
    (ht : IsUnit (e t)) (hu : IsUnit (e u)) (hx : x = t*u) :
    (homogeneousAwayEval 𝒜 e x (by simpa [hx] using ht.mul hu)).comp
      (HomogeneousLocalization.awayMap 𝒜 huk hx) =
      homogeneousAwayEval 𝒜 e t ht := by
  subst x
  exact homogeneousAwayEval_awayMap 𝒜 e htd huk ht hu

end AwayEval
section FieldCoordinates
variable {I R K : Type*} [CommRing R] [Field K]

lemma homogeneousAwayEval_scale (c : R →+* K) (v : I → K) (a : K) (ha : a ≠ 0)
    (i : I) (hi : v i ≠ 0) :
    homogeneousAwayEval (MvPolynomial.homogeneousSubmodule I R)
      (MvPolynomial.eval₂Hom c (fun j => a*v j)) (MvPolynomial.X i)
      (by simpa using isUnit_iff_ne_zero.mpr (mul_ne_zero ha hi)) =
    homogeneousAwayEval (MvPolynomial.homogeneousSubmodule I R)
      (MvPolynomial.eval₂Hom c v) (MvPolynomial.X i)
      (by simpa using isUnit_iff_ne_zero.mpr hi) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule I R
  have hd : MvPolynomial.X i ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X R i
  ext z
  obtain ⟨n,p,hp,rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hd z
  have hp' : p.IsHomogeneous n := by simpa [𝒜, MvPolynomial.mem_homogeneousSubmodule] using hp
  apply mul_right_cancel₀ (pow_ne_zero n (mul_ne_zero ha hi))
  have hL := homogeneousAwayEval_mk_mul 𝒜
    (MvPolynomial.eval₂Hom c (fun j => a*v j)) _
    (by simpa using isUnit_iff_ne_zero.mpr (mul_ne_zero ha hi)) hd n p hp
  have hR := homogeneousAwayEval_mk_mul 𝒜
    (MvPolynomial.eval₂Hom c v) _ (by simpa using isUnit_iff_ne_zero.mpr hi) hd n p hp
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at hL hR
  rw [hL, homogeneous_eval₂_scale c v a hp', mul_pow]
  rw [show (homogeneousAwayEval 𝒜 (MvPolynomial.eval₂Hom c v) (MvPolynomial.X i) _)
      (HomogeneousLocalization.Away.mk 𝒜 hd n p hp) * (a^n * v i^n) =
      a^n * ((homogeneousAwayEval 𝒜 (MvPolynomial.eval₂Hom c v) (MvPolynomial.X i) _)
      (HomogeneousLocalization.Away.mk 𝒜 hd n p hp) * v i^n) by ring, hR]

end FieldCoordinates

section ChartMorphism
universe u v
variable {A : Type u} [CommRing A] {σ : Type v}
variable [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {B : Type u} [CommRing B]

lemma homogeneous_chart_morphism_eq (e : A →+* B) {t u : A}
    {d k : ℕ} (htd : t ∈ 𝒜 d) (huk : u ∈ 𝒜 k) (hd : 0 < d) (hk : 0 < k)
    (ht : IsUnit (e t)) (hu : IsUnit (e u)) :
    Spec.map (CommRingCat.ofHom (homogeneousAwayEval 𝒜 e t ht)) ≫
      Proj.awayι 𝒜 t htd hd =
    Spec.map (CommRingCat.ofHom (homogeneousAwayEval 𝒜 e u hu)) ≫
      Proj.awayι 𝒜 u huk hk := by
  let hxu : IsUnit (e (t*u)) := by simpa using ht.mul hu
  let F := Spec.map (CommRingCat.ofHom (homogeneousAwayEval 𝒜 e (t*u) hxu))
  calc
    _ = F ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜 huk rfl)) ≫
        Proj.awayι 𝒜 t htd hd := by
      rw [← Spec.map_comp_assoc]
      congr 2
      apply CommRingCat.hom_ext
      exact (homogeneousAwayEval_awayMap 𝒜 e htd huk ht hu).symm
    _ = F ≫ Proj.awayι 𝒜 (t*u) (SetLike.mul_mem_graded htd huk) (by omega) := by
      rw [Proj.SpecMap_awayMap_awayι]
    _ = F ≫ Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜 htd (mul_comm _ _))) ≫
        Proj.awayι 𝒜 u huk hk := by
      rw [Proj.SpecMap_awayMap_awayι]
      congr! 2; omega
    _ = _ := by
      rw [← Spec.map_comp_assoc]
      congr 2
      apply CommRingCat.hom_ext
      exact homogeneousAwayEval_awayMap' 𝒜 e huk htd hu ht (mul_comm _ _)

end ChartMorphism

section DivisorCoordinates
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [StalkwiseNormal X] [CompactSpace X]

omit [StalkwiseNormal X] in
lemma generated_finite_section_cover (D : WeilDivisor X)
    (hgen : ∀ x : X, IsGeneratedAt D x) :
    ∃ N : ℕ, ∃ s : Fin (N+1) → X.functionField,
      (∀ i, s i ≠ 0 ∧ IsDivisorSection D (s i)) ∧
      (∀ x : X, ∃ i, x ∈ sectionNonvanishing D (s i)) := by
  classical
  choose s hs hsec hx using hgen
  obtain ⟨V,hV⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (sectionNonvanishing D (s x) : Set X))
    (fun x => (sectionNonvanishing D (s x)).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x,hx x⟩)
  let e : Fin (V.card+1) ≃ Option V :=
    (Fintype.equivFinOfCardEq (by simp)).symm
  let point : Option V → X := fun o => o.elim (genericPoint X) Subtype.val
  refine ⟨V.card,fun i => s (point (e i)),fun i => ⟨hs _,hsec _⟩,?_⟩
  intro x
  obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hV (Set.mem_univ x))
  exact ⟨e.symm (some ⟨y,hy⟩),by simpa [point] using hxy⟩

lemma cartier_section_basicOpen {D : WeilDivisor X} {U : X.Opens} [Nonempty U]
    {g s : X.functionField} (hg : g ≠ 0) (hs : s ≠ 0)
    (hDg : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord g p.1)
    (a : Γ(X,U)) (ha : X.germToFunctionField U a = s*g) :
    X.basicOpen a = U ⊓ sectionNonvanishing D s := by
  ext x
  constructor
  · intro hxa
    have hxU := X.basicOpen_le a hxa
    refine ⟨hxU,section_nonvanishing_of_local_unit hs hg hDg hxU
      (X.presheaf.germ U x hxU a) ((X.mem_basicOpen a x hxU).mp hxa) ?_⟩
    exact (X.algebraMap_germ_eq_germToFunctionField hxU a).trans ha
  · rintro ⟨hxU,hxs⟩
    obtain ⟨b,hb,heb⟩ := section_unit_stalk hs hg hDg hxU hxs
    have he : X.presheaf.germ U x hxU a = b := by
      apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
      exact (X.algebraMap_germ_eq_germToFunctionField hxU a).trans (ha.trans heb.symm)
    exact (X.mem_basicOpen a x hxU).mpr (he ▸ hb)

end DivisorCoordinates

structure DivisorProjectiveChart (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] {I : Type}
    (D : WeilDivisor X) (s : I → X.functionField) where
  domain : X.Opens
  generic_mem : genericPoint X ∈ domain
  equation : X.functionField
  equation_ne_zero : equation ≠ 0
  equation_order : ∀ p : PrimeDivisor X, p.1 ∈ domain → D p = X.ord equation p.1
  coordinate : I → Γ(X,domain)
  coordinate_value : ∀ i, X.presheaf.germ domain (genericPoint X) generic_mem (coordinate i) =
    s i * equation
  unit_index : I
  coordinate_unit : IsUnit (coordinate unit_index)

section LocalChartExistence
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [StalkwiseNormal X] [CompactSpace X]
variable {I : Type} {D : WeilDivisor X} {s : I → X.functionField}

lemma exists_divisorProjectiveChart (hD : IsCartierDivisor D)
    (hs : ∀ i, s i ≠ 0 ∧ IsDivisorSection D (s i)) (x : X)
    (hx : ∃ i, x ∈ sectionNonvanishing D (s i)) :
    ∃ C : DivisorProjectiveChart X D s, x ∈ C.domain := by
  classical
  obtain ⟨i,hix⟩ := hx
  obtain ⟨U,hU,hxU,g,hg,hDg⟩ := hD x
  let : Nonempty U := ⟨⟨x,hxU⟩⟩
  have hvals (j : I) : ∃ a : Γ(X,U), X.germToFunctionField U a = s j*g :=
    (cartier_local_section_iff hU hg hDg (s j)).mp
      ((hs j).2.imp id (fun h p _ => h p))
  choose a ha using hvals
  let V := X.basicOpen (a i)
  have heV : V = U ⊓ sectionNonvanishing D (s i) :=
    cartier_section_basicOpen hg (hs i).1 hDg (a i) (ha i)
  have hxV : x ∈ V := heV ▸ ⟨hxU,hix⟩
  let : Nonempty V := ⟨⟨x,hxV⟩⟩
  let r : Γ(X,U) ⟶ Γ(X,V) := X.presheaf.map (homOfLE (X.basicOpen_le (a i))).op
  refine ⟨⟨V,((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr
    ⟨x,Set.mem_univ x,hxV⟩,g,hg,fun p hp => hDg p (X.basicOpen_le (a i) hp),
    fun j => r (a j),?_,i,X.toRingedSpace.isUnit_res_basicOpen (a i)⟩,hxV⟩
  intro j
  exact (germToFunctionField_restrict (homOfLE (X.basicOpen_le (a i))) (a j)).trans (ha j)

end LocalChartExistence

section OpenScalars
variable {X : Scheme} [IsIntegral X]

lemma openScalar_generic (sX : X ⟶ Spec (.of ℂ)) (U : X.Opens)
    (hU : genericPoint X ∈ U) :
    (X.presheaf.germ U (genericPoint X) hU).hom.comp (schemeOpenScalar sX U) =
      schemeFieldScalar (.of ℂ) sX := by
  ext a
  simp only [schemeOpenScalar, schemeFieldScalar, Scheme.Hom.appLE,
    Scheme.Hom.appTop, RingHom.comp_apply, CommRingCat.hom_comp,
    TopCat.Presheaf.germ_res_apply]
  rfl

omit [IsIntegral X] in
lemma openScalar_toSpec (sX : X ⟶ Spec (.of ℂ)) (U : X.Opens) :
    U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (schemeOpenScalar sX U)) = U.ι ≫ sX := by
  have he : CommRingCat.ofHom (schemeOpenScalar sX U) =
      (Scheme.ΓSpecIso (.of ℂ)).inv ≫ sX.appTop ≫
        X.presheaf.map (homOfLE le_top).op := rfl
  rw [he, Spec.map_comp, Spec.map_comp]
  simp only [Category.assoc]
  rw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

end OpenScalars

namespace DivisorProjectiveChart
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {N : ℕ} {D : WeilDivisor X} {s : Fin (N+1) → X.functionField}
    (C : DivisorProjectiveChart X D s)

def normalized (i : Fin (N+1)) : Γ(X,C.domain) :=
  ↑C.coordinate_unit.unit⁻¹ * C.coordinate i

lemma normalized_index : C.normalized C.unit_index = 1 := by
  unfold normalized
  simpa only [C.coordinate_unit.unit_spec] using Units.inv_mul C.coordinate_unit.unit

def toMorphism (sX : X ⟶ Spec (.of ℂ)) : C.domain.toScheme ⟶ complexProjectiveSpace N :=
  C.domain.toSpecΓ ≫ projectiveAffineMap (schemeOpenScalar sX C.domain)
    C.normalized C.unit_index C.normalized_index

lemma toMorphism_over (sX : X ⟶ Spec (.of ℂ)) :
    C.toMorphism sX ≫ complexProjectiveSpaceMap N = C.domain.ι ≫ sX := by
  rw [toMorphism,Category.assoc,projectiveAffineMap_over,openScalar_toSpec]

lemma generic_normalized (hs : ∀ i, s i ≠ 0) (j : Fin (N+1)) :
    X.presheaf.germ C.domain (genericPoint X) C.generic_mem (C.normalized j) =
      (s C.unit_index)⁻¹ * s j := by
  have hu := C.coordinate_unit.unit_spec
  have he := congrArg (fun a => X.presheaf.germ C.domain (genericPoint X) C.generic_mem a) hu
  rw [C.coordinate_value] at he
  have hinv : X.presheaf.germ C.domain (genericPoint X) C.generic_mem
      (↑C.coordinate_unit.unit⁻¹) = (s C.unit_index * C.equation)⁻¹ := by
    rw [← he]
    exact map_units_inv _ _
  rw [normalized,map_mul,C.coordinate_value,hinv,mul_inv_rev]
  field_simp [hs C.unit_index,C.equation_ne_zero]

lemma toMorphism_generic (sX : X ⟶ Spec (.of ℂ)) (hs : ∀ i, s i ≠ 0) :
    C.domain.fromSpecStalkOfMem (genericPoint X) C.generic_mem ≫ C.toMorphism sX =
      projectiveFieldMap (schemeFieldScalar (.of ℂ) sX) s C.unit_index (hs _) := by
  rw [toMorphism,← Category.assoc,Scheme.Opens.fromSpecStalkOfMem_toSpecΓ]
  change Spec.map (CommRingCat.ofHom (X.presheaf.germ C.domain (genericPoint X) C.generic_mem).hom) ≫ _ = _
  rw [projectiveAffineMap_naturality]
  simp_rw [openScalar_generic,C.generic_normalized hs]
  rw [← projectiveFieldMap_eq_affine,projectiveFieldMap_scaling]
  exact inv_ne_zero (hs _)
lemma toMorphism_preimage [StalkwiseNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) (hs : ∀ i, s i ≠ 0) (i : Fin (N+1)) :
    C.toMorphism sX ⁻¹ᵁ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i) =
      C.domain.ι ⁻¹ᵁ sectionNonvanishing D (s i) := by
  let : Nonempty C.domain := ⟨⟨genericPoint X,C.generic_mem⟩⟩
  trans C.domain.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (C.normalized i)
  · exact congrArg (fun U => C.domain.toSpecΓ ⁻¹ᵁ U)
      (projectiveAffineMap_preimage (schemeOpenScalar sX C.domain)
        C.normalized C.unit_index C.normalized_index i)
  rw [Scheme.Opens.toSpecΓ_preimage_basicOpen,normalized,Scheme.basicOpen_mul,
    Scheme.basicOpen_of_isUnit X (Units.isUnit _)]
  have hval : X.germToFunctionField C.domain (C.coordinate i) = s i*C.equation :=
    C.coordinate_value i
  rw [cartier_section_basicOpen C.equation_ne_zero (hs i) C.equation_order _ hval]
  ext x
  change (x.1 ∈ C.domain ∧ x.1 ∈ C.domain ∧ x.1 ∈ sectionNonvanishing D (s i)) ↔ _
  simp only [x.2,true_and]
  rfl

def toPartialMap (sX : X ⟶ Spec (.of ℂ)) : X.PartialMap (complexProjectiveSpace N) where
  domain := C.domain
  dense_domain := by
    rw [dense_iff_closure_eq]
    apply top_unique
    change Set.univ ⊆ _
    rw [← genericPoint_spec X]
    exact closure_mono (Set.singleton_subset_iff.mpr C.generic_mem)
  hom := C.toMorphism sX

lemma toPartialMap_generic (sX : X ⟶ Spec (.of ℂ)) (hs : ∀ i, s i ≠ 0) :
    (C.toPartialMap sX).fromFunctionField =
      projectiveFieldMap (schemeFieldScalar (.of ℂ) sX) s C.unit_index (hs _) :=
  C.toMorphism_generic sX hs

lemma toRationalMap_eq (sX : X ⟶ Spec (.of ℂ)) (hs : ∀ i, s i ≠ 0)
    (C' : DivisorProjectiveChart X D s) :
    (C.toPartialMap sX).toRationalMap = (C'.toPartialMap sX).toRationalMap := by
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  simp only [Scheme.RationalMap.fromFunctionField_toRationalMap,
    toPartialMap_generic _ _ hs]
  exact projectiveFieldMap_independent _ s _ _ _ _

end DivisorProjectiveChart

lemma covering_partialMaps_extend {X Y : Scheme} [IsIntegral X] [Y.IsSeparated]
    {I : Type*} [Nonempty I] (P : I → X.PartialMap Y)
    (hcov : ∀ x : X, ∃ i, x ∈ (P i).domain)
    (heq : ∀ i j, (P i).toRationalMap = (P j).toRationalMap) :
    ∃ f : X ⟶ Y, ∀ i, (P i).domain.ι ≫ f = (P i).hom := by
  classical
  let i₀ : I := Classical.choice inferInstance
  let r := (P i₀).toRationalMap
  have hdom : r.domain = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i,hi⟩ := hcov x
    exact Scheme.RationalMap.mem_domain.mpr ⟨P i,hi,heq i i₀⟩
  let e : r.domain.toScheme ≅ X := X.isoOfEq hdom ≪≫ X.topIso
  have he : e.hom = r.domain.ι := by
    exact X.isoOfEq_hom_ι hdom
  let f := e.inv ≫ r.toPartialMap.hom
  refine ⟨f,?_⟩
  intro i
  have hle : (P i).domain ≤ r.domain := by
    rw [hdom]; exact le_top
  have hlocal : X.homOfLE hle ≫ r.toPartialMap.hom = (P i).hom := by
    have aux (t : X.RationalMap Y) (ht : (P i).toRationalMap = t)
        (hle : (P i).domain ≤ t.domain) :
        X.homOfLE hle ≫ t.toPartialMap.hom = (P i).hom := by
      subst t
      exact (P i).toPartialMap_toRationalMap_restrict
    exact aux r (heq i i₀) hle
  have hleft : (P i).domain.ι ≫ e.inv = X.homOfLE hle := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc,e.inv_hom_id,Category.comp_id,he,Scheme.homOfLE_ι]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g : (P i).domain.toScheme ⟶ r.domain.toScheme =>
      g ≫ r.toPartialMap.hom) hleft).trans hlocal)
theorem generated_cartier_defines_projective_morphism
    (X : ComplexProjectiveVariety) [StalkwiseNormal X.scheme]
    (D : WeilDivisor X.scheme) (hD : IsCartierDivisor D)
    (hgen : ∀ x : X.scheme, IsGeneratedAt D x) :
    ∃ N : ℕ, ∃ s : Fin (N+1) → X.scheme.functionField,
      (∀ i, s i ≠ 0 ∧ IsDivisorSection D (s i)) ∧
      (∀ x : X.scheme, ∃ i, x ∈ sectionNonvanishing D (s i)) ∧
      ∃ f : X.scheme ⟶ complexProjectiveSpace N,
        f ≫ complexProjectiveSpaceMap N = X.structureMap ∧
        ∀ i, f ⁻¹ᵁ ProjectiveSpectrum.basicOpen
          (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X i) =
          sectionNonvanishing D (s i) := by
  classical
  obtain ⟨N,s,hs,hcov⟩ := generated_finite_section_cover D hgen
  let : (complexProjectiveSpace N).IsSeparated := by
    have := complexProjectiveSpace_isProper N
    constructor
    rw [← Limits.terminal.comp_from (complexProjectiveSpaceMap N)]
    infer_instance
  choose C hC using fun x => exists_divisorProjectiveChart hD hs x (hcov x)
  obtain ⟨f,hf⟩ := covering_partialMaps_extend
    (fun x => (C x).toPartialMap X.structureMap)
    (fun x => ⟨x,hC x⟩) (fun x y => (C x).toRationalMap_eq X.structureMap
      (fun i => (hs i).1) (C y))
  refine ⟨N,s,hs,hcov,f,?_,?_⟩
  · let x := genericPoint X.scheme
    have := Opens.isDominant_ι (X := X.scheme) (U := (C x).domain)
      ((C x).toPartialMap X.structureMap).dense_domain
    apply ext_of_isDominant (C x).domain.ι
    rw [← Category.assoc]
    exact (congrArg (fun g => g ≫ complexProjectiveSpaceMap N) (hf x)).trans
      ((C x).toMorphism_over X.structureMap)
  · intro i
    ext x
    have h := congrArg (fun g : (C x).domain.toScheme ⟶ complexProjectiveSpace N =>
        g ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
          (MvPolynomial.X i)) (hf x)
    change (((C x).domain.ι ≫ f) ⁻¹ᵁ _) = (C x).toMorphism X.structureMap ⁻¹ᵁ _ at h
    erw [Scheme.Hom.comp_preimage,(C x).toMorphism_preimage X.structureMap
      (fun i => (hs i).1)] at h
    exact (congrArg (fun U : (C x).domain.toScheme.Opens => (⟨x,hC x⟩ : (C x).domain) ∈ U) h).to_iff

end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits

namespace NumericalDimensionOne
noncomputable section
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [StalkwiseNormal X] [CompactSpace X]
variable {I : Type} {D : WeilDivisor X} {s : I → X.functionField}
lemma exists_affine_divisorProjectiveChart (hD : IsCartierDivisor D)
    (hs : ∀ i, s i ≠ 0 ∧ IsDivisorSection D (s i)) (x : X)
    (hx : ∃ i, x ∈ sectionNonvanishing D (s i)) :
    ∃ C : DivisorProjectiveChart X D s, x ∈ C.domain ∧ IsAffineOpen C.domain := by
  classical
  obtain ⟨i,hix⟩ := hx
  obtain ⟨U,hU,hxU,g,hg,hDg⟩ := hD x
  let : Nonempty U := ⟨⟨x,hxU⟩⟩
  have hvals (j : I) : ∃ a : Γ(X,U), X.germToFunctionField U a = s j*g :=
    (cartier_local_section_iff hU hg hDg (s j)).mp
      ((hs j).2.imp id (fun h p _ => h p))
  choose a ha using hvals
  let V := X.basicOpen (a i)
  have heV : V = U ⊓ sectionNonvanishing D (s i) :=
    cartier_section_basicOpen hg (hs i).1 hDg (a i) (ha i)
  have hxV : x ∈ V := heV ▸ ⟨hxU,hix⟩
  let : Nonempty V := ⟨⟨x,hxV⟩⟩
  let r : Γ(X,U) ⟶ Γ(X,V) := X.presheaf.map (homOfLE (X.basicOpen_le (a i))).op
  refine ⟨⟨V,((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr
    ⟨x,Set.mem_univ x,hxV⟩,g,hg,fun p hp => hDg p (X.basicOpen_le (a i) hp),
    fun j => r (a j),?_,i,X.toRingedSpace.isUnit_res_basicOpen (a i)⟩,hxV,hU.basicOpen (a i)⟩
  intro j
  exact (germToFunctionField_restrict (homOfLE (X.basicOpen_le (a i))) (a j)).trans (ha j)

end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits

namespace NumericalDimensionOne
noncomputable section
lemma opens_topIso_inv_restrict {X : Scheme} {U V : X.Opens} (h : U ≤ V) (a : Γ(X,V)) :
    (X.homOfLE h).appTop (V.topIso.inv a) =
      U.topIso.inv (X.presheaf.map (homOfLE h).op a) := by
  simp only [Scheme.homOfLE_appTop,Scheme.Opens.topIso_inv]
  change (X.presheaf.map _ ≫ X.presheaf.map _) a =
    (X.presheaf.map _ ≫ X.presheaf.map _) a
  erw [← Functor.map_comp,← Functor.map_comp]
  rfl

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {N : ℕ} {D : WeilDivisor X} {s : Fin (N+1) → X.functionField}
lemma divisorProjectiveChart_normalized_transition
    (C C' : DivisorProjectiveChart X D s) (hs : ∀ i, s i ≠ 0) :
    ∃ e : Γ(pullback C.domain.ι C'.domain.ι,⊤)ˣ, ∀ j,
      (pullback.fst C.domain.ι C'.domain.ι).appTop (C.domain.topIso.inv (C.normalized j)) =
        e * (pullback.snd C.domain.ι C'.domain.ι).appTop
          (C'.domain.topIso.inv (C'.normalized j)) := by
  let U := C.domain ⊓ C'.domain
  have hU : genericPoint X ∈ U := ⟨C.generic_mem,C'.generic_mem⟩
  let : Nonempty U := ⟨⟨genericPoint X,hU⟩⟩
  let : Nonempty C.domain := ⟨⟨genericPoint X,C.generic_mem⟩⟩
  let : Nonempty C'.domain := ⟨⟨genericPoint X,C'.generic_mem⟩⟩
  let a := X.presheaf.map (homOfLE (show U ≤ C.domain from inf_le_left)).op
  let b := X.presheaf.map (homOfLE (show U ≤ C'.domain from inf_le_right)).op
  have ha (j) : X.germToFunctionField U (a (C.normalized j)) =
      (s C.unit_index)⁻¹ * s j := by
    rw [germToFunctionField_restrict]
    exact C.generic_normalized hs j
  have hb (j) : X.germToFunctionField U (b (C'.normalized j)) =
      (s C'.unit_index)⁻¹ * s j := by
    rw [germToFunctionField_restrict]
    exact C'.generic_normalized hs j
  have hab : a (C.normalized C'.unit_index) * b (C'.normalized C.unit_index) = 1 := by
    apply X.germToFunctionField_injective U
    rw [map_mul,map_one,ha,hb]
    field_simp [hs C.unit_index,hs C'.unit_index]
  let e : Γ(X,U)ˣ := ⟨a (C.normalized C'.unit_index),b (C'.normalized C.unit_index),hab,
    (mul_comm _ _).trans hab⟩
  have hc (j) : a (C.normalized j) = e * b (C'.normalized j) := by
    apply X.germToFunctionField_injective U
    change X.germToFunctionField U (a (C.normalized j)) =
      X.germToFunctionField U (a (C.normalized C'.unit_index) * b (C'.normalized j))
    rw [map_mul,ha,ha,hb]
    field_simp [hs C'.unit_index]
  let i := (isPullback_opens_inf C.domain C'.domain).isoPullback
  let φ := i.inv.appTop.hom.comp U.topIso.inv.hom
  refine ⟨Units.map φ e,fun j => ?_⟩
  have H := congrArg φ (hc j)
  simp only [map_mul,Units.coe_map] at H ⊢
  have hleft (z : Γ(X,C.domain)) :
      φ (a z) = (pullback.fst C.domain.ι C'.domain.ι).appTop (C.domain.topIso.inv z) := by
    dsimp [φ]
    rw [← opens_topIso_inv_restrict,← CommRingCat.comp_apply,← Scheme.Hom.comp_appTop]
    rw [(isPullback_opens_inf C.domain C'.domain).isoPullback_inv_fst]
  have hright (z : Γ(X,C'.domain)) :
      φ (b z) = (pullback.snd C.domain.ι C'.domain.ι).appTop (C'.domain.topIso.inv z) := by
    dsimp [φ]
    rw [← opens_topIso_inv_restrict,← CommRingCat.comp_apply,← Scheme.Hom.comp_appTop]
    rw [(isPullback_opens_inf C.domain C'.domain).isoPullback_inv_snd]
  rwa [hleft,hright] at H
end
end NumericalDimensionOne

end OAI
