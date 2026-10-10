import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.OpenSections

namespace OAI

/-! Local Klt Members. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin

namespace NumericalDimensionOne
noncomputable section
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {N : ℕ} {D : WeilDivisor X} {s : Fin (N+1) → X.functionField}

structure DivisorOpenAtlas (U : X.Opens) where
  index : Type
  finite : Fintype index
  chart : index → DivisorProjectiveChart X D s
  affine : ∀ i, IsAffineOpen (chart i).domain
  inside : ∀ i, (chart i).domain ≤ U
  covers : ∀ x : X, x ∈ U → ∃ i, x ∈ (chart i).domain
attribute [instance] DivisorOpenAtlas.finite
namespace DivisorOpenAtlas
variable {U : X.Opens} (A : DivisorOpenAtlas (D := D) (s := s) U)
def cover : U.toScheme.OpenCover where
  I₀ := A.index
  X i := (A.chart i).domain.toScheme
  f i := X.homOfLE (A.inside i)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_,inferInstance⟩
    obtain ⟨i,hi⟩ := A.covers x.1 x.2
    exact ⟨i,⟨⟨x.1,hi⟩,Subtype.ext (by simp)⟩⟩
instance : Fintype A.cover.I₀ := A.finite
instance (i : A.cover.I₀) : IsAffine (A.cover.X i) := A.affine i
def coordinate (i : A.index) (j : Fin (N+1)) : Γ(A.cover.X i,⊤) :=
  (A.chart i).domain.topIso.inv ((A.chart i).normalized j)
lemma cover_comp (i : A.index) : A.cover.f i ≫ U.ι = (A.chart i).domain.ι :=
  X.homOfLE_ι (A.inside i)
end DivisorOpenAtlas

theorem exists_divisorOpenAtlas [StalkwiseNormal X] [CompactSpace X]
    (hD : IsCartierDivisor D) (hs : ∀ i, s i ≠ 0 ∧ IsDivisorSection D (s i))
    (U : X.Opens) (hcov : ∀ x : X, x ∈ U → ∃ i, x ∈ sectionNonvanishing D (s i)) :
    Nonempty (DivisorOpenAtlas (D := D) (s := s) U) := by
  classical
  have : IsNoetherian X := ⟨⟩
  choose C hC hA hU using fun x : U =>
    exists_affine_divisorProjectiveChart_inside hD hs U x.1 x.2 (hcov x.1 x.2)
  obtain ⟨S,hS⟩ := (NoetherianSpace.isCompact (U : Set X)).elim_finite_subcover
    (fun x : U => ((C x).domain : Set X))
    (fun x => (C x).domain.isOpen)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x,hx⟩,hC ⟨x,hx⟩⟩)
  let e := (Fintype.equivFin S).symm
  refine ⟨⟨Fin (Fintype.card S),inferInstance,fun i => C (e i).1,
    fun i => hA (e i).1,fun i => hU (e i).1,?_⟩⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hS hx)
  exact ⟨e.symm ⟨y,hy⟩,by simpa using hxy⟩
theorem DivisorOpenAtlas.exists_nonzero_smooth_member
    [StalkwiseNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of ℂ)) [Smooth sX]
    {U : X.Opens} (A : DivisorOpenAtlas (D := D) (s := s) U)
    (hs : ∀ j, s j ≠ 0) :
    letI := schemeFieldAlgebra (.of ℂ) sX
    ∃ (J : 𝔸(Fin (N+1);X).IdealSheafData)
      (p : Spec (.of ℂ) ⟶ 𝔸(Fin (N+1);Spec (.of ℂ))),
      (∀ i, J.comap (AffineSpace.map _ (A.chart i).domain.ι) =
        Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (A.coordinate i)})) ∧
      p ≫ 𝔸(Fin (N+1);Spec (.of ℂ)) ↘ Spec (.of ℂ) = 𝟙 _ ∧
      Smooth (((J.comap (parameterSection sX p)).comap U.ι).subschemeι ≫ (U.ι ≫ sX)) ∧
      parameterLinearCombination s p ≠ 0 := by
  classical
  let := schemeFieldAlgebra (.of ℂ) sX
  have : IsNoetherian X := ⟨⟩
  have : NoetherianSpace U := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  obtain ⟨J,hJ⟩ := universal_incidence_exists (fun i => (A.chart i).domain.toScheme)
    (fun i => (A.chart i).domain.ι) A.coordinate
    (fun i j => divisorProjectiveChart_normalized_transition (A.chart i) (A.chart j) hs)
  let JU := J.comap (AffineSpace.map (Fin (N+1)) U.ι)
  have hJU (i : A.index) : JU.comap (AffineSpace.map _ (A.cover.f i)) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (A.coordinate i)}) := by
    rw [← Scheme.IdealSheafData.comap_comp,← AffineSpace.map_comp,A.cover_comp]
    exact hJ i
  have : Smooth (JU.subschemeι ≫ 𝔸(Fin (N+1);U) ↘ U) :=
    universal_incidence_smooth_over A.cover A.coordinate
      (fun i => ⟨(A.chart i).unit_index,by
        change (A.chart i).domain.topIso.inv ((A.chart i).normalized (A.chart i).unit_index) = 1
        rw [DivisorProjectiveChart.normalized_index]
        exact map_one _⟩) JU hJU
  obtain ⟨T,hT,hne⟩ := exists_linear_nonvanishing_parameter_open (k := ℂ) s 0 (hs 0)
  have : Uncountable ℂ := Cardinal.aleph0_lt_mk_iff.mp (by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
  obtain ⟨p,hp,hpT,hsm⟩ := exists_very_general_incidence_member (U.ι ≫ sX) JU
    (fun _ : Unit => T) (fun _ => hT)
  refine ⟨J,p,hJ,hp,?_,hne p hp (hpT ())⟩
  have hi : (J.comap (parameterSection sX p)).comap U.ι =
      JU.comap (parameterSection (U.ι ≫ sX) p) := by
    rw [← Scheme.IdealSheafData.comap_comp,parameterSection_naturality,
      Scheme.IdealSheafData.comap_comp]
  rwa [hi]
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin

namespace NumericalDimensionOne
noncomputable section

theorem exists_effective_member_smooth_on_open
    (X : ComplexProjectiveVariety) [StalkwiseNormal X.scheme]
    [Smooth X.structureMap] (D : WeilDivisor X.scheme)
    (hD : IsCartierDivisor D) (U : X.scheme.Opens) (hU : Nonempty U)
    (hgen : ∀ x : X.scheme, x ∈ U → IsGeneratedAt D x) :
    ∃ F : X.scheme.functionField, F ≠ 0 ∧ IsDivisorSection D F ∧
      ∀ x : X.scheme, x ∈ U →
        letI := schemeStalkAlgebra (.of ℂ) X.structureMap x
        ∃ a : CartierStalkEquation (D + principalWeilDivisor F) x,
          Algebra.FormallySmooth ℂ ((X.scheme.presheaf.stalk x) ⧸ Ideal.span {a.regular}) := by
  classical
  let := schemeFieldAlgebra (.of ℂ) X.structureMap
  obtain ⟨N,s,hs,hcov⟩ := generated_finite_section_cover_on_open D U hU hgen
  obtain ⟨A⟩ := exists_divisorOpenAtlas hD hs U hcov
  obtain ⟨J,p,hJ,hp,hsm,hF⟩ := A.exists_nonzero_smooth_member X.structureMap (fun j => (hs j).1)
  let F := parameterLinearCombination s p
  let I := J.comap (parameterSection X.structureMap p)
  have : Smooth ((I.comap U.ι).subschemeι ≫ (U.ι ≫ X.structureMap)) := hsm
  have hsec : IsDivisorSection D F := by
    change F ∈ divisorSectionsOver (.of ℂ) X.structureMap D
    exact (divisorSectionsOver (.of ℂ) X.structureMap D).sum_mem
      (fun j _ => (divisorSectionsOver (.of ℂ) X.structureMap D).smul_mem
        (parameterCoefficient p j) (hs j).2)
  refine ⟨F,hF,hsec,?_⟩
  intro x hxU
  let := schemeStalkAlgebra (.of ℂ) X.structureMap x
  obtain ⟨i,hi⟩ := A.covers x hxU
  let C := A.chart i
  have : IsAffine C.domain := A.affine i
  let a := C.member X.structureMap p
  let b : CartierStalkEquation (D + principalWeilDivisor F) x :=
    ⟨C.domain,hi,F / s C.unit_index,div_ne_zero hF (hs _).1,
      fun q hq => C.member_divisor_order hF (fun j => (hs j).1) q hq,
      X.scheme.presheaf.germ C.domain x hi a,by
        let : Nonempty C.domain := ⟨⟨x,hi⟩⟩
        rw [X.scheme.algebraMap_germ_eq_germToFunctionField hi]
        exact C.member_generic X.structureMap p (fun j => (hs j).1)⟩
  refine ⟨b,?_⟩
  have hl := parameter_member_chart C.domain.ι X.structureMap p J (A.coordinate i) (hJ i)
  change I.comap C.domain.ι = Scheme.IdealSheafData.ofIdealTop
    (Ideal.span {linearMemberSection (C.domain.ι ≫ X.structureMap) p
      (fun j => C.domain.topIso.inv (C.normalized j))}) at hl
  rw [← C.member_topIso X.structureMap p] at hl
  have : IsOpenImmersion (A.cover.f i) :=
    inferInstanceAs (IsOpenImmersion (X.scheme.homOfLE (A.inside i)))
  have hloc := smooth_ideal_open_comap (U.ι ≫ X.structureMap) (A.cover.f i) (I.comap U.ι)
  have hc : A.cover.f i ≫ (U.ι ≫ X.structureMap) = C.domain.ι ≫ X.structureMap := by
    rw [← Category.assoc,A.cover_comp]
    rfl
  rw [← Scheme.IdealSheafData.comap_comp,A.cover_comp,hc] at hloc
  change Smooth ((I.comap C.domain.ι).subschemeι ≫ C.domain.ι ≫ X.structureMap) at hloc
  rw [hl] at hloc
  exact affineOpen_hypersurface_stalk_formallySmooth X.structureMap C.domain a ⟨x,hi⟩
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin

namespace NumericalDimensionOne
noncomputable section

theorem order_smooth_hypersurface_le_jacobian
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
    (p : PrimeDivisor X)
    {k A : Type*} [Field k] [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra k A] [Algebra.FormallySmooth k A]
    [Algebra k (X.presheaf.stalk p.1)] [Algebra A (X.presheaf.stalk p.1)]
    [IsScalarTower k A (X.presheaf.stalk p.1)]
    {n : ℕ} (bA : Module.Basis (Fin n) A Ω[A⁄k])
    (bp : Module.Basis (Fin 1) (X.presheaf.stalk p.1)
      (⋀[X.presheaf.stalk p.1]^n Ω[X.presheaf.stalk p.1⁄k]))
    (g : A) (hg : g ≠ 0)
    [Algebra.FormallySmooth k (A ⧸ Ideal.span {g})]
    (hgX : algebraMap A (X.presheaf.stalk p.1) g ≠ 0)
    (v : ⋀[A]^n Ω[A⁄k]) (c : X.presheaf.stalk p.1)
    (hc : topDifferentialMap k A (X.presheaf.stalk p.1) n v = c • bp 0)
    (hcf : algebraMap (X.presheaf.stalk p.1) X.functionField c ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk p.1) X.functionField
      (algebraMap A (X.presheaf.stalk p.1) g)) p.1 ≤
      X.ord (algebraMap (X.presheaf.stalk p.1) X.functionField c) p.1 + 1 := by
  classical
  have hcpos := (ord_nonnegative_iff_regular p _ hcf).mpr ⟨c,rfl⟩
  by_cases hgu : IsUnit g
  · rw [order_stalk_unit p (hgu.map (algebraMap A (X.presheaf.stalk p.1)))]
    omega
  have hgm : g ∈ IsLocalRing.maximalIdeal A := by
    rwa [IsLocalRing.mem_maximalIdeal,mem_nonunits_iff]
  have hprim := smooth_hypersurface_differential_primitive bA g hg hgm
  let : IsDiscreteValuationRing (X.presheaf.stalk p.1) := dvr_at_prime_divisor p
  obtain ⟨t,ht⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk p.1)
  obtain ⟨e,u,he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hgX ht
  obtain ⟨w,hw⟩ := topDifferentialMap_divisible_of_primitive bA g hprim t (↑u) e he v
  have hcg : c = t^(e-1) * (bp.repr w 0) := by
    have hh := congrArg (fun z => bp.repr z 0) (hc.symm.trans hw)
    simpa only [map_smul,Finsupp.smul_apply,smul_eq_mul,Module.Basis.repr_self, Finsupp.single_eq_same,
      mul_one] using hh
  rw [he,order_stalk_unit_mul_pow p t ht u e]
  exact order_stalk_divisible_pow_lower_bound p t ht e c (bp.repr w 0) hcf hcg

lemma order_smooth_hypersurface_le_jacobian_chart
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]
    (p : PrimeDivisor X)
    {k A U : Type*} [Field k] [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra k A] [Algebra.FormallySmooth k A]
    [CommRing U] [Algebra k U] [Algebra U A] [IsScalarTower k U A]
    [Algebra k (X.presheaf.stalk p.1)] [Algebra A (X.presheaf.stalk p.1)]
    [Algebra U (X.presheaf.stalk p.1)]
    [IsScalarTower k A (X.presheaf.stalk p.1)]
    [IsScalarTower k U (X.presheaf.stalk p.1)]
    [IsScalarTower U A (X.presheaf.stalk p.1)]
    {n : ℕ} (bA : Module.Basis (Fin n) A Ω[A⁄k])
    (bp : Module.Basis (Fin 1) (X.presheaf.stalk p.1)
      (⋀[X.presheaf.stalk p.1]^n Ω[X.presheaf.stalk p.1⁄k]))
    (g : A) (hg : g ≠ 0)
    [Algebra.FormallySmooth k (A ⧸ Ideal.span {g})]
    (hgX : algebraMap A (X.presheaf.stalk p.1) g ≠ 0)
    (v : ⋀[U]^n Ω[U⁄k]) (c : X.presheaf.stalk p.1)
    (hc : topDifferentialMap k U (X.presheaf.stalk p.1) n v = c • bp 0)
    (hcf : algebraMap (X.presheaf.stalk p.1) X.functionField c ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk p.1) X.functionField
      (algebraMap A (X.presheaf.stalk p.1) g)) p.1 ≤
      X.ord (algebraMap (X.presheaf.stalk p.1) X.functionField c) p.1 + 1 := by
  have hh := LinearMap.congr_fun (topDifferentialMap_comp k U A (X.presheaf.stalk p.1) n) v
  simp only [LinearMap.comp_apply,LinearMap.restrictScalars_apply] at hh
  exact order_smooth_hypersurface_le_jacobian p bA bp g hg hgX
    (topDifferentialMap k U A n v) c (hh.trans hc) hcf

lemma cartier_order_le_jacobian_of_chart
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [StalkwiseNormal X] [StalkwiseNormal Y]
    (f : X ⟶ Y) [IsDominant f] (D : WeilDivisor Y)
    (T : WeilDivisor X) (hT : IsCartierPullback f D T) (p : PrimeDivisor X)
    {k U : Type*} [Field k] [CommRing U] [Algebra k U]
    [Algebra k (Y.presheaf.stalk (f p.1))]
    [Algebra.FormallySmooth k (Y.presheaf.stalk (f p.1))]
    [Algebra k (X.presheaf.stalk p.1)]
    [Algebra (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1)]
    [Algebra U (Y.presheaf.stalk (f p.1))] [Algebra U (X.presheaf.stalk p.1)]
    [IsScalarTower k U (Y.presheaf.stalk (f p.1))]
    [IsScalarTower k U (X.presheaf.stalk p.1)]
    [IsScalarTower k (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1)]
    [IsScalarTower U (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1)]
    (hmap : algebraMap (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1) =
      (f.stalkMap p.1).hom)
    {n : ℕ} (bY : Module.Basis (Fin n) (Y.presheaf.stalk (f p.1))
      Ω[Y.presheaf.stalk (f p.1)⁄k])
    (bp : Module.Basis (Fin 1) (X.presheaf.stalk p.1)
      (⋀[X.presheaf.stalk p.1]^n Ω[X.presheaf.stalk p.1⁄k]))
    (g : CartierStalkEquation D (f p.1))
    [Algebra.FormallySmooth k ((Y.presheaf.stalk (f p.1)) ⧸ Ideal.span {g.regular})]
    (v : ⋀[U]^n Ω[U⁄k]) (c : X.presheaf.stalk p.1)
    (hc : topDifferentialMap k U (X.presheaf.stalk p.1) n v = c • bp 0)
    (hcf : algebraMap (X.presheaf.stalk p.1) X.functionField c ≠ 0) :
    T p ≤ X.ord (algebraMap (X.presheaf.stalk p.1) X.functionField c) p.1 + 1 := by
  have hgmap : algebraMap (X.presheaf.stalk p.1) X.functionField
      (algebraMap (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1) g.regular) =
        dominantFunctionFieldMap f g.function := by
    rw [hmap,← g.regular_eq,dominantFunctionFieldMap_algebraMap]
  have hgnz : g.regular ≠ 0 := by
    intro hz
    exact g.nonzero (by rw [← g.regular_eq,hz,map_zero])
  have hgXnz : algebraMap (Y.presheaf.stalk (f p.1)) (X.presheaf.stalk p.1) g.regular ≠ 0 := by
    intro hz
    have hn := (map_ne_zero (dominantFunctionFieldMap f)).mpr g.nonzero
    exact hn (by rw [← hgmap,hz,map_zero])
  have hb := order_smooth_hypersurface_le_jacobian_chart p bY bp g.regular
    hgnz hgXnz v c hc hcf
  have hTord := hT.order_eq_of_equation g.nonzero g.equation p g.mem_openSet
  exact (hTord.trans (congrArg (fun z => X.ord z p.1) hgmap.symm)).le.trans hb

lemma topDifferentialMap_scalar_chart
    {k A B C F : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C] [CommRing F]
    [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k F]
    [Algebra A B] [Algebra A C] [Algebra A F] [Algebra B F] [Algebra C F]
    [IsScalarTower k A B] [IsScalarTower k A C] [IsScalarTower k A F]
    [IsScalarTower k B F] [IsScalarTower k C F]
    [IsScalarTower A B F] [IsScalarTower A C F]
    (n : ℕ) (u : ⋀[A]^n Ω[A⁄k]) (v : ⋀[C]^n Ω[C⁄k])
    (ω : ⋀[B]^n Ω[B⁄k]) (a : B) (c : C)
    (hω : ω = a • topDifferentialMap k A B n u)
    (hc : topDifferentialMap k A C n u = c • v) :
    topDifferentialMap k B F n ω =
      (algebraMap B F a * algebraMap C F c) • topDifferentialMap k C F n v := by
  rw [hω,map_smul,← IsScalarTower.algebraMap_smul F a]
  have h₁ := LinearMap.congr_fun (topDifferentialMap_comp k A B F n) u
  have h₂ := LinearMap.congr_fun (topDifferentialMap_comp k A C F n) u
  simp only [LinearMap.comp_apply,LinearMap.restrictScalars_apply] at h₁ h₂
  rw [h₁,← h₂,hc,map_smul,← IsScalarTower.algebraMap_smul F c,← mul_smul]

theorem smooth_boundary_discrepancy_bound_at
    (X Y : ComplexProjectiveVariety) (n : ℕ)
    (hX : IsSmoothNfold X n) (hY : IsSmoothNfold Y n)
    [StalkwiseNormal Y.scheme]
    (f : X.scheme ⟶ Y.scheme) [IsDominant f]
    (hf : f ≫ Y.structureMap = X.structureMap)
    (ω : rationalTopForms (.of ℂ) Y.structureMap n)
    (DX : WeilDivisor X.scheme) (DY : WeilDivisor Y.scheme)
    (hDX : IsCanonicalDivisorOf (.of ℂ) X.structureMap n
      (rationalTopFormPullback (.of ℂ) X.structureMap Y.structureMap f hf n ω) DX)
    (hDY : IsCanonicalDivisorOf (.of ℂ) Y.structureMap n ω DY)
    (P : WeilDivisor X.scheme) (hP : IsCartierPullback f DY P)
    (D : WeilDivisor Y.scheme)
    (T : WeilDivisor X.scheme) (hT : IsCartierPullback f D T)
    (p : PrimeDivisor X.scheme)
    (hg : letI := schemeStalkAlgebra (.of ℂ) Y.structureMap (f p.1)
      ∃ g : CartierStalkEquation D (f p.1),
        Algebra.FormallySmooth ℂ ((Y.scheme.presheaf.stalk (f p.1)) ⧸ Ideal.span {g.regular})) :
    T p ≤ (DX-P) p + 1 := by
  classical
  let : SmoothOfRelativeDimension n X.structureMap := hX
  let : SmoothOfRelativeDimension n Y.structureMap := hY
  let : StalkwiseNormal X.scheme := smoothNormal X hX
  let : StalkwiseNormal Y.scheme := smoothNormal Y hY
  let := schemeFieldAlgebra (.of ℂ) X.structureMap
  let := schemeFieldAlgebra (.of ℂ) Y.structureMap
  let : Algebra Y.scheme.functionField X.scheme.functionField :=
    (dominantFunctionFieldMap f).toAlgebra
  let : IsScalarTower ℂ Y.scheme.functionField X.scheme.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (dominantFunctionFieldMap_scalar (.of ℂ) X.structureMap Y.structureMap f hf a).symm)
  change T p ≤ DX p - P p + 1
  obtain ⟨U, hU, hpU, hs⟩ := exists_standard_smooth_chart Y.structureMap n (f p.1)
  let : Nonempty U := ⟨⟨f p.1, hpU⟩⟩
  let := schemeOpenAlgebra Y.structureMap U
  let : Algebra.IsStandardSmoothOfRelativeDimension n ℂ Γ(Y.scheme, U) := hs
  let : Algebra.IsStandardSmooth ℂ Γ(Y.scheme, U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let := open_field_scalar_tower Y.structureMap U
  let := functionField_isFractionRing_of_isAffineOpen Y.scheme U hU
  let : Algebra.FormallyEtale Γ(Y.scheme, U) Y.scheme.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors Γ(Y.scheme, U))
  obtain ⟨bU⟩ := nonempty_topDifferential_basis ℂ Γ(Y.scheme, U) n
  let bF := (topDifferential_isBaseChange ℂ Γ(Y.scheme, U) Y.scheme.functionField n).basis bU
  let a := bF.repr ω 0
  have heq : ω = a • topDifferentialMap ℂ Γ(Y.scheme, U) Y.scheme.functionField n (bU 0) := by
    simpa only [bF, IsBaseChange.basis_apply] using basis_singleton_repr bF ω
  have ha : a ≠ 0 := by
    intro h
    exact hDY.1 (by simpa [h] using heq)
  have hDa := canonical_chart_equation Y.structureMap n hDY U hU hs bU a ha heq
  have hPa := hP.order_eq_of_equation ha hDa p hpU
  let := schemeStalkAlgebra (.of ℂ) X.structureMap p.1
  let := stalk_field_scalar_tower (.of ℂ) X.structureMap p.1
  let u : U := ⟨f p.1, hpU⟩
  let := schemeStalkAlgebra (.of ℂ) Y.structureMap (f p.1)
  let := TopCat.Presheaf.algebra_section_stalk Y.scheme.presheaf u
  let := open_stalk_scalar_tower Y.structureMap U u
  let : Algebra Γ(Y.scheme, U) (X.scheme.presheaf.stalk p.1) :=
    ((f.stalkMap p.1).hom.comp (Y.scheme.presheaf.germ U (f p.1) hpU).hom).toAlgebra
  let : IsScalarTower ℂ Γ(Y.scheme, U) (X.scheme.presheaf.stalk p.1) := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change schemeStalkScalar (.of ℂ) X.structureMap p.1 z =
      f.stalkMap p.1 (algebraMap Γ(Y.scheme, U) (Y.scheme.presheaf.stalk (f p.1))
        (algebraMap ℂ Γ(Y.scheme, U) z))
    rw [← IsScalarTower.algebraMap_apply]
    exact (dominant_stalk_scalar (.of ℂ) X.structureMap Y.structureMap f hf p.1 z).symm
  let : Algebra Γ(Y.scheme, U) X.scheme.functionField :=
    ((dominantFunctionFieldMap f).comp (Y.scheme.germToFunctionField U).hom).toAlgebra
  let : IsScalarTower Γ(Y.scheme, U) Y.scheme.functionField X.scheme.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    rfl
  let : IsScalarTower ℂ Γ(Y.scheme, U) X.scheme.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change algebraMap ℂ X.scheme.functionField z =
      dominantFunctionFieldMap f
        (algebraMap Γ(Y.scheme, U) Y.scheme.functionField (algebraMap ℂ Γ(Y.scheme, U) z))
    rw [← IsScalarTower.algebraMap_apply]
    exact (dominantFunctionFieldMap_scalar (.of ℂ) X.structureMap Y.structureMap f hf z).symm
  let : IsScalarTower Γ(Y.scheme, U) (X.scheme.presheaf.stalk p.1) X.scheme.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change dominantFunctionFieldMap f (Y.scheme.germToFunctionField U z) =
      algebraMap (X.scheme.presheaf.stalk p.1) X.scheme.functionField
        (f.stalkMap p.1 (Y.scheme.presheaf.germ U (f p.1) hpU z))
    rw [← dominantFunctionFieldMap_algebraMap, Y.scheme.algebraMap_germ_eq_germToFunctionField]
  obtain ⟨bp⟩ := nonempty_smooth_canonical_stalk_basis X.structureMap n p.1
  let v := topDifferentialMap ℂ Γ(Y.scheme, U) (X.scheme.presheaf.stalk p.1) n (bU 0)
  let c := bp.repr v 0
  have hc : v = c • bp 0 := basis_singleton_repr bp v
  dsimp only [v] at hc
  let cf := algebraMap (X.scheme.presheaf.stalk p.1) X.scheme.functionField c
  have hpull : rationalTopFormPullback (.of ℂ) X.structureMap Y.structureMap f hf n ω =
      (dominantFunctionFieldMap f a * cf) •
        topDifferentialMap ℂ (X.scheme.presheaf.stalk p.1) X.scheme.functionField n (bp 0) := by
    exact topDifferentialMap_scalar_chart n (bU 0) (bp 0) ω a c heq hc
  have hprod : dominantFunctionFieldMap f a * cf ≠ 0 := by
    intro h
    exact hDX.1 (by simpa [h] using hpull)
  have hcf : cf ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  obtain ⟨cp, a', ha', heq', hDXp⟩ := hDX.2 p
  have hDXord := canonical_local_order_unique X.structureMap n p _ cp bp a'
    (dominantFunctionFieldMap f a * cf) hDX.1 ha' hprod heq' hpull
  obtain ⟨g, hgSmooth⟩ := hg
  have hbound : T p ≤ X.scheme.ord cf p.1 + 1 := by
    let : Algebra.FormallySmooth ℂ (Y.scheme.presheaf.stalk (f p.1)) :=
      formallySmooth_smooth_stalk Y.structureMap n (f p.1)
    let : Algebra.FormallySmooth ℂ
        ((Y.scheme.presheaf.stalk (f p.1)) ⧸ Ideal.span {g.regular}) := hgSmooth
    obtain ⟨bY⟩ := nonempty_smooth_stalk_differential_basis Y.structureMap n (f p.1)
    let : Algebra (Y.scheme.presheaf.stalk (f p.1)) (X.scheme.presheaf.stalk p.1) :=
      (f.stalkMap p.1).hom.toAlgebra
    let : IsScalarTower ℂ (Y.scheme.presheaf.stalk (f p.1)) (X.scheme.presheaf.stalk p.1) := by
      apply IsScalarTower.of_algebraMap_eq
      intro z
      exact (dominant_stalk_scalar (.of ℂ) X.structureMap Y.structureMap f hf p.1 z).symm
    let : IsScalarTower Γ(Y.scheme,U) (Y.scheme.presheaf.stalk (f p.1))
        (X.scheme.presheaf.stalk p.1) := by
      apply IsScalarTower.of_algebraMap_eq
      intro z
      rfl
    exact cartier_order_le_jacobian_of_chart f D T hT p rfl bY bp g (bU 0) c hc hcf
  rw [hDXp, hDXord, X.scheme.ord_mul ((map_ne_zero _).mpr ha) hcf, hPa]
  omega
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open scoped IntermediateField.algebraAdjoinAdjoin

namespace NumericalDimensionOne

theorem exists_effective_locally_klt_member
    {n : ℕ} (Y : CanonicalModel n) (hY : IsSmoothNfold Y.toComplexProjectiveVariety n)
    (D : WeilDivisor Y.scheme) (hD : IsCartierDivisor D)
    (U : Y.scheme.Opens) (hU : Nonempty U)
    (hgen : ∀ x : Y.scheme, x ∈ U → IsGeneratedAt D x)
    (ε : ℚ) (hε : 0 ≤ ε) (hε1 : ε < 1) :
    ∃ F : Y.scheme.functionField, F ≠ 0 ∧ IsDivisorSection D F ∧
      let Δ := ε • rationalWeilDivisor (D + principalWeilDivisor F)
      0 ≤ Δ ∧ IsQCartierDivisor (rationalWeilDivisor Y.canonical + Δ) ∧
      ∀ W : ComplexProjectiveVariety, IsSmoothNfold W n →
        ∀ f : W.scheme ⟶ Y.scheme, ∀ (_ : IsDominant f),
          IsProper f → IsBirationalMorphism f →
          ∀ hf : f ≫ Y.structureMap = W.structureMap,
            ∀ KW : WeilDivisor W.scheme,
              IsCanonicalDivisorOf (.of ℂ) W.structureMap n
                (rationalTopFormPullback (.of ℂ) W.structureMap Y.structureMap f hf n Y.form) KW →
              ∀ P : QWeilDivisor W.scheme,
                IsQCartierPullback f (rationalWeilDivisor Y.canonical + Δ) P →
                ∀ p : PrimeDivisor W.scheme, f p.1 ∈ U →
                  -1 < (rationalWeilDivisor KW - P) p := by
  let : SmoothOfRelativeDimension n Y.structureMap := hY
  let : Smooth Y.structureMap := SmoothOfRelativeDimension.smooth n Y.structureMap
  obtain ⟨F,hF,hsec,hsm⟩ := exists_effective_member_smooth_on_open
    Y.toComplexProjectiveVariety D hD U hU hgen
  let E := D + principalWeilDivisor F
  have hE : IsCartierDivisor E := isCartierDivisor_add hD (isCartierDivisor_principal hF)
  have heff : 0 ≤ E := by
    intro p
    have hs := hsec.resolve_left hF p
    change 0 ≤ D p + Y.scheme.ord F p.1
    omega
  have hK := canonicalModel_isCartier Y hY
  let M : CartierMultiple (rationalWeilDivisor Y.canonical) := ⟨1,by decide,⟨_,hK⟩,by simp⟩
  let N : CartierMultiple (rationalWeilDivisor E) := ⟨1,by decide,⟨_,hE⟩,by simp⟩
  let R := M.add (N.smul ε)
  refine ⟨F,hF,hsec,?_,⟨R.denominator,R.positive,R.divisor.1,R.divisor.2,R.equation⟩,?_⟩
  · intro p
    change 0 ≤ ε * (E p : ℚ)
    exact mul_nonneg hε (by exact_mod_cast heff p)
  intro W hW f hdom _hproper _hbir hf KW hKW Q hQ p hpU
  let : IsDominant f := hdom
  let : StalkwiseNormal W.scheme := smoothNormal W hW
  obtain ⟨P,hP⟩ := exists_cartierPullback f Y.canonical hK
  obtain ⟨T,hT⟩ := exists_cartierPullback f E hE
  have he := hQ.unique ((hP.rational hK).add ((hT.rational hE).smul ε))
  rw [he]
  have ha := smooth_relative_canonical_effective W Y.toComplexProjectiveVariety n hW hY
    f hf Y.form KW Y.canonical hKW Y.canonical_of_form P hP p
  have hb := smooth_boundary_discrepancy_bound_at W Y.toComplexProjectiveVariety n hW hY
    f hf Y.form KW Y.canonical hKW Y.canonical_of_form P hP E T hT p (hsm (f p.1) hpU)
  have haQ : (0 : ℚ) ≤ (KW p : ℚ) - (P p : ℚ) := by exact_mod_cast ha
  have hbQ : (T p : ℚ) ≤ (KW p : ℚ) - (P p : ℚ) + 1 := by exact_mod_cast hb
  have hm := mul_le_mul_of_nonneg_left hbQ hε
  have hs : 0 < (1-ε)*((KW p : ℚ)-(P p : ℚ)+1) :=
    mul_pos (sub_pos.mpr hε1) (by linarith)
  change -1 < (KW p : ℚ) - ((P p : ℚ) + ε * (T p : ℚ))
  nlinarith
end NumericalDimensionOne

end OAI
