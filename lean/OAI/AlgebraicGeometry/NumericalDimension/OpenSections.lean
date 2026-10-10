import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.CompleteIntersections

namespace OAI

/-! Open Sections. -/

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

namespace NumericalDimensionOne
attribute [local instance] MvPolynomial.gradedAlgebra

theorem hyperplane_intersection_component_dimension_lower
    {X S : Scheme} [IsLocallyNoetherian X] [NoetherianSpace S] [JacobsonSpace S]
    {N d r : ℕ} (f : X ⟶ complexProjectiveSpace N) [IsClosedImmersion f]
    (i : S ⟶ X) [IsClosedImmersion i] (a : Fin r → Fin (N+1) → ℂ)
    (hs : Set.range i = {x | ∀ j, f x ∉
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
        (projectiveLinearPolynomial (a j))})
    (hd : ∀ x : X, IsClosed {x} → (d+r : ℕ) ≤ Order.coheight x)
    {Z : Set S} (hZ : Z ∈ irreducibleComponents S) :
    (d : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
  obtain ⟨p,hpc,_,hpZ⟩ := exists_closed_point_in_component_interior S hZ
  have hpic : IsClosed {i p} := by
    simpa only [Set.image_singleton] using i.isClosedEmbedding.isClosedMap {p} hpc
  have hp : ∀ j, f (i p) ∉
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
        (projectiveLinearPolynomial (a j)) := by
    have h : i p ∈ Set.range i := Set.mem_range_self p
    rw [hs] at h
    exact h
  obtain ⟨q,hpq,hqd,hqa⟩ := projective_section_dimension_lower f (i p) a hp (hd _ hpic)
  have hqr : q ∈ Set.range i := by rwa [hs]
  obtain ⟨y,hyq⟩ := hqr
  have hpy : p ≤ y := by
    apply i.isClosedEmbedding.isEmbedding.isInducing.specializes_iff.mp
    rw [hyq]
    exact hpq
  have hdy : (d : ℕ∞) ≤ Order.height y := by
    rwa [height_eq_of_closedImmersion i y,hyq]
  exact (WithBot.coe_le_coe.mpr hdy).trans
    (height_le_closed_topologicalKrullDim (isClosed_of_mem_irreducibleComponents Z hZ)
      ⟨y,hpZ y hpy⟩)
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

namespace NumericalDimensionOne
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

theorem IncidenceCutChain.pure_dimension_of_embedding
    {X S : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {N d r : ℕ} {D : WeilDivisor X} {s : Fin (N+1) → X.functionField}
    (A : DivisorAffineAtlas X D s) (sX : X ⟶ Spec (.of ℂ)) [IsProper sX]
    (J : 𝔸(Fin (N+1);X).IdealSheafData)
    (hJ : ∀ j, J.comap (AffineSpace.map _ (A.cover.f j)) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (A.coordinate j)}))
    (f : X ⟶ complexProjectiveSpace N) [IsClosedImmersion f]
    (hf : ∀ j, (A.chart j).domain.ι ≫ f = (A.chart j).toMorphism sX)
    {i : S ⟶ X} (h : IncidenceCutChain X sX J r S i)
    (hdim : topologicalKrullDim X = (d+r : ℕ)) :
    Nonempty S ∧ topologicalKrullDim S = d ∧
      ∀ Z ∈ irreducibleComponents S, topologicalKrullDim Z = d := by
  have := h.isClosedImmersion
  have : IsProper (i ≫ sX) := inferInstance
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (i ≫ sX)
  have : IsNoetherian S := ⟨⟩
  have : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace (i ≫ sX)
  have hdq : (d+r : ℕ) ≤ Order.height (genericPoint X) := by
    have he := (genericPoint_height_eq_dimension X).trans hdim
    exact_mod_cast le_of_eq he.symm
  obtain ⟨x,hxd⟩ := h.exists_height_ge_of_embedding A sX J hJ f hf (genericPoint X) hdq
  have hu := h.height_le (fun q => by
    have he := Order.height_le_krullDim q
    rw [← scheme_topologicalKrullDim_eq,hdim] at he
    exact_mod_cast he)
  have hS : topologicalKrullDim S = d := by
    rw [scheme_topologicalKrullDim_eq]
    apply le_antisymm
    · rw [Order.krullDim_eq_iSup_height]
      exact iSup_le (fun q => WithBot.coe_le_coe.mpr (hu q))
    · exact (WithBot.coe_le_coe.mpr hxd).trans (Order.height_le_krullDim x)
  refine ⟨⟨x⟩,hS,?_⟩
  obtain ⟨ps,hps,_,hker⟩ := h.exists_parameters
  have hrange : Set.range i = {x | ∀ j : Fin ps.length, f x ∉
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
        (projectiveLinearPolynomial (parameterCoefficient (ps.get j)))} := by
    rw [← i.isClosedEmbedding.isClosed_range.closure_eq,← Scheme.Hom.support_ker,hker]
    ext x
    refine (incidenceIntersectionIdeal_mem_support sX J ps x).trans ?_
    constructor
    · intro hx j
      have hm := hx (ps.get j) (List.get_mem ps j)
      change x ∈ ((J.comap (parameterSection sX (ps.get j))).support : Set X) at hm
      rwa [A.incidence_member_support sX J hJ f hf] at hm
    · intro hx p hp
      obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hp
      change x ∈ ((J.comap (parameterSection sX (ps.get j))).support : Set X)
      rw [A.incidence_member_support sX J hJ f hf]
      exact hx j
  have hff := functionField_dimension_of_dimension sX (d+r) hdim
  obtain ⟨_,hclosed,_⟩ := scheme_dimension_of_functionField ℂ sX (d+r) hff
  intro Z hZ
  apply le_antisymm
  · exact (topologicalKrullDim_subspace_le S Z).trans hS.le
  · apply hyperplane_intersection_component_dimension_lower f i
      (fun j => parameterCoefficient (ps.get j)) hrange _ hZ
    intro q hq
    rw [hclosed q hq,hps]
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

namespace NumericalDimensionOne
noncomputable section

theorem exists_smooth_pure_very_ample_complete_intersection
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {N d r : ℕ} {D : WeilDivisor X} {s : Fin (N+1) → X.functionField}
    (A : DivisorAffineAtlas X D s) (hs : ∀ j, s j ≠ 0)
    (sX : X ⟶ Spec (.of ℂ)) [IsProper sX]
    (f : X ⟶ complexProjectiveSpace N) [IsClosedImmersion f]
    (hf : ∀ j, (A.chart j).domain.ι ≫ f = (A.chart j).toMorphism sX)
    (hover : f ≫ complexProjectiveSpaceMap N = sX)
    (hdim : topologicalKrullDim X = (d+r : ℕ)) (U : X.Opens)
    [Smooth (U.ι ≫ sX)] {ι : Type} [Countable ι]
    (Z : ι → Set X) (hZ : ∀ j, IsClosed (Z j))
    (hdU : topologicalKrullDim ↥((U : Set X)ᶜ) < r)
    (hdZ : ∀ j, topologicalKrullDim (Z j) < r) :
    ∃ (J : 𝔸(Fin (N+1);X).IdealSheafData) (S : Scheme) (i : S ⟶ X),
      (∀ a, J.comap (AffineSpace.map _ (A.cover.f a)) =
        Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (A.coordinate a)})) ∧
      IncidenceCutChain X sX J r S i ∧ Smooth (i ≫ sX) ∧
      Nonempty S ∧ topologicalKrullDim S = d ∧
      (∀ T ∈ irreducibleComponents S, topologicalKrullDim T = d) ∧
      IsComplexProjective (i ≫ sX) ∧ Set.range i ⊆ U ∧ ∀ j x, i x ∉ Z j
 := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have : Uncountable ℂ := Cardinal.aleph0_lt_mk_iff.mp (by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum)
  obtain ⟨J,hJ⟩ := A.incidence_exists hs
  let T : Option ι → Set X := fun a => a.elim ((U : Set X)ᶜ) Z
  have hT : ∀ a, IsClosed (T a) := by
    intro a
    rcases a with _ | a
    · exact U.isOpen.isClosed_compl
    · exact hZ a
  have hdT : ∀ a x, x ∈ T a → Order.height x < r := by
    intro a
    rcases a with _ | a
    · exact height_lt_of_closed_dim_lt U.isOpen.isClosed_compl hdU
    · exact height_lt_of_closed_dim_lt (hZ a) (hdZ a)
  obtain ⟨S,i,hchain,hsm,ha⟩ := exists_smooth_complete_intersection_avoiding r sX U
    A.cover A.coordinate
    (fun a => ⟨(A.chart a).unit_index,by simp [DivisorAffineAtlas.coordinate,
      DivisorProjectiveChart.normalized_index]; rfl⟩) J hJ T hT
    (height_lt_of_closed_dim_lt U.isOpen.isClosed_compl hdU) hdT
  obtain ⟨hne,hd,hpure⟩ := hchain.pure_dimension_of_embedding A sX J hJ f hf hdim
  have := hchain.isClosedImmersion
  refine ⟨J,S,i,hJ,hchain,hsm,hne,hd,hpure,?_,?_,?_⟩
  · exact ⟨N,i ≫ f,inferInstance,by simp only [Category.assoc,hover]⟩
  · rintro _ ⟨x,rfl⟩
    exact Classical.not_not.mp (ha none x)
  · intro j
    exact ha (some j)
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

theorem nonempty_differential_basis_of_transcendence_basis
    {k K ι : Type} [Field k] [Field K] [Algebra k K] [CharZero k]
    {v : ι → K} (hv : IsTranscendenceBasis k v) :
    Nonempty (Module.Basis ι K Ω[K⁄k]) := by
  let A := Algebra.adjoin k (Set.range v)
  let F := IntermediateField.adjoin k (Set.range v)
  let e : MvPolynomial ι k ≃ₐ[k] A := hv.1.aevalEquiv
  let : Algebra (MvPolynomial ι k) A := e.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial ι k) A := IsScalarTower.of_algHom e.toAlgHom
  let e' : MvPolynomial ι k ≃ₐ[MvPolynomial ι k] A :=
    { e.toRingEquiv with commutes' := fun _ => rfl }
  have : Algebra.FormallyEtale (MvPolynomial ι k) A := Algebra.FormallyEtale.of_equiv e'
  let bA := (KaehlerDifferential.isBaseChange_of_formallyEtale k (MvPolynomial ι k) A).basis
    (KaehlerDifferential.mvPolynomialBasis k ι)
  have : Algebra.FormallyEtale A F := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  let bF := (KaehlerDifferential.isBaseChange_of_formallyEtale k A F).basis bA
  have : Algebra.IsAlgebraic A K := hv.isAlgebraic
  have : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.extendScalars
    (IsFractionRing.injective A F)
  have : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  exact ⟨(KaehlerDifferential.isBaseChange_of_formallyEtale k F K).basis bF⟩
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

theorem differential_rank_eq_trdeg (k K : Type) [Field k] [Field K]
    [Algebra k K] [CharZero k] : Module.rank K Ω[K⁄k] = Algebra.trdeg k K := by
  obtain ⟨v,hv⟩ := exists_isTranscendenceBasis k K
  obtain ⟨b⟩ := nonempty_differential_basis_of_transcendence_basis hv
  exact b.mk_eq_rank''.symm.trans hv.cardinalMk_eq_trdeg

theorem standardSmoothOfRelativeDimension_of_fractionField
    (k A K : Type) [Field k] [CommRing A] [IsDomain A] [Field K] [CharZero k]
    [Algebra k A] [Algebra k K] [Algebra A K] [IsScalarTower k A K]
    [IsFractionRing A K] [Algebra.IsStandardSmooth k A]
    (n : ℕ) (hd : Algebra.trdeg k K = n) :
    Algebra.IsStandardSmoothOfRelativeDimension n k A := by
  apply (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth n).mpr
  have : Algebra.FormallyEtale A K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  let b := Module.Free.chooseBasis A Ω[A⁄k]
  let bK := (KaehlerDifferential.isBaseChange_of_formallyEtale k A K).basis b
  rw [← b.mk_eq_rank'', bK.mk_eq_rank'', differential_rank_eq_trdeg,hd]
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

theorem isReduced_of_etale_domain_base (R A : Type*) [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.Etale R A] : IsReduced A := by
  let K := FractionRing R
  have : Algebra.FormallyUnramified K (K ⊗[R] A) := inferInstance
  have : IsReduced (K ⊗[R] A) := Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[R] A)
  let f := (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := A))
  have hf : Function.Injective f := by
    have he : ⇑f = (LinearMap.rTensor A (Algebra.ofId R K).toLinearMap).comp
        (Algebra.TensorProduct.lid R A).symm.toLinearMap := by
      ext a
      simp [f]
    rw [he]
    exact (Module.Flat.rTensor_preserves_injective_linearMap _
      (IsFractionRing.injective R K)).comp (Algebra.TensorProduct.lid R A).symm.injective
  exact isReduced_of_injective f hf

theorem isReduced_of_smooth_field (k A : Type*) [Field k] [CommRing A]
    [Algebra k A] [Algebra.Smooth k A] : IsReduced A := by
  apply isReduced_ofLocalizationMaximal
  intro p hp
  let := hp
  obtain ⟨f,hfp,n,af,ht,he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p)
  let : Algebra (MvPolynomial (Fin n) k) (Localization.Away f) := af
  let : IsScalarTower k (MvPolynomial (Fin n) k) (Localization.Away f) := ht
  let : Algebra.IsStandardEtale (MvPolynomial (Fin n) k) (Localization.Away f) := he
  have : IsReduced (Localization.Away f) :=
    isReduced_of_etale_domain_base (MvPolynomial (Fin n) k) (Localization.Away f)
  have hle : Submonoid.powers f ≤ p.primeCompl := Submonoid.powers_le.mpr hfp
  let : Algebra (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ hle
  let : IsScalarTower A (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  let : IsLocalization (p.primeCompl.map (algebraMap A (Localization.Away f)))
      (Localization.AtPrime p) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ _ hle
  exact isReduced_localizationPreserves
    (p.primeCompl.map (algebraMap A (Localization.Away f))) (Localization.AtPrime p) inferInstance
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

theorem scheme_isReduced_of_smooth_field
    {k : Type} [Field k] {X : Scheme} (sX : X ⟶ Spec (.of k)) [Smooth sX] :
    IsReduced X := by
  apply +allowSynthFailures isReduced_of_isReduced_stalk
  intro x
  obtain ⟨U,hU,V,hV,hx,e,hsm⟩ := Smooth.exists_isStandardSmooth sX x
  have hUtop : U = ⊤ := by
    ext y
    have hm : sX x ∈ U := e hx
    rw [Subsingleton.elim (sX x) y] at hm
    exact ⟨fun _ => trivial,fun _ => hm⟩
  subst U
  let := schemeOpenAlgebra sX V
  have hstd : RingHom.IsStandardSmooth (schemeOpenScalar sX V) :=
    RingHom.isStandardSmooth_respectsIso.right (sX.appLE ⊤ V e).hom
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv hsm
  have : Algebra.IsStandardSmooth k Γ(X,V) := hstd
  have : _root_.IsReduced Γ(X,V) := isReduced_of_smooth_field k Γ(X,V)
  let y : V := ⟨x,hx⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf y
  let := hV.isLocalization_stalk y
  exact isReduced_localizationPreserves (hV.primeIdealOf y).asIdeal.primeCompl
    (X.presheaf.stalk x) inferInstance
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

lemma stalk_scalar_over
    {X Y : Scheme} (k : CommRingCat) (sY : Y ⟶ Spec k)
    (f : X ⟶ Y) (x : X) (a : k) :
    f.stalkMap x (schemeStalkScalar k sY (f x) a) =
      schemeStalkScalar k (f ≫ sY) x a := by
  simp only [schemeStalkScalar, RingHom.coe_comp, Function.comp_apply,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  simp only [Scheme.Hom.appTop]
  exact f.germ_stalkMap_apply ⊤ x (by trivial) (sY.appTop ((Scheme.ΓSpecIso k).inv a))

lemma generic_component_stalk_isField {X : Scheme} [IsReduced X] (q : X)
    (hq : closure ({q} : Set X) ∈ irreducibleComponents X) :
    IsField (X.presheaf.stalk q) := by
  exact isField_stalk_of_closure_mem_irreducibleComponents X q hq
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

theorem generic_component_stalk_trdeg {k : Type} [Field k] {X : Scheme} [IsReduced X]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (n : ℕ) (hpure : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = n)
    (q : X) (hq : closure ({q} : Set X) ∈ irreducibleComponents X) :
    let := schemeStalkAlgebra (.of k) sX q;
    Algebra.trdeg k (X.presheaf.stalk q) = n := by
  let C := pointClosure q
  let f := pointClosureι q
  let g := genericPoint C
  let := schemeStalkAlgebra (.of k) sX (f g)
  let := schemeFieldAlgebra (.of k) (f ≫ sX)
  have hq' : closure ({f g} : Set X) ∈ irreducibleComponents X := by
    simpa only [f,g,C,pointClosure_generic] using hq
  have hfld := generic_component_stalk_isField (f g) hq'
  let := hfld.toField
  let e : (X.presheaf.stalk (f g)) ≃ₐ[k] C.functionField :=
    { RingEquiv.ofBijective (f.stalkMap g).hom
        ⟨(f.stalkMap g).hom.injective,f.stalkMap_surjective g⟩ with
      commutes' := fun a => stalk_scalar_over (.of k) sX f g a }
  let eC := f.isClosedEmbedding.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (pointClosure_range q))
  have hd : topologicalKrullDim C = n :=
    (eC.isHomeomorph.topologicalKrullDim_eq eC).trans (hpure _ hq)
  have hh := e.trdeg_eq.trans (functionField_dimension_of_dimension (f ≫ sX) n hd)
  change (let := schemeStalkAlgebra (.of k) sX (f g);
    Algebra.trdeg k (X.presheaf.stalk (f g)) = n) at hh
  dsimp only [f,g,C] at hh
  rw [pointClosure_generic] at hh
  exact hh
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

theorem standardSmoothOfRelativeDimension_of_formallyEtaleField
    (k A K : Type) [Field k] [CommRing A] [Nontrivial A] [Field K] [CharZero k]
    [Algebra k A] [Algebra k K] [Algebra A K] [IsScalarTower k A K]
    [Algebra.FormallyEtale A K] [Algebra.IsStandardSmooth k A]
    (n : ℕ) (hd : Algebra.trdeg k K = n) :
    Algebra.IsStandardSmoothOfRelativeDimension n k A := by
  apply (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth n).mpr
  let b := Module.Free.chooseBasis A Ω[A⁄k]
  let bK := (KaehlerDifferential.isBaseChange_of_formallyEtale k A K).basis b
  rw [← b.mk_eq_rank'',bK.mk_eq_rank'',differential_rank_eq_trdeg,hd]

theorem smooth_relative_dimension_of_pure_dimension
    {k : Type} [Field k] [CharZero k] {X : Scheme}
    (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (n : ℕ) (hpure : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = n) :
    SmoothOfRelativeDimension n sX := by
  have : IsReduced X := scheme_isReduced_of_smooth_field sX
  constructor
  intro x
  obtain ⟨U,hU,V,hV,hx,e,hsm⟩ := Smooth.exists_isStandardSmooth sX x
  have hUtop : U = ⊤ := by
    ext y
    have hm : sX x ∈ U := e hx
    rw [Subsingleton.elim (sX x) y] at hm
    exact ⟨fun _ => trivial,fun _ => hm⟩
  subst U
  have : Nonempty V := ⟨⟨x,hx⟩⟩
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent x,irreducibleComponent_mem_irreducibleComponents x⟩
  let q : genericPoints X := genericPoints.ofComponent C
  have hqV : q.1 ∈ V :=
    ((genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent).mem_open
      V.isOpen hx
  let y : V := ⟨q.1,hqV⟩
  let := schemeOpenAlgebra sX V
  let := schemeStalkAlgebra (.of k) sX q.1
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf y
  have := open_stalk_scalar_tower sX V y
  let := (generic_component_stalk_isField q.1 q.2).toField
  have := hV.isLocalization_stalk y
  have : Algebra.FormallyEtale Γ(X,V) (X.presheaf.stalk q.1) :=
    Algebra.FormallyEtale.of_isLocalization (hV.primeIdealOf y).asIdeal.primeCompl
  have hstd : RingHom.IsStandardSmooth (schemeOpenScalar sX V) :=
    RingHom.isStandardSmooth_respectsIso.right (sX.appLE ⊤ V e).hom
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv hsm
  have : Algebra.IsStandardSmooth k Γ(X,V) := hstd
  have htrdeg : Algebra.trdeg k (X.presheaf.stalk q.1) = n :=
    generic_component_stalk_trdeg sX n hpure q.1 q.2
  have hrel : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X,V) :=
    standardSmoothOfRelativeDimension_of_formallyEtaleField k Γ(X,V)
      (X.presheaf.stalk q.1) n htrdeg
  have hr : RingHom.IsStandardSmoothOfRelativeDimension n (schemeOpenScalar sX V) := hrel
  refine ⟨⊤,hU,V,hV,hx,e,?_⟩
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).cancel_left_isIso
    (Scheme.ΓSpecIso (.of k)).inv (sX.appLE ⊤ V e) |>.mp hr
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
lemma generated_finite_section_cover_on_open
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (D : WeilDivisor X) (U : X.Opens) (hU : Nonempty U)
    (hgen : ∀ x : X, x ∈ U → IsGeneratedAt D x) :
    ∃ N : ℕ, ∃ s : Fin (N+1) → X.functionField,
      (∀ i, s i ≠ 0 ∧ IsDivisorSection D (s i)) ∧
      (∀ x : X, x ∈ U → ∃ i, x ∈ sectionNonvanishing D (s i)) := by
  classical
  choose s hs hsec hx using fun x : U => hgen x.1 x.2
  have : NoetherianSpace X := (show IsNoetherian X from ⟨⟩).noetherianSpace
  obtain ⟨V,hV⟩ := (NoetherianSpace.isCompact (U : Set X)).elim_finite_subcover
    (fun x : U => (sectionNonvanishing D (s x) : Set X))
    (fun x => (sectionNonvanishing D (s x)).isOpen)
    (fun x h => Set.mem_iUnion.mpr ⟨⟨x,h⟩,hx ⟨x,h⟩⟩)
  let e : Fin (V.card+1) ≃ Option V :=
    (Fintype.equivFinOfCardEq (by simp)).symm
  let point : Option V → U := fun o => o.elim (Classical.choice hU) Subtype.val
  refine ⟨V.card,fun i => s (point (e i)),fun i => ⟨hs _,hsec _⟩,?_⟩
  intro x hxU
  obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hV hxU)
  exact ⟨e.symm (some ⟨y,hy⟩),by simpa [point] using hxy⟩

namespace DivisorProjectiveChart
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type} {D : WeilDivisor X} {s : I → X.functionField}
def restrict (C : DivisorProjectiveChart X D s) (V : X.Opens)
    (hV : V ≤ C.domain) (hv : genericPoint X ∈ V) : DivisorProjectiveChart X D s where
  domain := V
  generic_mem := hv
  equation := C.equation
  equation_ne_zero := C.equation_ne_zero
  equation_order p hp := C.equation_order p (hV hp)
  coordinate i := X.presheaf.map (homOfLE hV).op (C.coordinate i)
  coordinate_value i := by
    let : Nonempty V := ⟨⟨genericPoint X,hv⟩⟩
    let : Nonempty C.domain := ⟨⟨genericPoint X,C.generic_mem⟩⟩
    exact (germToFunctionField_restrict (homOfLE hV) (C.coordinate i)).trans
      (C.coordinate_value i)
  unit_index := C.unit_index
  coordinate_unit := C.coordinate_unit.map _
end DivisorProjectiveChart

lemma exists_affine_divisorProjectiveChart_inside
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [StalkwiseNormal X] [CompactSpace X]
    {I : Type} {D : WeilDivisor X} {s : I → X.functionField}
    (hD : IsCartierDivisor D) (hs : ∀ i, s i ≠ 0 ∧ IsDivisorSection D (s i))
    (U : X.Opens) (x : X) (hxU : x ∈ U)
    (hx : ∃ i, x ∈ sectionNonvanishing D (s i)) :
    ∃ C : DivisorProjectiveChart X D s,
      x ∈ C.domain ∧ IsAffineOpen C.domain ∧ C.domain ≤ U := by
  obtain ⟨C,hC⟩ := exists_divisorProjectiveChart hD hs x hx
  obtain ⟨V,hV,hxV,hVU⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x ∈ C.domain ⊓ U from ⟨hC,hxU⟩)
  have hgen : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨x,Set.mem_univ x,hxV⟩
  exact ⟨C.restrict V (le_trans hVU inf_le_left) hgen,hxV,hV,
    le_trans hVU inf_le_right⟩
end
end NumericalDimensionOne

end OAI
