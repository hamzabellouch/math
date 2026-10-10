import Mathlib
import OAI.AlgebraicGeometry.SectionFields.FlatDescent

namespace OAI

/-! Generic-fibre geometry, function fields and principal presentations. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order Polynomial
open scoped TensorProduct WithZero
universe u

namespace RelativeDenominators

 

theorem flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hx : x ∈ U := X.affineCover.covers x
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
  dsimp [IsAffineOpen.fromSpecStalk]
  have : Flat (Spec.map (X.presheaf.germ U x hx)) := by
    rw [Flat.SpecMap_iff]
    let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      (X.presheaf.germ U x hx).hom.toAlgebra
    let := hU.isLocalization_stalk ⟨x, hx⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  infer_instance

 

theorem isIso_stalkMap_of_flat_preimmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsPreimmersion f] (x : X) :
    IsIso (f.stalkMap x) := by
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x))
    (X.presheaf.stalk x), f.stalkMap_surjective x⟩

 

abbrev genericFiber {X Z : Scheme.{u}} [IsIntegral Z] (f : X ⟶ Z) : Scheme.{u} :=
  pullback f (Z.fromSpecStalk (genericPoint Z))

abbrev genericFiberι {X Z : Scheme.{u}} [IsIntegral Z] (f : X ⟶ Z) :
    genericFiber f ⟶ X := pullback.fst _ _

abbrev genericFiberToSpec {X Z : Scheme.{u}} [IsIntegral Z] (f : X ⟶ Z) :
    genericFiber f ⟶ Spec Z.functionField := pullback.snd _ _

instance genericFiberι_flat {X Z : Scheme.{u}} [IsIntegral Z] (f : X ⟶ Z) :
    Flat (genericFiberι f) := by
  let := flat_fromSpecStalk Z (genericPoint Z)
  change Flat (pullback.fst f (Z.fromSpecStalk (genericPoint Z)))
  infer_instance

instance genericFiberι_preimmersion {X Z : Scheme.{u}} [IsIntegral Z] (f : X ⟶ Z) :
    IsPreimmersion (genericFiberι f) := inferInstanceAs (IsPreimmersion (pullback.fst _ _))

instance genericFiberι_stalk_iso {X Z : Scheme.{u}} [IsIntegral Z]
    (f : X ⟶ Z) (x : genericFiber f) : IsIso ((genericFiberι f).stalkMap x) :=
  isIso_stalkMap_of_flat_preimmersion _ _

lemma range_fromSpecStalk_generic (Z : Scheme.{u}) [IsIntegral Z] :
    Set.range (Z.fromSpecStalk (genericPoint Z)) = {genericPoint Z} := by
  rw [Scheme.range_fromSpecStalk]
  ext z
  exact ⟨fun h => (h.antisymm ((genericPoint_spec Z).specializes trivial)).eq,
    fun h => h ▸ specializes_rfl⟩

lemma range_genericFiberι {X Z : Scheme.{u}} [IsIntegral Z] (f : X ⟶ Z) :
    Set.range (genericFiberι f) = f ⁻¹' {genericPoint Z} := by
  rw [genericFiberι, Scheme.Pullback.range_fst, range_fromSpecStalk_generic]

lemma genericPoint_mem_range_genericFiberι
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsDominant f] : genericPoint X ∈ Set.range (genericFiberι f) := by
  rw [range_genericFiberι]
  change f (genericPoint X) = genericPoint Z
  apply IsGenericPoint.eq _ (genericPoint_spec Z)
  simpa [Set.image_univ, f.denseRange.closure_range] using
    (genericPoint_spec X).image f.continuous

instance genericFiberι_dominant
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsDominant f] : IsDominant (genericFiberι f) := by
  constructor
  intro x
  apply closure_mono (Set.singleton_subset_iff.mpr (genericPoint_mem_range_genericFiberι f))
  rw [(genericPoint_spec X).def]
  trivial

instance genericFiber_irreducible
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsDominant f] : IrreducibleSpace (genericFiber f) := by
  obtain ⟨y, hy⟩ := genericPoint_mem_range_genericFiberι f
  have hg : IsGenericPoint y Set.univ := by
    rw [isGenericPoint_iff_specializes]
    intro z
    simp only [Set.mem_univ, iff_true]
    apply (genericFiberι f).isEmbedding.isInducing.specializes_iff.mp
    rw [hy]
    exact (genericPoint_spec X).specializes trivial
  exact (irreducibleSpace_def _).mpr hg.isIrreducible

instance genericFiber_reduced
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) : AlgebraicGeometry.IsReduced (genericFiber f) := by
  let (x : genericFiber f) : _root_.IsReduced ((genericFiber f).presheaf.stalk x) :=
    isReduced_of_injective (asIso ((genericFiberι f).stalkMap x)).inv.hom
      (ConcreteCategory.bijective_of_isIso _).1
  exact isReduced_of_isReduced_stalk _

instance genericFiber_integral
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsDominant f] : IsIntegral (genericFiber f) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

theorem genericFiber_normal
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (x : genericFiber f) : IsIntegrallyClosed ((genericFiber f).presheaf.stalk x) := by
  let := hNX (genericFiberι f x)
  exact IsIntegrallyClosed.of_equiv
    (asIso ((genericFiberι f).stalkMap x)).commRingCatIsoToRingEquiv

instance genericFiber_isNoetherian
    {X Z : Scheme.{u}} [IsIntegral Z] (f : X ⟶ Z) [LocallyOfFiniteType f] [QuasiCompact f] :
    IsNoetherian (genericFiber f) := by
  have : LocallyOfFiniteType (genericFiberToSpec f) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : QuasiCompact (genericFiberToSpec f) :=
    inferInstanceAs (QuasiCompact (pullback.snd _ _))
  have : IsLocallyNoetherian (genericFiber f) :=
    LocallyOfFiniteType.isLocallyNoetherian (genericFiberToSpec f)
  have : CompactSpace (genericFiber f) :=
    QuasiCompact.compactSpace_of_compactSpace (genericFiberToSpec f)
  exact {}

open Order TopologicalSpace

 

noncomputable def genericFiberFunctionFieldEquiv
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsDominant f] :
    X.functionField ≃+* (genericFiber f).functionField := by
  apply RingEquiv.ofBijective (functionFieldPullback (genericFiberι f))
  let e := X.presheaf.stalkCongr
    (Inseparable.of_eq (genericPoint_eq_of_dominant (genericFiberι f)))
  have he : X.presheaf.stalkSpecializes
      (specializes_of_eq (genericPoint_eq_of_dominant (genericFiberι f))) = e.inv := rfl
  have : IsIso (X.presheaf.stalkSpecializes
      (specializes_of_eq (genericPoint_eq_of_dominant (genericFiberι f)))) := by
    rw [he]; infer_instance
  exact ConcreteCategory.bijective_of_isIso
    (X.presheaf.stalkSpecializes
      (specializes_of_eq (genericPoint_eq_of_dominant (genericFiberι f))) ≫
      (genericFiberι f).stalkMap (genericPoint (genericFiber f)))

 

theorem pullbackQCartier_eq_zero_at_of_mem_range
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [Flat f]
    (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (hzero : pullbackQCartier hNZ f D hD = 0)
    (p : PrimeDivisor Z) (hp : p.1 ∈ Set.range f) : D p = 0 := by
  let c := hD.data
  obtain ⟨x, hx⟩ := hp
  have hord : ∀ y : X, f y ∈ c.chart p.1 → coheight y = 1 →
      X.ord (functionFieldPullback f (c.equation p.1 : Z.functionField)) y = 0 := by
    intro y hy hc
    have h := pullbackQCartier_apply_of_local hNZ f D hD c.index c.index_pos
      (c.chart p.1) (c.equation p.1) (c.ord_eq p.1) ⟨y, hc⟩ hy
    rw [hzero, Finsupp.zero_apply] at h
    have hz : (X.ord (functionFieldPullback f (c.equation p.1 : Z.functionField)) y : ℚ) = 0 := by
      exact (div_eq_zero_iff).mp h.symm |>.resolve_right (by exact_mod_cast c.index_pos.ne')
    exact_mod_cast hz
  obtain ⟨r, hr⟩ := stalk_unit_of_flat_pullback_ord_zero hNX f (c.chart p.1)
    (c.equation p.1) hord x (by simpa only [hx] using c.mem_chart p.1)
  have hz : Z.ord (c.equation p.1 : Z.functionField) (f x) = 0 := by
    rw [← hr]
    exact ord_eq_zero_of_stalk_unit Z (f x) (by rw [hx]; exact p.2) r
  rw [hx] at hz
  have he := c.ord_eq p.1 p (c.mem_chart p.1)
  rw [hz, Int.cast_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (by exact_mod_cast c.index_pos.ne')

 

theorem isVertical_of_genericFiber_pullback_zero
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] [IsNoetherian X]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X ⟶ Z) [IsDominant f] [LocallyOfFiniteType f] [QuasiCompact f]
    (D : RationalWeilDivisor X) (hD : IsQCartier X D)
    (hzero : pullbackQCartier hNX (genericFiberι f) D hD = 0) :
    IsVerticalRationalDivisor f D := by
  intro p hp he
  apply hp
  apply pullbackQCartier_eq_zero_at_of_mem_range (genericFiber_normal f hNX)
    hNX (genericFiberι f) D hD hzero p
  rw [range_genericFiberι]
  exact he

 

theorem exists_vertical_principalization_of_genericFiber
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] [IsNoetherian X]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X ⟶ Z) [IsDominant f] [LocallyOfFiniteType f] [QuasiCompact f]
    (A : RationalWeilDivisor X) (hA : IsQCartier X A) (p : ℕ)
    (u : (genericFiber f).functionFieldˣ)
    (hu : (p : ℚ) • pullbackQCartier hNX (genericFiberι f) A hA +
      rationalPrincipalDivisor (genericFiber f) u = 0) :
    ∃ ψ : X.functionFieldˣ,
      IsVerticalRationalDivisor f ((p : ℚ) • A + rationalPrincipalDivisor X ψ) := by
  let e := genericFiberFunctionFieldEquiv f
  let ψ := Units.map e.symm.toMonoidHom u
  have hψ : Units.map (functionFieldPullback (genericFiberι f)).toMonoidHom ψ = u := by
    apply Units.ext
    exact e.apply_symm_apply (u : (genericFiber f).functionField)
  refine ⟨ψ, isVertical_of_genericFiber_pullback_zero hNX f _
    (isQCartier_add (isQCartier_smul hA (p : ℚ)) (isQCartier_principal X ψ)) ?_⟩
  rw [pullbackQCartier_add hNX (genericFiberι f)
      (isQCartier_smul hA (p : ℚ)) (isQCartier_principal X ψ),
    pullbackQCartier_smul hNX (genericFiberι f) hA,
    pullbackQCartier_principal hNX (genericFiberι f), hψ]
  exact hu

 

theorem relative_exact_presentation_of_genericFiber_principalization
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [IsIso f.c] [LocallyOfFiniteType f] [QuasiCompact f]
    (A : RationalWeilDivisor X) (hA : IsQCartier X A)
    (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (p a : ℕ) (hp : 0 < p) (ha : 0 < a) (hpa : p ∣ a)
    (u : (genericFiber f).functionFieldˣ)
    (hu : (p : ℚ) • pullbackQCartier hNX (genericFiberι f) A hA +
      rationalPrincipalDivisor (genericFiber f) u = 0)
    (φ : X.functionFieldˣ)
    (hlinear : (a : ℚ) • A + rationalPrincipalDivisor X φ =
      pullbackQCartier hNZ f ((a : ℚ) • D) (isQCartier_smul hD (a : ℚ))) :
    ∃ (ψ : X.functionFieldˣ) (DZ : RationalWeilDivisor Z) (hDZ : IsQCartier Z DZ),
      RationallyLinearlyEquivalent Z DZ D ∧
      A + (p : ℚ)⁻¹ • rationalPrincipalDivisor X ψ = pullbackQCartier hNZ f DZ hDZ := by
  obtain ⟨ψ, hψ⟩ := exists_vertical_principalization_of_genericFiber hNX f A hA p u hu
  obtain ⟨DZ, hDZ, hlin, heq⟩ := relative_exact_presentation_of_vertical_principalization
    hNX hNZ f A D hD p a hp ha hpa ψ φ hψ hlinear
  exact ⟨ψ, DZ, hDZ, hlin, heq⟩

end RelativeDenominators
end

end OAI
