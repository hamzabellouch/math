import Mathlib
import OAI.AlgebraicGeometry.SectionFields.GaloisAction

namespace OAI

/-! Faithfully flat descent of fractions and injectivity of divisor pullback. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Order Polynomial
open scoped TensorProduct WithZero
universe u

namespace RelativeDenominators
section

 

theorem fraction_mem_of_faithfullyFlat
    (R S K T : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Field K] [Field T] [Algebra R S] [Module.FaithfullyFlat R S]
    [Algebra R K] [IsFractionRing R K] [Algebra S T] [IsFractionRing S T]
    (i : K →+* T)
    (hi : ∀ r : R, i (algebraMap R K r) = algebraMap S T (algebraMap R S r))
    (x : K) (s : S) (hs : i x = algebraMap S T s) :
    ∃ r : R, algebraMap R K r = x := by
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective R x
  have hbK : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have he : algebraMap R S b * s = algebraMap R S a := by
    apply IsFractionRing.injective S T
    rw [map_mul, ← hi, ← hs, ← map_mul, ← hx, mul_div_cancel₀ _ hbK, hi]
  have hbS : algebraMap R S a ∈ Ideal.span ({algebraMap R S b} : Set S) := by
    apply Ideal.mem_span_singleton.mpr
    exact ⟨s, he.symm⟩
  have ha : a ∈ Ideal.span ({b} : Set R) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) (Ideal.span ({b} : Set R))]
    exact (Ideal.mem_comap).mpr (by simpa [Ideal.map_span, Set.image_singleton] using hbS)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ha
  refine ⟨r, ?_⟩
  rw [← hx, hr, map_mul, mul_div_cancel_left₀ _ hbK]

 

theorem fraction_unit_of_faithfullyFlat
    (R S K T : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Field K] [Field T] [Algebra R S] [Module.FaithfullyFlat R S]
    [Algebra R K] [IsFractionRing R K] [Algebra S T] [IsFractionRing S T]
    (i : K →+* T)
    (hi : ∀ r : R, i (algebraMap R K r) = algebraMap S T (algebraMap R S r))
    (x : Kˣ) (s : Sˣ) (hs : i (x : K) = algebraMap S T (s : S)) :
    ∃ r : Rˣ, algebraMap R K (r : R) = (x : K) := by
  obtain ⟨a, ha⟩ := fraction_mem_of_faithfullyFlat R S K T i hi (x : K) (s : S) hs
  have hs' : i ((x⁻¹ : Kˣ) : K) = algebraMap S T ((s⁻¹ : Sˣ) : S) := by
    apply mul_left_cancel₀ (show i (x : K) ≠ 0 by simp)
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
      hs, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  obtain ⟨b, hb⟩ := fraction_mem_of_faithfullyFlat R S K T i hi _ _ hs'
  have hab : a * b = 1 := by
    apply IsFractionRing.injective R K
    rw [map_mul, ha, hb, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, ha⟩

open Order TopologicalSpace

lemma functionFieldPullback_stalk
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsDominant f] (x : X) (r : Z.presheaf.stalk (f x)) :
    functionFieldPullback f (algebraMap (Z.presheaf.stalk (f x)) Z.functionField r) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x r) := by
  have he : Z.presheaf.stalkSpecializes ((genericPoint_spec Z).specializes trivial) ≫
      CommRingCat.ofHom (functionFieldPullback f) =
      f.stalkMap x ≫ X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) := by
    change Z.presheaf.stalkSpecializes _ ≫
      (Z.presheaf.stalkSpecializes _ ≫ f.stalkMap _) = _
    rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
    exact f.stalkSpecializes_stalkMap _ _ ((genericPoint_spec X).specializes trivial)
  exact congrArg (fun h => h r) he

 

theorem stalk_unit_of_flat_pullback_ord_zero
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X ⟶ Z) [IsDominant f] [Flat f]
    (U : Z.Opens) (u : Z.functionFieldˣ)
    (hord : ∀ x : X, f x ∈ U → coheight x = 1 →
      X.ord (functionFieldPullback f (u : Z.functionField)) x = 0)
    (x : X) (hx : f x ∈ U) :
    ∃ r : (Z.presheaf.stalk (f x))ˣ,
      algebraMap (Z.presheaf.stalk (f x)) Z.functionField (r : Z.presheaf.stalk (f x)) =
        (u : Z.functionField) := by
  let W := f ⁻¹ᵁ U
  let : Nonempty W := ⟨⟨x, hx⟩⟩
  let v := Units.map (functionFieldPullback f).toMonoidHom u
  obtain ⟨w, hw⟩ := exists_section_unit_of_ord_eq_zero X hNX W v hord
  let : Algebra (Z.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Module.FaithfullyFlat (Z.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  let s : (X.presheaf.stalk x)ˣ :=
    Units.map (X.presheaf.germ W x hx).hom.toMonoidHom w
  apply fraction_unit_of_faithfullyFlat (Z.presheaf.stalk (f x)) (X.presheaf.stalk x)
    Z.functionField X.functionField (functionFieldPullback f)
    (functionFieldPullback_stalk f x) u s
  change functionFieldPullback f (u : Z.functionField) =
    algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ W x hx (w : Γ(X, W)))
  rw [X.algebraMap_germ_eq_germToFunctionField hx]
  exact hw.symm

 
lemma ord_eq_zero_of_stalk_unit
    (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (hx : coheight x = 1) (r : (X.presheaf.stalk x)ˣ) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField (r : X.presheaf.stalk x)) x = 0 := by
  have hn : algebraMap (X.presheaf.stalk x) X.functionField (r : X.presheaf.stalk x) ≠ 0 :=
    by simp
  rw [X.ord_eq_iff hx hn]
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  exact Ring.ordFrac_of_isUnit r.isUnit

 

theorem pullbackQCartier_eq_zero_imp
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [Flat f] [Surjective f]
    (D : RationalWeilDivisor Z) (hD : IsQCartier Z D)
    (hzero : pullbackQCartier hNZ f D hD = 0) : D = 0 := by
  let c := hD.data
  ext p
  obtain ⟨x, hx⟩ := f.surjective p.1
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

end

 

theorem pullbackQCartier_injective
    {X Z : Scheme} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (hNX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hNZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (f : X ⟶ Z) [IsDominant f] [Flat f] [Surjective f]
    (D E : RationalWeilDivisor Z) (hD : IsQCartier Z D) (hE : IsQCartier Z E)
    (heq : pullbackQCartier hNZ f D hD = pullbackQCartier hNZ f E hE) : D = E := by
  have hneg := isQCartier_smul hE (-1)
  have hsub := isQCartier_add hD hneg
  have hz : pullbackQCartier hNZ f (D + (-1 : ℚ) • E) hsub = 0 := by
    rw [pullbackQCartier_add hNZ f hD hneg hsub,
      pullbackQCartier_smul hNZ f hE (-1) hneg, heq]
    simp
  have := pullbackQCartier_eq_zero_imp hNX hNZ f (D + (-1 : ℚ) • E) hsub hz
  simpa only [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] using this

attribute [local instance] Units.mulDistribMulActionRight

 

theorem principalization_descends_from_galois_extension
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [Module.Finite K L] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f] [IsProper f]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D : RationalWeilDivisor X) (hD : IsQCartier X D)
    (u : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))).functionFieldˣ)
    (hu : letI : IsNoetherian (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := {}
      rationalPrincipalDivisor _ u = pullbackQCartier hNormal (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) D hD) :
    ∃ v : X.functionFieldˣ, rationalPrincipalDivisor X v = D := by
  let XL := pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  let π := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  let : IsNoetherian XL := {}
  let := schemeBaseChangeGaloisAction K L f
  have hNL := galois_baseChange_normal K L f hNormal
  have hdiv (σ : Gal(L/K)) : principalDivisor XL (σ • u) = principalDivisor XL u := by
    have he : σ • u = Units.map (functionFieldPullback
        (scalarExtensionAutomorphism K L f σ)).toMonoidHom u := by
      apply Units.ext
      exact schemeBaseChangeGaloisAction_eq_pullback K L f σ (u : XL.functionField)
    rw [he]
    exact principalDivisor_eq_of_over_base hNL hNormal π
      (scalarExtensionAutomorphism K L f σ) (scalarExtensionAutomorphism_fst K L f σ)
      D hD u hu
  obtain ⟨v, hv⟩ := same_divisor_descends_from_galois_extension K L f hNormal u hdiv
  refine ⟨v, ?_⟩
  apply pullbackQCartier_injective hNL hNormal π
    (rationalPrincipalDivisor X v) D (isQCartier_principal X v) hD
  rw [pullbackQCartier_principal hNormal π v]
  rw [← hu]
  ext p
  change (principalDivisor XL (Units.map (functionFieldPullback π).toMonoidHom v) p : ℚ) =
    (principalDivisor XL u p : ℚ)
  exact_mod_cast DFunLike.congr_fun hv p

end RelativeDenominators
end

end OAI
