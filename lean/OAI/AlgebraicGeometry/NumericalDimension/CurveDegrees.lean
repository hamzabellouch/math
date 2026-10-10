import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.CurveOrders

namespace OAI

/-! Curve Degrees. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux
open AlgebraicGeometry CategoryTheory TopologicalSpace

abbrev PrimeDivisor (X : Scheme) := {x : X // Order.coheight x = 1}
abbrev WeilDivisor (X : Scheme) := PrimeDivisor X →₀ ℤ

def complexWeilDegree {X : Scheme} (D : WeilDivisor X) : ℤ := D.sum fun _ a => a

lemma coheight_eq_one_on_curve {C : Scheme} [IsIntegral C]
    (hdim : ∀ x : C, Order.coheight x ≤ 1) {x : C} (hx : x ≠ genericPoint C) :
    Order.coheight x = 1 := by
  apply le_antisymm (hdim x)
  have hxηlt : x < genericPoint C := lt_iff_le_not_ge.mpr
    ⟨genericPoint_specializes x, fun h => hx (Specializes.antisymm
      (show x ⤳ genericPoint C from h) (genericPoint_specializes x)).eq⟩
  calc
    (1 : ℕ∞) = 0 + 1 := by simp
    _ ≤ Order.coheight (genericPoint C) + 1 := add_le_add bot_le le_rfl
    _ ≤ Order.coheight x := Order.coheight_add_one_le hxηlt

lemma affine_point_of_nonzero_prime {C : Scheme} [IsIntegral C]
    (hdim : ∀ x : C, Order.coheight x ≤ 1)
    {U : C.Opens} [Nonempty U] (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(C, U)) (hq : q.asIdeal ≠ ⊥) :
    Order.coheight (hU.fromSpec q) = 1 := by
  apply coheight_eq_one_on_curve hdim
  intro he
  have h := hU.fromSpec.isOpenEmbedding.injective
    (he.trans (genericPoint_eq_of_isOpenImmersion hU.fromSpec).symm)
  rw [genericPoint_eq_bot_of_affine] at h
  exact hq (congrArg PrimeSpectrum.asIdeal h)

variable {C : Scheme} [IsIntegral C] [IsLocallyNoetherian C]
  (hdim : ∀ x : C, Order.coheight x ≤ 1)
  {U : C.Opens} [Nonempty U] (hU : IsAffineOpen U)
  [Algebra (Polynomial ℂ) Γ(C, U)]
  (hi : Function.Injective (algebraMap (Polynomial ℂ) Γ(C, U)))

noncomputable def polynomialFiberPoint (c : ℂ)
    (q : (polynomialPoint c).primesOver Γ(C, U)) : PrimeDivisor C := by
  let : FaithfulSMul (Polynomial ℂ) Γ(C, U) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hi
  refine ⟨hU.fromSpec ⟨q.1, inferInstance⟩,
    affine_point_of_nonzero_prime hdim hU ⟨q.1, inferInstance⟩ ?_⟩
  apply Ideal.ne_bot_of_mem_primesOver (p := polynomialPoint c) ?_ q.2
  exact Ideal.span_singleton_eq_bot.not.mpr (Polynomial.X_sub_C_ne_zero c)

omit [IsLocallyNoetherian C] in
lemma polynomialFiberPoint_injective (c : ℂ) :
    Function.Injective (polynomialFiberPoint hdim hU hi c) := by
  intro q r h
  apply Subtype.ext
  have hp : hU.fromSpec (⟨q.1, inferInstance⟩ : PrimeSpectrum Γ(C, U)) =
      hU.fromSpec (⟨r.1, inferInstance⟩ : PrimeSpectrum Γ(C, U)) :=
    congrArg (fun p : PrimeDivisor C => p.1) h
  exact congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective hp)

noncomputable def polynomialFiberDivisor (c : ℂ)
    [Fintype ((polynomialPoint c).primesOver Γ(C, U))] : WeilDivisor C :=
  ∑ q : (polynomialPoint c).primesOver Γ(C, U),
    Finsupp.single (polynomialFiberPoint hdim hU hi c q)
      ((Ring.ord (Localization.AtPrime q.1)
        (algebraMap (Polynomial ℂ) (Localization.AtPrime q.1)
          (Polynomial.X - Polynomial.C c))).toNat : ℤ)

omit [IsLocallyNoetherian C] in
lemma polynomialFiberDivisor_degree [Module.Finite (Polynomial ℂ) Γ(C, U)] (c : ℂ)
    [Fintype ((polynomialPoint c).primesOver Γ(C, U))] :
    complexWeilDegree (polynomialFiberDivisor hdim hU hi c) =
      (Module.finrank (Polynomial ℂ) Γ(C, U) : ℤ) := by
  classical
  unfold complexWeilDegree polynomialFiberDivisor
  rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp only [Finsupp.sum_single_index]
  exact_mod_cast polynomial_fiber_order_eq_rank hi c

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux
open AlgebraicGeometry CategoryTheory

lemma polynomial_liesOver_iff {k S : Type*} [Field k] [CommRing S]
    [Algebra (Polynomial k) S] (q : Ideal S) [q.IsPrime] (c : k) :
    q.LiesOver (polynomialPoint c) ↔
      algebraMap (Polynomial k) S (Polynomial.X - Polynomial.C c) ∈ q := by
  constructor
  · intro h
    let := h
    exact (q.mem_of_liesOver (polynomialPoint c) _).mp (Ideal.subset_span rfl)
  · intro h
    constructor
    apply Ideal.IsMaximal.eq_of_le (inferInstance : (polynomialPoint c).IsMaximal)
      (Ideal.IsPrime.ne_top (inferInstance : (q.under (Polynomial k)).IsPrime))
    exact (Ideal.span_singleton_le_iff_mem _).mpr h

variable {C : Scheme} [IsIntegral C] [IsLocallyNoetherian C]
  (hdim : ∀ x : C, Order.coheight x ≤ 1)
  {U : C.Opens} [Nonempty U] (hU : IsAffineOpen U)
  [Algebra (Polynomial ℂ) Γ(C, U)]
  (hi : Function.Injective (algebraMap (Polynomial ℂ) Γ(C, U)))

omit [IsLocallyNoetherian C] in
lemma polynomialFiberDivisor_apply_outside (c : ℂ)
    [Fintype ((polynomialPoint c).primesOver Γ(C, U))]
    (p : PrimeDivisor C) (hp : p.1 ∉ U) :
    polynomialFiberDivisor hdim hU hi c p = 0 := by
  classical
  simp only [polynomialFiberDivisor, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro q _
  apply Finsupp.single_eq_of_ne'
  intro he
  apply hp
  rw [← congrArg (fun p : PrimeDivisor C => p.1) he]
  exact (hU.isoSpec.inv (⟨q.1, inferInstance⟩ : PrimeSpectrum Γ(C, U))).2

lemma polynomialFiberDivisor_apply_inside (c : ℂ)
    [Fintype ((polynomialPoint c).primesOver Γ(C, U))]
    (p : PrimeDivisor C) (hp : p.1 ∈ U) :
    polynomialFiberDivisor hdim hU hi c p =
      C.ord (C.germToFunctionField U
        (algebraMap (Polynomial ℂ) Γ(C, U) (Polynomial.X - Polynomial.C c))) p.1 := by
  classical
  let x : U := ⟨p.1, hp⟩
  let q := hU.primeIdealOf x
  let a := algebraMap (Polynomial ℂ) Γ(C, U) (Polynomial.X - Polynomial.C c)
  have ha : a ≠ 0 := by
    simpa only [map_zero] using hi.ne (Polynomial.X_sub_C_ne_zero c)
  rw [scheme_order_on_affine_chart hU x p.2 a ha]
  by_cases hq : q.asIdeal.LiesOver (polynomialPoint c)
  · let q' : (polynomialPoint c).primesOver Γ(C, U) := ⟨q.asIdeal, q.isPrime, hq⟩
    have hpoint : polynomialFiberPoint hdim hU hi c q' = p := by
      apply Subtype.ext
      exact hU.fromSpec_primeIdealOf x
    simp only [polynomialFiberDivisor, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single q']
    · rw [hpoint, Finsupp.single_eq_same]
      congr 2
    · intro r _ hr
      apply Finsupp.single_eq_of_ne'
      intro he
      exact hr ((polynomialFiberPoint_injective hdim hU hi c) (he.trans hpoint.symm))
    · simp
  · have hnot : a ∉ q.asIdeal := (polynomial_liesOver_iff q.asIdeal c).not.mp hq
    have hunit : IsUnit (algebraMap Γ(C, U) (Localization.AtPrime q.asIdeal) a) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q.asIdeal)
        q.asIdeal a).mpr hnot
    rw [Ring.ord_of_isUnit hunit]
    simp only [ENat.toNat_zero, Nat.cast_zero, polynomialFiberDivisor, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro r _
    apply Finsupp.single_eq_of_ne'
    intro he
    have he' : hU.fromSpec (⟨r.1, inferInstance⟩ : PrimeSpectrum Γ(C, U)) =
        hU.fromSpec q := (congrArg (fun p : PrimeDivisor C => p.1) he).trans
          (hU.fromSpec_primeIdealOf x).symm
    have hrq : r.1 = q.asIdeal :=
      congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective he')
    exact hq (hrq ▸ r.2.2)
end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]

theorem finite_primeDivisors_in_closed {Z : Set X} (hZ : IsClosed Z)
    (hproper : Z ≠ Set.univ) :
    {p : PrimeDivisor X | p.1 ∈ Z}.Finite := by
  classical
  let : PartialOrder X := specializationOrder X
  let : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  obtain ⟨S, hSfinite, hSclosed, hSirr, hZS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  let : Fintype S := hSfinite.fintype
  let g : S → X := fun T => (hSirr T.1 T.2).genericPoint
  have hgen : genericPoint X ∉ Z := by
    intro h
    apply hproper
    exact Set.eq_univ_of_univ_subset
      (((genericPoint_spec X).mem_closed_set_iff hZ).mp h)
  have hfin : (Set.range g).Finite := Set.finite_range g
  apply ((hfin.preimage (f := fun p : PrimeDivisor X => p.1)
    Subtype.val_injective.injOn)).subset
  intro p hp
  obtain ⟨T, hT, hpT⟩ := Set.mem_sUnion.mp (hZS ▸ hp)
  let q := g ⟨T, hT⟩
  have hq : IsGenericPoint q T := (hSirr T hT).isGenericPoint_genericPoint (hSclosed T hT)
  have hqp : p.1 ≤ q := hq.specializes hpT
  have hqg : q < genericPoint X := by
    refine lt_of_le_of_ne (genericPoint_specializes q) ?_
    intro heq
    apply hgen
    rw [← heq, hZS]
    exact Set.mem_sUnion.mpr ⟨T, hT, hq.mem⟩
  have hqone : (1 : ℕ∞) ≤ Order.coheight q := by
    exact le_trans (by simp) (Order.coheight_add_one_le hqg)
  have hpq : p.1 = q := by
    by_contra hne
    have h := Order.coheight_add_one_le (lt_of_le_of_ne hqp hne)
    rw [p.2] at h
    have htwo : (2 : ℕ∞) ≤ 1 := (add_le_add hqone (le_refl (1 : ℕ∞))).trans h
    norm_num at htwo
  exact ⟨⟨T, hT⟩, hpq.symm⟩

theorem ord_finite_support (f : X.functionField) :
    (Function.support (fun p : PrimeDivisor X => X.ord f p.1)).Finite := by
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨U, _, f', hU, heq, hunit⟩ := exists_isUnit_germ_eq X f hf
  have hproper : (U : Set X)ᶜ ≠ Set.univ := by
    intro h
    obtain ⟨x⟩ := hU
    have hx : x.1 ∈ (U : Set X)ᶜ := by rw [h]; trivial
    exact hx x.2
  apply (finite_primeDivisors_in_closed U.isOpen.isClosed_compl hproper).subset
  intro p hp hpU
  apply hp
  rw [← heq]
  exact X.ord_of_isUnit hunit hpU

noncomputable def principalWeilDivisor (f : X.functionField) : WeilDivisor X :=
  Finsupp.ofSupportFinite (fun p => X.ord f p.1) (ord_finite_support f)

@[simp] theorem principalWeilDivisor_apply (f : X.functionField) (p : PrimeDivisor X) :
    principalWeilDivisor f p = X.ord f p.1 := rfl

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux
open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] complexAffineChart_isOpenImmersion

lemma dvr_stalk_of_smooth_curve {C : Scheme} [IsIntegral C] [IsLocallyNoetherian C]
    (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC]
    (p : PrimeDivisor C) : IsDiscreteValuationRing (C.presheaf.stalk p.1) := by
  let : Smooth sC := SmoothOfRelativeDimension.smooth 1 sC
  let : IsIntegrallyClosed (C.presheaf.stalk p.1) :=
    integrallyClosed_stalk_of_smooth_field sC p.1
  have hd : ringKrullDim (C.presheaf.stalk p.1) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, p.2]
    rfl
  have hnf : ¬ IsField (C.presheaf.stalk p.1) :=
    (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hd).1
  let : Ring.KrullDimLE 1 (C.presheaf.stalk p.1) := krullDimLE_of_coheight_le p.2.le
  let : Ring.DimensionLEOne (C.presheaf.stalk p.1) :=
    ⟨fun {I} hI hprime =>
      Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance I hI hprime⟩
  let : IsDedekindDomain (C.presheaf.stalk p.1) := { }
  exact ((IsDiscreteValuationRing.TFAE (C.presheaf.stalk p.1) hnf).out 3 1).mp
    (show IsDedekindDomain (C.presheaf.stalk p.1) from inferInstance)

lemma curve_scalar_order_zero {C : Scheme} [IsIntegral C] [IsLocallyNoetherian C]
    (sC : C ⟶ Spec (.of ℂ)) (c : ℂ) (p : PrimeDivisor C) :
    C.ord (curveFieldScalar sC c) p.1 = 0 := by
  by_cases hc : c = 0
  · simp [hc]
  have hu : IsUnit (curveStalkScalar sC p.1 c) := (isUnit_iff_ne_zero.mpr hc).map _
  have he : algebraMap (C.presheaf.stalk p.1) C.functionField
      (curveStalkScalar sC p.1 c) = curveFieldScalar sC c :=
    congrArg (fun g : ℂ →+* C.functionField => g c) (curveStalkScalar_comp_field sC p.1)
  rw [← he, scheme_order_of_stalk_element p.1 p.2 _ hu.ne_zero, Ring.ord_of_isUnit hu]
  rfl

lemma affine_polynomial_germ {C : Scheme} [IsIntegral C]
    (sC : C ⟶ Spec (.of ℂ)) (b : C.functionField)
    (U : C.Opens) (hη : genericPoint C ∈ U)
    (α : .of (Polynomial ℂ) ⟶ Γ(C, U))
    (hαg : α ≫ C.presheaf.germ U (genericPoint C) hη =
      CommRingCat.ofHom (curveFunctionPolynomial sC b))
    [Nonempty U] (c : ℂ) :
    C.germToFunctionField U (α (Polynomial.X - Polynomial.C c)) =
      b - curveFieldScalar sC c := by
  have h := congrArg (fun β : .of (Polynomial ℂ) ⟶ C.functionField =>
    β (Polynomial.X - Polynomial.C c)) hαg
  change C.germToFunctionField U (α (Polynomial.X - Polynomial.C c)) =
    Polynomial.eval₂RingHom (curveFieldScalar sC) b (Polynomial.X - Polynomial.C c) at h
  simpa only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_C] using h

theorem proper_curve_principal_degree_zero {C : Scheme} [IsIntegral C]
    [IsLocallyNoetherian C] [CompactSpace C] [NoetherianSpace C]
    (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC] [IsProper sC]
    (a : C.functionField) : complexWeilDegree (principalWeilDivisor a) = 0 := by
  classical
  by_cases ha : a ∈ Set.range (curveFieldScalar sC)
  · obtain ⟨c, rfl⟩ := ha
    have hz : principalWeilDivisor (curveFieldScalar sC c) = 0 := by
      ext p
      exact curve_scalar_order_zero sC c p
    rw [hz]
    rfl
  have ha1 : a - 1 ≠ 0 := by
    intro he
    apply ha
    refine ⟨1, ?_⟩
    simpa only [map_one] using (sub_eq_zero.mp he).symm
  let b : C.functionField := (a - 1)⁻¹
  have hb : b ∉ Set.range (curveFieldScalar sC) := by
    rintro ⟨c, hc⟩
    apply ha
    refine ⟨1 + c⁻¹, ?_⟩
    rw [map_add, map_one, map_inv₀, hc]
    dsimp [b]
    rw [inv_inv]
    ring
  have hb0 : b ≠ 0 := inv_ne_zero ha1
  have hbp1 : b + 1 ≠ 0 := by
    intro he
    apply hb
    refine ⟨-1, ?_⟩
    simp only [map_neg, map_one]
    exact (eq_neg_of_add_eq_zero_left he).symm
  have hab : a = (b + 1) / b := by
    dsimp [b]
    field_simp
    ring
  obtain ⟨f, U, hU, hη, α, hf, hUf, hαfin, hαinj, hαg, _hαf⟩ :=
    exists_finite_polynomial_presentation sC hb
  let : Nonempty U := ⟨⟨genericPoint C, hη⟩⟩
  let : Algebra (Polynomial ℂ) Γ(C, U) := α.hom.toAlgebra
  let : Module.Finite (Polynomial ℂ) Γ(C, U) := hαfin
  let (c : ℂ) : Fintype ((polynomialPoint c).primesOver Γ(C, U)) :=
    (Algebra.QuasiFinite.finite_primesOver (R := Polynomial ℂ) (S := Γ(C, U))
      (polynomialPoint c)).fintype
  let hdim := coheight_le_of_smooth_dimension sC 1
  let F : ℂ → WeilDivisor C := fun c => polynomialFiberDivisor hdim hU hαinj c
  have hdiff : principalWeilDivisor a = F (-1) - F 0 := by
    ext p
    change C.ord a p.1 = F (-1) p - F 0 p
    rw [hab, order_div _ _ hbp1 hb0]
    dsimp only [F]
    by_cases hp : p.1 ∈ U
    · rw [polynomialFiberDivisor_apply_inside hdim hU hαinj (-1) p hp,
        polynomialFiberDivisor_apply_inside hdim hU hαinj 0 p hp]
      change C.ord (b + 1) p.1 - C.ord b p.1 =
        C.ord (C.germToFunctionField U (α (Polynomial.X - Polynomial.C (-1)))) p.1 -
        C.ord (C.germToFunctionField U (α (Polynomial.X - Polynomial.C 0))) p.1
      rw [affine_polynomial_germ sC b U hη α hαg,
        affine_polynomial_germ sC b U hη α hαg]
      simp
    · rw [polynomialFiberDivisor_apply_outside hdim hU hαinj (-1) p hp,
        polynomialFiberDivisor_apply_outside hdim hU hαinj 0 p hp, sub_zero]
      let : IsDiscreteValuationRing (C.presheaf.stalk p.1) := dvr_stalk_of_smooth_curve sC p
      have hneg : C.ord b p.1 < 0 := by
        apply lt_of_not_ge
        intro ho
        obtain ⟨v, hv⟩ := (order_nonnegative_iff_local p.2 b hb0).mp ho
        apply hp
        rw [hUf]
        exact curveFunction_mem_chart_of_regular sC b f hf p.1 v hv
      rw [order_add_one_of_negative hneg, sub_self]
  rw [hdiff]
  change (F (-1) - F 0).sum (fun _ a => a) = 0
  rw [Finsupp.sum_sub_index (fun _ _ _ => rfl)]
  change complexWeilDegree (F (-1)) - complexWeilDegree (F 0) = 0
  rw [polynomialFiberDivisor_degree hdim hU hαinj,
    polynomialFiberDivisor_degree hdim hU hαinj, sub_self]
end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOne

lemma pulledCartierRepresentative_difference {C Y : Scheme}
    [IsIntegral C] [IsIntegral Y] [IsLocallyNoetherian C] [IsLocallyNoetherian Y]
    [CompactSpace C] [StalkwiseNormal Y]
    {f : C ⟶ Y} {D : WeilDivisor Y} {E F : WeilDivisor C}
    (hE : IsPulledCartierRepresentative f D E)
    (hF : IsPulledCartierRepresentative f D F) :
    ∃ a : C.functionField, a ≠ 0 ∧ E = F + principalWeilDivisor a := by
  obtain ⟨U, _, hU, g, hg, hDg, hEloc⟩ := hE
  obtain ⟨V, _, hV, h, hh, hDh, hFloc⟩ := hF
  obtain ⟨a, ha, hea⟩ := local_equation_ratio_unit hh hg hDh hDg hV hU
  refine ⟨f.stalkMap (genericPoint C) a,
    (ha.map (f.stalkMap (genericPoint C)).hom).ne_zero, ?_⟩
  ext p
  obtain ⟨U', _, hpU, g', hg', hDg', b, hb, heb, hEb⟩ := hEloc p.1
  obtain ⟨V', _, hpV, h', hh', hDh', c, hc, hec, hFc⟩ := hFloc p.1
  have heca : algebraMap _ Y.functionField (c * a) = h' / g := by
    rw [map_mul, hec, hea]
    field_simp
  have heq := curve_equation_order_eq f hg' hh' hg hDg' hDh' b (c * a)
    (hc.mul ha) heb heca p hpU hpV
  rw [map_mul, C.ord_mul
    (hc.map (f.stalkMap (genericPoint C)).hom).ne_zero
    (ha.map (f.stalkMap (genericPoint C)).hom).ne_zero] at heq
  simpa only [Finsupp.add_apply, principalWeilDivisor_apply, hEb p hpU, hFc p hpV]
    using heq

lemma principal_degree_zero (C : ComplexProjectiveVariety) (hC : IsSmoothNfold C 1)
    (a : C.scheme.functionField) : complexWeilDegree (principalWeilDivisor a) = 0 := by
  let : SmoothOfRelativeDimension 1 C.structureMap := hC
  let : AlgebraicGeometry.IsNoetherian C.scheme := ⟨⟩
  exact NumericalDimensionOneCurveAux.proper_curve_principal_degree_zero C.structureMap a

lemma pulledCartierRepresentative_degree_eq {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] (C : CurveOn X) {D : WeilDivisor X.scheme}
    {E F : WeilDivisor C.curve.scheme}
    (hE : IsPulledCartierRepresentative C.morphism D E)
    (hF : IsPulledCartierRepresentative C.morphism D F) :
    complexWeilDegree E = complexWeilDegree F := by
  classical
  obtain ⟨a, _, rfl⟩ := pulledCartierRepresentative_difference hE hF
  change (F + principalWeilDivisor a).sum (fun _ a => a) = _
  rw [Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl)]
  change complexWeilDegree F + complexWeilDegree (principalWeilDivisor a) = _
  rw [principal_degree_zero C.curve C.smooth, add_zero]

lemma divisor_degree_nonnegative (C : ComplexProjectiveVariety) (hC : IsSmoothNfold C 1)
    (D : WeilDivisor C.scheme) (a : C.scheme.functionField) (ha : a ≠ 0)
    (hsec : IsDivisorSection D a) : 0 ≤ complexWeilDegree D := by
  classical
  have hpoint (p : PrimeDivisor C.scheme) : 0 ≤ (principalWeilDivisor a + D) p := by
    exact (hsec.resolve_left ha) p
  have hdeg : 0 ≤ complexWeilDegree (principalWeilDivisor a + D) := by
    exact Finset.sum_nonneg (fun p _ => hpoint p)
  change 0 ≤ (principalWeilDivisor a + D).sum (fun _ a => a) at hdeg
  rw [Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl)] at hdeg
  change 0 ≤ complexWeilDegree (principalWeilDivisor a) + complexWeilDegree D at hdeg
  simpa only [principal_degree_zero C hC, zero_add] using hdeg

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOne

lemma IsPulledCartierRepresentative.add {C Y : Scheme}
    [IsIntegral C] [IsIntegral Y] [IsLocallyNoetherian C] [IsLocallyNoetherian Y]
    {f : C ⟶ Y} {D₁ D₂ : WeilDivisor Y} {E₁ E₂ : WeilDivisor C}
    (h₁ : IsPulledCartierRepresentative f D₁ E₁)
    (h₂ : IsPulledCartierRepresentative f D₂ E₂) :
    IsPulledCartierRepresentative f (D₁ + D₂) (E₁ + E₂) := by
  obtain ⟨U, _, hU, g, hg, hDg, hEloc⟩ := h₁
  obtain ⟨V, _, hV, h, hh, hDh, hFloc⟩ := h₂
  obtain ⟨W, hW, hyW, hWUV⟩ := exists_isAffineOpen_mem_and_subset
    (show f (genericPoint C) ∈ U ⊓ V from ⟨hU, hV⟩)
  refine ⟨W, hW, hyW, g * h, mul_ne_zero hg hh, ?_, ?_⟩
  · intro p hp
    rw [Finsupp.add_apply, hDg p (hWUV hp).1, hDh p (hWUV hp).2,
      Y.ord_mul hg hh]
  · intro x
    obtain ⟨U', _, hxU, g', hg', hDg', b, hb, heb, hEb⟩ := hEloc x
    obtain ⟨V', _, hxV, h', hh', hDh', c, hc, hec, hFc⟩ := hFloc x
    obtain ⟨W', hW', hxW', hWUV'⟩ := exists_isAffineOpen_mem_and_subset
      (show f x ∈ U' ⊓ V' from ⟨hxU, hxV⟩)
    refine ⟨W', hW', hxW', g' * h', mul_ne_zero hg' hh', ?_,
      b * c, hb.mul hc, ?_, ?_⟩
    · intro p hp
      rw [Finsupp.add_apply, hDg' p (hWUV' hp).1, hDh' p (hWUV' hp).2,
        Y.ord_mul hg' hh']
    · rw [map_mul, heb, hec]
      exact div_mul_div_comm g' g h' h
    · intro p hp
      rw [Finsupp.add_apply, hEb p (hWUV' hp).1, hFc p (hWUV' hp).2, map_mul,
        C.ord_mul (hb.map (f.stalkMap (genericPoint C)).hom).ne_zero
          (hc.map (f.stalkMap (genericPoint C)).hom).ne_zero]

lemma isPulledCartierRepresentative_zero {C Y : Scheme}
    [IsIntegral C] [IsIntegral Y] [IsLocallyNoetherian C] [IsLocallyNoetherian Y]
    (f : C ⟶ Y) : IsPulledCartierRepresentative f 0 0 := by
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f (genericPoint C) ∈ (⊤ : Y.Opens) from trivial)
  refine ⟨U, hU, hyU, 1, one_ne_zero, ?_, ?_⟩
  · intro p _
    simp only [Finsupp.zero_apply, order_one]
  · intro x
    obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show f x ∈ (⊤ : Y.Opens) from trivial)
    refine ⟨V, hV, hxV, 1, one_ne_zero, ?_, 1, isUnit_one, ?_, ?_⟩
    · intro p _
      simp only [Finsupp.zero_apply, order_one]
    · simp only [map_one, div_one]
    · intro p _
      simp only [Finsupp.zero_apply, map_one, order_one]

lemma cartierCurveDegree_add {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    (D E : cartierDivisors (X := X.scheme)) (C : CurveOn X) :
    cartierCurveDegree (D + E) C = cartierCurveDegree D C + cartierCurveDegree E C := by
  classical
  rw [cartierCurveDegree, pulledCartierRepresentative_degree_eq C
    (pulledCartierRepresentative_spec C (D + E).1 (D + E).2)
    ((pulledCartierRepresentative_spec C D.1 D.2).add
      (pulledCartierRepresentative_spec C E.1 E.2))]
  exact Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl)

lemma cartierCurveDegree_zero {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    (C : CurveOn X) : cartierCurveDegree 0 C = 0 := by
  change complexWeilDegree (pulledCartierRepresentative C 0 isCartierDivisor_zero) = 0
  rw [pulledCartierRepresentative_degree_eq C
    (pulledCartierRepresentative_spec C 0 isCartierDivisor_zero)
    (isPulledCartierRepresentative_zero C.morphism)]
  rfl

noncomputable def cartierCurveDegreeHom {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] (C : CurveOn X) : cartierDivisors (X := X.scheme) →+ ℤ where
  toFun D := cartierCurveDegree D C
  map_zero' := cartierCurveDegree_zero C
  map_add' D E := cartierCurveDegree_add D E C

end NumericalDimensionOne

end OAI
