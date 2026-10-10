import OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite
import OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula
import OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter
import OAI.NumberTheory.PiExponent.Jets.DVRBranchJet
import OAI.NumberTheory.PiExponent.Polynomials.WeightedPolynomialPole

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveContactSum

open WeightedPolynomialPole WeightedCurveDegree CurveValuationCenter PolynomialPoleBound

theorem contact_sum_le_of_principal_sum
    {P : Type*} (z : P →₀ ℤ) (pole : P →₀ ℚ)
    (hz : z.sum (fun _ n => n) = 0) (hpole_nonneg : ∀ p, 0 ≤ pole p)
    (S : Finset P) (μ : P → ℝ) (N B : ℝ) (hN : 0 ≤ N)
    (hlocal : ∀ p ∈ S, B * μ p ≤ (z p : ℝ))
    (hglobal : ∀ p, -N * (pole p : ℝ) ≤ (z p : ℝ)) :
    B * (∑ p ∈ S, μ p) ≤ N * pole.sum (fun _ n => (n : ℝ)) := by
  classical
  let T := S ∪ z.support ∪ pole.support
  have hST : S ⊆ T := by intro p hp; simp [T, hp]
  have hzT : z.support ⊆ T := by intro p hp; simp [T, hp]
  have hpT : pole.support ⊆ T := by intro p hp; simp [T, hp]
  have hzsum : (∑ p ∈ T, (z p : ℝ)) = 0 := by
    have hh := z.sum_of_support_subset hzT (fun _ n => n) (by simp)
    have hi : (∑ p ∈ T, z p) = 0 := hh.symm.trans hz
    exact_mod_cast hi
  have hpsum : (∑ p ∈ T, (pole p : ℝ)) = pole.sum (fun _ n => (n : ℝ)) :=
    (pole.sum_of_support_subset hpT (fun _ n => (n : ℝ)) (by simp)).symm
  calc
    B * (∑ p ∈ S, μ p) = ∑ p ∈ S, B * μ p := Finset.mul_sum _ _ _
    _ ≤ ∑ p ∈ S, ((z p : ℝ) + N * (pole p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact (hlocal p hp).trans (le_add_of_nonneg_right
        (mul_nonneg hN (by exact_mod_cast hpole_nonneg p)))
    _ ≤ ∑ p ∈ T, ((z p : ℝ) + N * (pole p : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hST
      intro p hp hnot
      have hh := hglobal p
      linarith
    _ = N * pole.sum (fun _ n => (n : ℝ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzsum, zero_add, hpsum]

theorem contact_sum_le_div_of_principal_sum
    {P : Type*} (z : P →₀ ℤ) (pole : P →₀ ℚ)
    (hz : z.sum (fun _ n => n) = 0) (hpole_nonneg : ∀ p, 0 ≤ pole p)
    (S : Finset P) (μ : P → ℝ) (N B : ℝ) (hN : 0 ≤ N) (hB : 0 < B)
    (hlocal : ∀ p ∈ S, B * μ p ≤ (z p : ℝ))
    (hglobal : ∀ p, -N * (pole p : ℝ) ≤ (z p : ℝ)) :
    (∑ p ∈ S, μ p) ≤ N / B * pole.sum (fun _ n => (n : ℝ)) := by
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hB).mpr
  simpa only [mul_comm B] using
    contact_sum_le_of_principal_sum z pole hz hpole_nonneg S μ N B hN hlocal hglobal

theorem coordinatePole_eq_zero {E ι : Type*} [Field E] [Fintype ι]
    (v : AddValuation E (WithTop ℤ)) (x : ι → E) (w : ι → ℚ)
    (hx : ∀ i, coordinateOrder v (x i) = 0) : coordinatePole v x w = 0 := by
  unfold coordinatePole weightedPole
  simp only [hx, Int.cast_zero, neg_zero, zero_div]
  have he : (fun i : Option ι => i.elim 0 (fun _ => (0 : ℚ))) = fun _ => 0 := by
    funext i
    cases i <;> rfl
  rw [he]
  exact Finset.sup'_const _ _

theorem coordinatePole_finite_support {E ι P : Type*} [Field E] [Fintype ι]
    (v : P → AddValuation E (WithTop ℤ)) (x : ι → E) (w : ι → ℚ)
    (hfinite : ∀ i, Set.Finite {p | coordinateOrder (v p) (x i) ≠ 0}) :
    Set.Finite {p | coordinatePole (v p) x w ≠ 0} := by
  have hu : Set.Finite (⋃ i, {p | coordinateOrder (v p) (x i) ≠ 0}) :=
    Set.finite_iUnion (fun i => hfinite i)
  apply hu.subset
  intro p hp
  by_contra hn
  apply hp
  apply coordinatePole_eq_zero
  intro i
  by_contra hi
  exact hn (Set.mem_iUnion.mpr ⟨i,hi⟩)

theorem exists_constant_of_isAlgebraic {E : Type*} [Field E] [Algebra ℂ E]
    (f : E) (hf : IsAlgebraic ℂ f) : ∃ c : ℂ, algebraMap ℂ E c = f := by
  have hm : f ∈ algebraicClosure ℂ E := mem_algebraicClosure_iff.mpr hf
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure ℂ E)] at hm
  exact hm

theorem frameWord_field_order_lower
    {A E : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]
    [Field E] [Algebra A E] [IsFractionRing A E] [Algebra ℂ E] [IsScalarTower ℂ A E]
    {m : ℕ} (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : PiExponentApprox.FramePolynomial m)
    (hp : FormalLogJet.formalJet c p ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval (Fin.cases (algebraMap A E y) (fun i => algebraMap A E (x i)))
      (PiExponentApprox.polynomialFrameWord m word p) ≠ 0) :
    DVRBranchJet.contact v c y x hnc * (H - (word.map v).sum) ≤
      (integerOrder (CurveLocalOrder.fractionAddValuation A E)
        (Units.mk0 (MvPolynomial.aeval
          (Fin.cases (algebraMap A E y) (fun i => algebraMap A E (x i)))
          (PiExponentApprox.polynomialFrameWord m word p)) hne) : ℚ) := by
  have he (q : PiExponentApprox.FramePolynomial m) :
      algebraMap A E (MvPolynomial.aeval (Fin.cases y x) q) =
        MvPolynomial.aeval (Fin.cases (algebraMap A E y) (fun i => algebraMap A E (x i))) q := by
    have hh := MvPolynomial.comp_aeval_apply (f := Fin.cases y x)
      (IsScalarTower.toAlgHom ℂ A E) q
    exact hh.trans (congrArg (fun z => MvPolynomial.aeval z q) (by
      funext i
      cases i using Fin.cases <;> rfl))
  have hn : MvPolynomial.aeval (Fin.cases y x)
      (PiExponentApprox.polynomialFrameWord m word p) ≠ 0 := by
    intro hz
    apply hne
    rw [← he, hz, map_zero]
  have hlen := CurveLocalOrder.integerOrder_field_image_eq_length (K := E) hn
  have hu : Units.mk0 (MvPolynomial.aeval
      (Fin.cases (algebraMap A E y) (fun i => algebraMap A E (x i)))
      (PiExponentApprox.polynomialFrameWord m word p)) hne =
      Units.mk0 (algebraMap A E (MvPolynomial.aeval (Fin.cases y x)
        (PiExponentApprox.polynomialFrameWord m word p)))
        ((map_ne_zero_iff _ (IsFractionRing.injective A E)).mpr hn) := by
    apply Units.ext
    exact (he _).symm
  rw [hu, hlen]
  simpa only [Int.cast_natCast] using
    DVRBranchJet.frameWord_colength_lower v hv H c y x hy hx hnc p hp word hn

theorem coordinateOrder_constant_eq_zero {E : Type*} [Field E] [Algebra ℂ E]
    (p : NormalizedPlace ℂ E) (c : ℂ) : coordinateOrder p.valuation (algebraMap ℂ E c) = 0 := by
  by_cases hc : c = 0
  · simp [hc, coordinateOrder]
  have hm : algebraMap ℂ E c ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hc
  rw [coordinateOrder, dite_eq_right hm]
  exact CurveProductFormula.placeOrder_constant_eq_zero p c hc

def coordinateOrderDivisor {E : Type*} [Field E] [Algebra ℂ E]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (f : E) : NormalizedPlace ℂ E →₀ ℤ := by
  classical
  exact if ht : Transcendental ℂ f then
    letI := hfinite f ht
    CurveProductFormula.principalDivisor f ht
  else 0

@[simp] theorem coordinateOrderDivisor_apply {E : Type*} [Field E] [Algebra ℂ E]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (f : E) (p : NormalizedPlace ℂ E) :
    coordinateOrderDivisor hfinite f p = coordinateOrder p.valuation f := by
  classical
  by_cases ht : Transcendental ℂ f
  · let := hfinite f ht
    simp only [coordinateOrderDivisor, dite_eq_left ht, CurveProductFormula.principalDivisor_apply,
      coordinateOrder, dite_eq_right ht.ne_zero]
    rfl
  · rw [coordinateOrderDivisor, dite_eq_right ht]
    obtain ⟨c,rfl⟩ := exists_constant_of_isAlgebraic f (not_not.mp ht)
    exact (coordinateOrder_constant_eq_zero p c).symm

theorem coordinateOrderDivisor_degree_zero {E : Type*} [Field E] [Algebra ℂ E]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (f : E) : (coordinateOrderDivisor hfinite f).sum (fun _ n => n) = 0 := by
  classical
  by_cases ht : Transcendental ℂ f
  · let := hfinite f ht
    rw [coordinateOrderDivisor, dite_eq_left ht]
    exact CurveProductFormula.principalDivisor_degree_zero f ht
  · simp [coordinateOrderDivisor, ht]

def weightedPoleDivisor {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) : NormalizedPlace ℂ E →₀ ℚ :=
  Finsupp.ofSupportFinite (fun p => coordinatePole p.valuation x w)
    (coordinatePole_finite_support (fun p : NormalizedPlace ℂ E => p.valuation) x w (by
      intro i
      simpa only [Function.HasFiniteSupport, Function.support, coordinateOrderDivisor_apply] using
        (coordinateOrderDivisor hfinite (x i)).hasFiniteSupport))

@[simp] theorem weightedPoleDivisor_apply {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) (p : NormalizedPlace ℂ E) :
    weightedPoleDivisor hfinite x w p = coordinatePole p.valuation x w := rfl

def weightedDegree {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) : ℝ :=
  (weightedPoleDivisor hfinite x w).sum (fun _ n => (n : ℝ))

theorem weightedDegree_nonneg {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) : 0 ≤ weightedDegree hfinite x w := by
  apply Finset.sum_nonneg
  intro p hp
  change (0 : ℝ) ≤ (coordinatePole p.valuation x w : ℚ)
  exact_mod_cast weightedPole_nonneg w (fun i => (coordinateOrder p.valuation (x i) : ℚ))

theorem constants_real_nonneg {E : Type*} [Field E] [Algebra ℂ E]
    (p : NormalizedPlace ℂ E) (c : ℂ) :
    0 ≤ realValuation p.valuation (algebraMap ℂ E c) := by
  have h := (show Monotone (WithTop.map (fun z : ℤ => (z : ℝ))) from
    (Int.cast_mono (R := ℝ)).withTop_map) (p.constants_nonneg c)
  have hz : WithTop.map (fun z : ℤ => (z : ℝ)) (0 : WithTop ℤ) = (0 : WithTop ℝ) := by
    change (((0 : ℤ) : ℝ) : WithTop ℝ) = 0
    norm_num
  rw [hz] at h
  exact h

theorem polynomial_order_lower {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (x : ι → E) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (N : ℝ)
    (f : MvPolynomial ι ℂ)
    (hdegree : ∀ d ∈ f.support, Finsupp.weight (fun i => (w i : ℝ)) d ≤ N)
    (hne : MvPolynomial.aeval x f ≠ 0) (p : NormalizedPlace ℂ E) :
    -N * (coordinatePole p.valuation x w : ℝ) ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℝ) := by
  have h := PolynomialPoleBound.polynomial_order_lower (realValuation p.valuation) x
    (fun i => (w i : ℝ)) (coordinatePole p.valuation x w : ℝ) N
    (by exact_mod_cast weightedPole_nonneg w (fun i => (coordinateOrder p.valuation (x i) : ℚ)))
    (coordinate_order_lower p.valuation x w hw) (constants_real_nonneg p) f hdegree
  rw [realValuation_of_ne_zero _ _ hne] at h
  exact WithTop.coe_le_coe.mp h

theorem polynomial_contact_sum_le {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (N B : ℝ) (hN : 0 ≤ N)
    (f : MvPolynomial ι ℂ)
    (hdegree : ∀ d ∈ f.support, Finsupp.weight (fun i => (w i : ℝ)) d ≤ N)
    (hne : MvPolynomial.aeval x f ≠ 0)
    (S : Finset (NormalizedPlace ℂ E)) (μ : NormalizedPlace ℂ E → ℝ)
    (hlocal : ∀ p ∈ S, B * μ p ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℝ)) :
    B * (∑ p ∈ S, μ p) ≤ N * weightedDegree hfinite x w := by
  refine contact_sum_le_of_principal_sum
    (coordinateOrderDivisor hfinite (MvPolynomial.aeval x f)) (weightedPoleDivisor hfinite x w)
    (coordinateOrderDivisor_degree_zero hfinite _) ?_ S μ N B hN ?_ ?_
  · intro p
    exact weightedPole_nonneg w (fun i => (coordinateOrder p.valuation (x i) : ℚ))
  · intro p hp
    simpa only [coordinateOrderDivisor_apply] using hlocal p hp
  · intro p
    simpa only [weightedPoleDivisor_apply, coordinateOrderDivisor_apply] using
      polynomial_order_lower x w hw N f hdegree hne p

theorem polynomial_contact_sum_le_div {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (N B : ℝ) (hN : 0 ≤ N) (hB : 0 < B)
    (f : MvPolynomial ι ℂ)
    (hdegree : ∀ d ∈ f.support, Finsupp.weight (fun i => (w i : ℝ)) d ≤ N)
    (hne : MvPolynomial.aeval x f ≠ 0)
    (S : Finset (NormalizedPlace ℂ E)) (μ : NormalizedPlace ℂ E → ℝ)
    (hlocal : ∀ p ∈ S, B * μ p ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℝ)) :
    (∑ p ∈ S, μ p) ≤ N / B * weightedDegree hfinite x w := by
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hB).mpr
  simpa only [mul_comm B] using
    polynomial_contact_sum_le hfinite x w hw N B hN f hdegree hne S μ hlocal

theorem polynomial_eq_zero_of_excess_contact
    {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (N B : ℝ) (hN : 0 ≤ N)
    (f : MvPolynomial ι ℂ)
    (hdegree : ∀ d ∈ f.support, Finsupp.weight (fun i => (w i : ℝ)) d ≤ N)
    (S : Finset (NormalizedPlace ℂ E)) (μ : NormalizedPlace ℂ E → ℝ)
    (hlocal : MvPolynomial.aeval x f ≠ 0 → ∀ p ∈ S, B * μ p ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℝ))
    (hexcess : N * weightedDegree hfinite x w < B * (∑ p ∈ S, μ p)) :
    MvPolynomial.aeval x f = 0 := by
  by_contra hne
  exact (not_le_of_gt hexcess)
    (polynomial_contact_sum_le hfinite x w hw N B hN f hdegree hne S μ (hlocal hne))

end PiExponent.CurveContactSum

end

end OAI
