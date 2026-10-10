import Mathlib
import OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open PiExponent.WeightedCurveDegree PiExponent.CurveLocalOrder

namespace PiExponent.WeightedLocalLattice

theorem exists_local_element_iff_nonnegative_order
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] (x : K) :
    (∃ a : A, algebraMap A K a = x) ↔ 0 ≤ fractionAddValuation A K x := by
  constructor
  · rintro ⟨a, rfl⟩
    rw [fractionAddValuation_algebraMap, localAddValuation_apply]
    have h := enatToIntegerOrder_monotone (show (0 : ℕ∞) ≤ IsDiscreteValuationRing.addVal A a from bot_le)
    simpa using h
  · intro hx
    by_cases hx0 : x = 0
    · exact ⟨0, by simp [hx0]⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
    have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    have ha0 : a ≠ 0 := by
      intro ha
      apply hx0
      simp [ha]
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
      (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr ha0)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
      (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hb0)
    rw [AddValuation.map_div, fractionAddValuation_algebraMap,
      fractionAddValuation_algebraMap, localAddValuation_apply,
      localAddValuation_apply, ← hm, ← hn] at hx
    change (0 : WithTop ℤ) ≤ ((m : ℤ) : WithTop ℤ) - ((n : ℤ) : WithTop ℤ) at hx
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_zero, WithTop.coe_le_coe] at hx
    have hnm : n ≤ m := by exact_mod_cast (sub_nonneg.mp hx)
    have hdvd : b ∣ a := IsDiscreteValuationRing.addVal_le_iff_dvd.mp (by
      rw [← hm, ← hn]
      exact_mod_cast hnm)
    obtain ⟨c, rfl⟩ := hdvd
    refine ⟨c, ?_⟩
    rw [map_mul, mul_div_cancel_left₀]
    exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hb0

def generatedLattice
    (A : Type*) {K ι : Type*} [CommRing A] [Field K] [Algebra A K]
    (y : ι → K) (s : Finset ι) : Submodule A K :=
  Submodule.span A {z | ∃ i ∈ s, z = y i}

theorem generatedLattice_eq_span_of_minimum
    {A K ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) (hya : y a ≠ 0)
    (hmin : ∀ b ∈ s, fractionAddValuation A K (y a) ≤ fractionAddValuation A K (y b)) :
    generatedLattice A y s = Submodule.span A {y a} := by
  have hva : fractionAddValuation A K (y a) ≠ ⊤ :=
    (AddValuation.top_iff _).not.mpr hya
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨b, hb, rfl⟩
    have hv : 0 ≤ fractionAddValuation A K (y b / y a) := by
      rw [AddValuation.map_div]
      calc
        0 = fractionAddValuation A K (y a) - fractionAddValuation A K (y a) :=
          (LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top hva).symm
        _ ≤ fractionAddValuation A K (y b) - fractionAddValuation A K (y a) :=
          (LinearOrderedAddCommGroupWithTop.sub_left_strictMono_of_ne_top hva).monotone (hmin b hb)
    obtain ⟨c, hc⟩ := (exists_local_element_iff_nonnegative_order _).mpr hv
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    rw [Algebra.smul_def, hc]
    exact div_mul_cancel₀ _ hya
  · apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact Submodule.subset_span ⟨a, ha, rfl⟩

theorem generatedLattice_rank_one_of_minimum
    {A K ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) (hya : y a ≠ 0)
    (hmin : ∀ b ∈ s, fractionAddValuation A K (y a) ≤ fractionAddValuation A K (y b)) :
    Nonempty (A ≃ₗ[A] generatedLattice A y s) := by
  rw [generatedLattice_eq_span_of_minimum y s a ha hya hmin]
  exact ⟨LinearEquiv.toSpanNonzeroSingleton A K _ hya⟩

def monomialLattice
    (A : Type*) {K ι : Type*} [CommRing A] [Field K] [Algebra A K]
    [Fintype ι] (x : ι → Kˣ) (monomials : Finset (ι → ℕ)) : Submodule A K :=
  Submodule.span A {y | ∃ a ∈ monomials, y = ((∏ i, x i ^ a i : Kˣ) : K)}

theorem exists_monomialLattice_generator
    {A K ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Fintype ι]
    (x : ι → Kˣ) (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials) :
    ∃ a ∈ monomials,
      monomialLattice A x monomials =
        Submodule.span A {((∏ i, x i ^ a i : Kˣ) : K)} ∧
      integerOrder (fractionAddValuation A K) (∏ i, x i ^ a i) =
        -monomialPoleCoefficient (fractionAddValuation A K) x monomials hzero := by
  obtain ⟨a, ha, hord, hregular, _⟩ :=
    exists_regular_monomial_chart (fractionAddValuation A K) x monomials hzero
  refine ⟨a, ha, ?_, hord⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨b, hb, rfl⟩
    have hv : 0 ≤ fractionAddValuation A K
        (((∏ i, x i ^ b i) / (∏ i, x i ^ a i) : Kˣ) : K) := hregular b hb
    obtain ⟨c, hc⟩ := (exists_local_element_iff_nonnegative_order _).mpr hv
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    rw [Algebra.smul_def, hc]
    simp only [Units.val_div_eq_div_val]
    exact div_mul_cancel₀ _ (Units.ne_zero _)
  · apply Submodule.span_le.mpr
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact Submodule.subset_span ⟨a, ha, rfl⟩

theorem monomialLattice_rank_one
    {A K ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Fintype ι]
    (x : ι → Kˣ) (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials) :
    Nonempty (A ≃ₗ[A] monomialLattice A x monomials) := by
  obtain ⟨a, ha, hspan, hord⟩ := exists_monomialLattice_generator (A := A) x monomials hzero
  rw [hspan]
  exact ⟨LinearEquiv.toSpanNonzeroSingleton A K _ (Units.ne_zero _)⟩

end PiExponent.WeightedLocalLattice

end

end OAI
