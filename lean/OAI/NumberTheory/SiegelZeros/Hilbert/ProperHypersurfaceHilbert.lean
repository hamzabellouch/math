import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Fintype.Option
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.Tactic
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.ColonSeriesTelescope
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.RegularSequenceSeries
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.StabilizedColonPowers

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W27
open Polynomial

theorem difference_taylor_coefficient (p : Polynomial ℚ) (s : ℕ)
    (hp : p.natDegree = s+1) (a : ℚ) :
    (p - Polynomial.taylor a p).coeff s = -a * (s+1 : ℚ) * p.leadingCoeff := by
  have hd : (Polynomial.hasseDeriv s p).natDegree ≤ 1 := by
    simpa [hp] using Polynomial.natDegree_hasseDeriv_le p s
  have hlin := Polynomial.eq_X_add_C_of_natDegree_le_one hd
  have h0 : (Polynomial.hasseDeriv s p).coeff 0 = p.coeff s := by
    simp [Polynomial.hasseDeriv_coeff]
  have h1 : (Polynomial.hasseDeriv s p).coeff 1 = (s+1 : ℚ) * p.leadingCoeff := by
    rw [Polynomial.hasseDeriv_coeff]
    simp only [Nat.add_comm 1 s, Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one]
    rw [← hp, Polynomial.coeff_natDegree]
  rw [Polynomial.coeff_sub, Polynomial.taylor_coeff, hlin]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [h0, h1]
  ring

theorem difference_taylor_natDegree_le (p : Polynomial ℚ) (s : ℕ)
    (hp : p.natDegree = s+1) (a : ℚ) :
    (p - Polynomial.taylor a p).natDegree ≤ s := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [Polynomial.coeff_sub]
  by_cases he : n = s+1
  · subst n
    rw [← hp, Polynomial.coeff_natDegree, Polynomial.coeff_taylor_natDegree, sub_self]
  · have hlt : p.natDegree < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hlt), sub_self]

theorem backward_difference_degree_and_leading
    (p : Polynomial ℚ) (s : ℕ) (hp : p.natDegree = s+1)
    (d : ℚ) (hd : d ≠ 0) :
    (p - Polynomial.taylor (-d) p).natDegree = s ∧
      (p - Polynomial.taylor (-d) p).leadingCoeff = d * (s+1 : ℚ) * p.leadingCoeff := by
  have hp0 : p ≠ 0 := by
    intro hz
    simp [hz] at hp
  have hs : (s+1 : ℚ) ≠ 0 := by positivity
  have hc : (p - Polynomial.taylor (-d) p).coeff s =
      d * (s+1 : ℚ) * p.leadingCoeff := by
    simpa using difference_taylor_coefficient p s hp (-d)
  have hcn : (p - Polynomial.taylor (-d) p).coeff s ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (mul_ne_zero hd hs) (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  have hdeg := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (difference_taylor_natDegree_le p s hp (-d)) hcn
  refine ⟨hdeg, ?_⟩
  simpa only [Polynomial.leadingCoeff, hdeg] using hc

theorem backward_difference_multiplicity
    (p : Polynomial ℚ) (s : ℕ) (hp : p.natDegree = s+1)
    (d : ℚ) (hd : d ≠ 0) :
    (p - Polynomial.taylor (-d) p).leadingCoeff *
        ((p - Polynomial.taylor (-d) p).natDegree.factorial : ℚ) =
      d * (p.leadingCoeff * (p.natDegree.factorial : ℚ)) := by
  obtain ⟨hdeg, hl⟩ := backward_difference_degree_and_leading p s hp d hd
  rw [hl, hdeg, hp, Nat.factorial_succ]
  push_cast
  ring

theorem backward_difference_eq_comp (p : Polynomial ℚ) (d : ℚ) :
    p - Polynomial.taylor (-d) p = p - p.comp (Polynomial.X - Polynomial.C d) := by
  simp only [Polynomial.taylor_apply, Polynomial.C_neg, sub_eq_add_neg]

end WeightedTorusJets.W27

end

section

namespace WeightedTorusJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def colonHilbertNumerator (P : ℕ → Polynomial ℤ) (m : ℕ) : Polynomial ℤ :=
  (∑ j ∈ Finset.range m, Polynomial.X ^ j * P j) * (1 - Polynomial.X) +
    Polynomial.X ^ m * P m

theorem stabilized_colon_polynomial_numerator
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous 1) (m r : ℕ)
    (hstable : iteratedColon I f (m+1) = iteratedColon I f m)
    (P : ℕ → Polynomial ℤ)
    (hP : ∀ j : ℕ, sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon I f j) =
      (P j : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ r).val) :
    sectionHilbertSeries I = (colonHilbertNumerator P m : PowerSeries ℤ) *
      (PowerSeries.invOneSubPow ℤ (r+1)).val := by
  have hu : (PowerSeries.invOneSubPow ℤ r).val =
      (1-PowerSeries.X) * (PowerSeries.invOneSubPow ℤ (r+1)).val := by
    symm
    simpa only [pow_one, Nat.add_comm] using
      PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℤ r 1
  have hv : (PowerSeries.invOneSubPow ℤ r).val * (PowerSeries.invOneSubPow ℤ 1).val =
      (PowerSeries.invOneSubPow ℤ (r+1)).val := by
    rw [← Units.val_mul, ← PowerSeries.invOneSubPow_add]
  rw [stabilized_iteratedColon_series I hI f hf m hstable]
  simp_rw [hP]
  have hsum : (∑ j ∈ Finset.range m,
      PowerSeries.X ^ j * ((P j : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ r).val)) =
      (∑ j ∈ Finset.range m, PowerSeries.X ^ j * (P j : PowerSeries ℤ)) *
        (PowerSeries.invOneSubPow ℤ r).val := by
    simp only [Finset.sum_mul, mul_assoc]
  rw [hsum, mul_assoc (P m : PowerSeries ℤ), hv, hu]
  have hcoe : (colonHilbertNumerator P m : PowerSeries ℤ) =
      (∑ j ∈ Finset.range m, PowerSeries.X ^ j * (P j : PowerSeries ℤ)) *
        (1-PowerSeries.X) + PowerSeries.X ^ m * (P m : PowerSeries ℤ) := by
    change Polynomial.coeToPowerSeries.ringHom
      ((∑ j ∈ Finset.range m, Polynomial.X ^ j * P j) * (1-Polynomial.X) +
        Polynomial.X ^ m * P m) = _
    rw [map_add, map_mul, map_sum]
    simp only [map_mul, map_sub, map_pow, map_one]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
  rw [hcoe]
  ring

end WeightedTorusJets.W64

end

section

namespace WeightedTorusJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def degreePolynomial (D : ℕ → ℕ) (m : ℕ) : Polynomial ℤ :=
  ∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i), (Polynomial.X : Polynomial ℤ) ^ j

theorem degreePolynomial_eval_one (D : ℕ → ℕ) (m : ℕ) :
    (degreePolynomial D m).eval 1 = ∏ i ∈ Finset.range m, (D i : ℤ) := by
  simp [degreePolynomial, Polynomial.eval_prod, Polynomial.eval_finsetSum]

variable {k σ : Type*} [Field k] [Fintype σ]

theorem regular_sequence_series_polynomial
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length = Fintype.card σ) :
    sectionHilbertSeries (Ideal.ofList rs) =
      ((degreePolynomial (degreeAt degrees) rs.length) : PowerSeries ℤ) := by
  rw [regular_sequence_series_geometric hσ rs degrees hhom hreg hlen]
  change _ = (Polynomial.coeToPowerSeries.ringHom : Polynomial ℤ →+* PowerSeries ℤ)
    (∏ i ∈ Finset.range rs.length, ∑ j ∈ Finset.range (degreeAt degrees i),
      (Polynomial.X : Polynomial ℤ) ^ j)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_pow]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

theorem regular_sequence_section_dimension_coeff
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length = Fintype.card σ) (n : ℕ) :
    (Module.finrank k (quotientSection (Ideal.ofList rs) n) : ℤ) =
      (degreePolynomial (degreeAt degrees) rs.length).coeff n := by
  have h := congrArg (PowerSeries.coeff n)
    (regular_sequence_series_polynomial hσ rs degrees hhom hreg hlen)
  simpa only [coeff_sectionHilbertSeries, Polynomial.coeff_coe] using h

theorem regular_sequence_section_dimension_eq_zero
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length = Fintype.card σ) (n : ℕ)
    (hn : n ∉ (degreePolynomial (degreeAt degrees) rs.length).support) :
    Module.finrank k (quotientSection (Ideal.ofList rs) n) = 0 := by
  have h := regular_sequence_section_dimension_coeff hσ rs degrees hhom hreg hlen n
  have hz : (degreePolynomial (degreeAt degrees) rs.length).coeff n = 0 := by
    simpa only [Polynomial.mem_support_iff, not_not] using hn
  rw [hz] at h
  exact_mod_cast h

theorem regular_sequence_section_dimension_sum
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length = Fintype.card σ) :
    (∑ n ∈ (degreePolynomial (degreeAt degrees) rs.length).support,
      Module.finrank k (quotientSection (Ideal.ofList rs) n)) =
      ∏ i ∈ Finset.range rs.length, degreeAt degrees i := by
  have h :
      (∑ n ∈ (degreePolynomial (degreeAt degrees) rs.length).support,
        (Module.finrank k (quotientSection (Ideal.ofList rs) n) : ℤ)) =
        ∏ i ∈ Finset.range rs.length, (degreeAt degrees i : ℤ) := by
    calc
      _ = ∑ n ∈ (degreePolynomial (degreeAt degrees) rs.length).support,
          (degreePolynomial (degreeAt degrees) rs.length).coeff n := by
        apply Finset.sum_congr rfl
        intro n _
        exact regular_sequence_section_dimension_coeff hσ rs degrees hhom hreg hlen n
      _ = (degreePolynomial (degreeAt degrees) rs.length).eval 1 := by
        simp [Polynomial.eval_eq_sum, Polynomial.sum]
      _ = _ := degreePolynomial_eval_one _ _
  exact_mod_cast h

theorem regular_sequence_section_dimension_sum_le
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length = Fintype.card σ) (D : ℕ)
    (hD : ∀ i, degrees i ≤ D) :
    (∑ n ∈ (degreePolynomial (degreeAt degrees) rs.length).support,
      Module.finrank k (quotientSection (Ideal.ofList rs) n)) ≤ D ^ rs.length := by
  rw [regular_sequence_section_dimension_sum hσ rs degrees hhom hreg hlen]
  calc
    _ ≤ ∏ _i ∈ Finset.range rs.length, D := by
      apply Finset.prod_le_prod
      intro i hi
      simpa only [degreeAt, dite_eq_left (Finset.mem_range.mp hi)] using
        hD ⟨i, Finset.mem_range.mp hi⟩
    _ = _ := by simp

end WeightedTorusJets.W64

end

section

namespace WeightedTorusJets.W64

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type v} [Field k]

theorem iteratedColon_eq_colon_power {σ : Type u} [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k) (n : ℕ) :
    iteratedColon I f n = I.colon {f^n} := by
  induction n with
  | zero => simp only [iteratedColon_zero, WeightedTorusJets.W06.colon_pow_zero]
  | succ n ih => rw [iteratedColon_succ, ih, WeightedTorusJets.W06.colon_pow_succ]

theorem sectionHilbertSeries_rename {σ τ : Type u} [Finite σ] [Finite τ]
    (e : σ ≃ τ) (I : Ideal (MvPolynomial σ k)) :
    sectionHilbertSeries I =
      sectionHilbertSeries (I.map (MvPolynomial.rename e).toRingHom) := by
  ext n
  simp only [coeff_sectionHilbertSeries,
    SiegelZeros.W08.renameQuotientSection_finrank e I n]

theorem sectionHilbertSeries_coordinate {σ : Type u} [Finite σ]
    (I : Ideal (MvPolynomial (Option σ) k)) (hX : MvPolynomial.X none ∈ I) :
    sectionHilbertSeries I =
      sectionHilbertSeries (SiegelZeros.W08.coordinateImageIdeal I) := by
  ext n
  simp only [coeff_sectionHilbertSeries,
    SiegelZeros.W08.coordinateQuotientSection_finrank I hX n]

theorem exists_homogeneous_hilbert_numerator
    (σ : Type u) [Fintype σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ P : Polynomial ℤ, sectionHilbertSeries I =
      (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  classical
  refine Fintype.induction_empty_option
    (P := fun τ _ => ∀ J : Ideal (MvPolynomial τ k),
      J.IsHomogeneous (MvPolynomial.homogeneousSubmodule τ k) →
      ∃ P : Polynomial ℤ, sectionHilbertSeries J =
        (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card τ)).val)
    ?_ ?_ ?_ σ I hI
  · intro α β _ e ih J hJ
    let : Fintype α := Fintype.ofEquiv β e.symm
    obtain ⟨P, hP⟩ := ih (J.map (MvPolynomial.rename e.symm).toRingHom)
      (SiegelZeros.W08.renameImageIdeal_homogeneous e.symm J hJ)
    refine ⟨P, ?_⟩
    rw [sectionHilbertSeries_rename e.symm J]
    simpa only [Fintype.card_congr e] using hP
  · intro J _
    exact exists_hilbert_numerator_no_variables (by simp) J
  · intro α _ ih J hJ
    let f : MvPolynomial (Option α) k := MvPolynomial.X none
    have hf : f.IsHomogeneous 1 := MvPolynomial.isHomogeneous_X k none
    obtain ⟨m, hm⟩ := WeightedTorusJets.W06.exists_colon_pow_stable J f
    have hstable : iteratedColon J f (m+1) = iteratedColon J f m := by
      simpa only [iteratedColon_eq_colon_power] using hm
    let Jlower : ℕ → Ideal (MvPolynomial (Option α) k) :=
      fun j => Ideal.span {f} ⊔ iteratedColon J f j
    have hlower : ∀ j, (Jlower j).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Option α) k) := by
      intro j
      apply Ideal.IsHomogeneous.sup
      · apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule (Option α) k)
        intro g hg
        obtain rfl := Set.mem_singleton_iff.mp hg
        exact ⟨1, hf⟩
      · exact iteratedColon_homogeneous J hJ f hf j
    have hX : ∀ j, MvPolynomial.X none ∈ Jlower j := by
      intro j
      have hinc : Ideal.span {f} ≤ Jlower j := le_sup_left
      exact hinc (Ideal.subset_span (Set.mem_singleton f))
    choose P hP using fun j => ih (SiegelZeros.W08.coordinateImageIdeal (Jlower j))
      (SiegelZeros.W08.coordinateImageIdeal_homogeneous (Jlower j) (hlower j))
    have hseries : ∀ j, sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon J f j) =
        (P j : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card α)).val := by
      intro j
      rw [show Ideal.span {f} ⊔ iteratedColon J f j = Jlower j from rfl,
        sectionHilbertSeries_coordinate (Jlower j) (hX j)]
      exact hP j
    refine ⟨colonHilbertNumerator P m, ?_⟩
    simpa only [Fintype.card_option] using
      stabilized_colon_polynomial_numerator J hJ f hf m (Fintype.card α) hstable P hseries

end WeightedTorusJets.W64

end

section

namespace WeightedTorusJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem regular_sequence_series_general
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs) :
    sectionHilbertSeries (Ideal.ofList rs) =
      (∏ i ∈ Finset.range rs.length, (1 - PowerSeries.X ^ degreeAt degrees i)) *
        (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  have h := regular_prefix_series rs degrees hhom hreg rs.length le_rfl
  simp only [List.take_length] at h
  rwa [sectionHilbertSeries_bot hσ] at h

theorem degreePolynomial_coe (D : ℕ → ℕ) (m : ℕ) :
    ((degreePolynomial D m) : PowerSeries ℤ) =
      ∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i),
        (PowerSeries.X : PowerSeries ℤ) ^ j := by
  change (Polynomial.coeToPowerSeries.ringHom : Polynomial ℤ →+* PowerSeries ℤ)
    (∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i),
      (Polynomial.X : Polynomial ℤ) ^ j) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_pow]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

theorem regular_sequence_series_residual
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length ≤ Fintype.card σ) :
    sectionHilbertSeries (Ideal.ofList rs) =
      ((degreePolynomial (degreeAt degrees) rs.length) : PowerSeries ℤ) *
        (PowerSeries.invOneSubPow ℤ (Fintype.card σ - rs.length)).val := by
  rw [regular_sequence_series_general hσ rs degrees hhom hreg]
  have hn : Fintype.card σ = rs.length + (Fintype.card σ - rs.length) :=
    (Nat.add_sub_of_le hlen).symm
  have hi := congrArg (PowerSeries.invOneSubPow ℤ) hn
  rw [PowerSeries.invOneSubPow_add] at hi
  rw [hi, Units.val_mul, ← mul_assoc,
    degree_factors_mul_invOneSubPow, ← degreePolynomial_coe]

noncomputable def rationalSectionHilbertSeries (I : Ideal (MvPolynomial σ k)) :
    PowerSeries ℚ := PowerSeries.map (Int.castRingHom ℚ) (sectionHilbertSeries I)

omit [Fintype σ] in
@[simp] theorem coeff_rationalSectionHilbertSeries
    (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    PowerSeries.coeff n (rationalSectionHilbertSeries I) =
      (Module.finrank k (quotientSection I n) : ℚ) := by
  simp [rationalSectionHilbertSeries, PowerSeries.coeff_map]

noncomputable def rationalDegreePolynomial (D : ℕ → ℕ) (m : ℕ) : Polynomial ℚ :=
  (degreePolynomial D m).map (Int.castRingHom ℚ)

theorem rationalDegreePolynomial_eval_one (D : ℕ → ℕ) (m : ℕ) :
    (rationalDegreePolynomial D m).eval 1 =
      (∏ i ∈ Finset.range m, D i : ℕ) := by
  rw [rationalDegreePolynomial, Polynomial.eval_one_map, degreePolynomial_eval_one]
  simp

theorem map_int_invOneSubPow (r : ℕ) :
    PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.invOneSubPow ℤ r).val =
      (PowerSeries.invOneSubPow ℚ r).val := by
  cases r with
  | zero => simp [PowerSeries.invOneSubPow_zero]
  | succ r =>
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
      PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
    ext n
    simp [PowerSeries.coeff_map]

theorem rational_regular_sequence_series_residual
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length ≤ Fintype.card σ) :
    rationalSectionHilbertSeries (Ideal.ofList rs) =
      ((rationalDegreePolynomial (degreeAt degrees) rs.length) : PowerSeries ℚ) *
        (PowerSeries.invOneSubPow ℚ (Fintype.card σ - rs.length)).val := by
  rw [rationalSectionHilbertSeries,
    regular_sequence_series_residual hσ rs degrees hhom hreg hlen,
    map_mul, map_int_invOneSubPow]
  rw [← Polynomial.polynomial_map_coe]
  rfl

noncomputable def regularSequenceHilbertPolynomial
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ) : Polynomial ℚ :=
  Polynomial.hilbertPoly (rationalDegreePolynomial (degreeAt degrees) rs.length)
    (Fintype.card σ - rs.length)

theorem regularSequenceHilbertPolynomial_eventually_exact
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length ≤ Fintype.card σ) (n : ℕ)
    (hn : (rationalDegreePolynomial (degreeAt degrees) rs.length).natDegree < n) :
    (Module.finrank k (quotientSection (Ideal.ofList rs) n) : ℚ) =
      (regularSequenceHilbertPolynomial rs degrees).eval (n : ℚ) := by
  rw [← coeff_rationalSectionHilbertSeries,
    rational_regular_sequence_series_residual hσ rs degrees hhom hreg hlen]
  exact Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval _ hn

theorem hilbertPolynomial_top_coefficient (p : Polynomial ℚ) (r : ℕ) (hr : 0 < r) :
    (Polynomial.hilbertPoly p r).coeff (r-1) =
      p.eval 1 * ((r-1).factorial : ℚ)⁻¹ := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.succ_sub_one, Polynomial.hilbertPoly_succ,
    Polynomial.finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul,
    Polynomial.coeff_preHilbertPoly_self]
  rw [← Finset.sum_mul]
  congr 1
  simp [Polynomial.eval_eq_sum, Polynomial.sum]

theorem hilbertPolynomial_natDegree_le (p : Polynomial ℚ) (r : ℕ) (hr : 0 < r) :
    (Polynomial.hilbertPoly p r).natDegree ≤ r-1 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.succ_sub_one, Polynomial.hilbertPoly_succ]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_smul_le _ _).trans
    (Polynomial.natDegree_preHilbertPoly ℚ s i).le

theorem hilbertPolynomial_degree_and_leading
    (p : Polynomial ℚ) (r : ℕ) (hr : 0 < r) (hp : p.eval 1 ≠ 0) :
    (Polynomial.hilbertPoly p r).natDegree = r-1 ∧
      (Polynomial.hilbertPoly p r).leadingCoeff = p.eval 1 * ((r-1).factorial : ℚ)⁻¹ := by
  have hf : (((r-1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (r-1)
  have hc : (Polynomial.hilbertPoly p r).coeff (r-1) ≠ 0 := by
    rw [hilbertPolynomial_top_coefficient p r hr]
    exact mul_ne_zero hp (inv_ne_zero hf)
  have hd := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (hilbertPolynomial_natDegree_le p r hr) hc
  refine ⟨hd, ?_⟩
  rw [Polynomial.leadingCoeff, hd, hilbertPolynomial_top_coefficient p r hr]

noncomputable def hilbertMultiplicity (p : Polynomial ℚ) (ringDimension : ℕ) : ℚ :=
  p.coeff (ringDimension-1) * ((ringDimension-1).factorial : ℚ)

theorem regularSequenceHilbertPolynomial_multiplicity
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hlen : rs.length < Fintype.card σ) :
    hilbertMultiplicity (regularSequenceHilbertPolynomial rs degrees)
        (Fintype.card σ - rs.length) =
      (∏ i ∈ Finset.range rs.length, degreeAt degrees i : ℕ) := by
  have hr : 0 < Fintype.card σ - rs.length := Nat.sub_pos_of_lt hlen
  have hf : (((Fintype.card σ - rs.length - 1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (Fintype.card σ - rs.length - 1)
  rw [hilbertMultiplicity, regularSequenceHilbertPolynomial,
    hilbertPolynomial_top_coefficient _ _ hr, mul_assoc, inv_mul_cancel₀ hf,
    mul_one, rationalDegreePolynomial_eval_one]

theorem regular_sequence_has_hilbert_polynomial_with_degree_product
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length < Fintype.card σ) :
    ∃ p : Polynomial ℚ,
      (∃ N : ℕ, ∀ n : ℕ, N < n →
        (Module.finrank k (quotientSection (Ideal.ofList rs) n) : ℚ) = p.eval (n : ℚ)) ∧
      hilbertMultiplicity p (Fintype.card σ - rs.length) =
        (∏ i ∈ Finset.range rs.length, degreeAt degrees i : ℕ) := by
  refine ⟨regularSequenceHilbertPolynomial rs degrees, ?_,
    regularSequenceHilbertPolynomial_multiplicity rs degrees hlen⟩
  refine ⟨(rationalDegreePolynomial (degreeAt degrees) rs.length).natDegree, ?_⟩
  intro n hn
  exact regularSequenceHilbertPolynomial_eventually_exact hσ rs degrees hhom hreg hlen.le n hn

end WeightedTorusJets.W64

end

section

namespace WeightedTorusJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def shiftHilbertPolynomial (p : Polynomial ℚ) (d : ℕ) : Polynomial ℚ :=
  p.comp (Polynomial.X - Polynomial.C (d : ℚ))

@[simp] theorem shiftHilbertPolynomial_eval (p : Polynomial ℚ) (d n : ℕ)
    (hdn : d ≤ n) :
    (shiftHilbertPolynomial p d).eval (n : ℚ) = p.eval ((n-d : ℕ) : ℚ) := by
  simp [shiftHilbertPolynomial, Polynomial.eval_comp, Nat.cast_sub hdn]

@[simp] theorem shiftHilbertPolynomial_natDegree (p : Polynomial ℚ) (d : ℕ) :
    (shiftHilbertPolynomial p d).natDegree = p.natDegree := by
  rw [shiftHilbertPolynomial, Polynomial.natDegree_comp,
    Polynomial.natDegree_X_sub_C, mul_one]

@[simp] theorem shiftHilbertPolynomial_leadingCoeff (p : Polynomial ℚ) (d : ℕ) :
    (shiftHilbertPolynomial p d).leadingCoeff = p.leadingCoeff := by
  rw [shiftHilbertPolynomial, Polynomial.leadingCoeff_comp]
  · rw [Polynomial.leadingCoeff_X_sub_C, one_pow, mul_one]
  · rw [Polynomial.natDegree_X_sub_C]
    exact one_ne_zero

theorem shiftHilbertPolynomial_top_coeff (p : Polynomial ℚ) (d t : ℕ)
    (hp : p.natDegree ≤ t) :
    (shiftHilbertPolynomial p d).coeff t = p.coeff t := by
  by_cases he : p.natDegree = t
  · rw [← he]
    calc
      (shiftHilbertPolynomial p d).coeff p.natDegree =
          (shiftHilbertPolynomial p d).coeff (shiftHilbertPolynomial p d).natDegree := by
            rw [shiftHilbertPolynomial_natDegree]
      _ = (shiftHilbertPolynomial p d).leadingCoeff := Polynomial.coeff_natDegree
      _ = p.leadingCoeff := shiftHilbertPolynomial_leadingCoeff p d
      _ = p.coeff p.natDegree := Polynomial.coeff_natDegree.symm
  · have ht : p.natDegree < t := lt_of_le_of_ne hp he
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (by simpa using ht : (shiftHilbertPolynomial p d).natDegree < t),
      Polynomial.coeff_eq_zero_of_natDegree_lt ht]

theorem hilbertMultiplicity_shift (p : Polynomial ℚ) (d r : ℕ)
    (hp : p.natDegree ≤ r-1) :
    hilbertMultiplicity (shiftHilbertPolynomial p d) r = hilbertMultiplicity p r := by
  unfold hilbertMultiplicity
  rw [shiftHilbertPolynomial_top_coeff p d (r-1) hp]

theorem hilbertMultiplicity_add (p q : Polynomial ℚ) (r : ℕ) :
    hilbertMultiplicity (p+q) r = hilbertMultiplicity p r + hilbertMultiplicity q r := by
  simp [hilbertMultiplicity, add_mul]

theorem colon_hilbert_polynomial_eventually
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (pJ pP : Polynomial ℚ) (NJ NP : ℕ)
    (hJ : ∀ n : ℕ, NJ < n →
      (Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) : ℚ) = pJ.eval (n : ℚ))
    (hP : ∀ n : ℕ, NP < n →
      (Module.finrank k (quotientSection (I.colon {f}) n) : ℚ) = pP.eval (n : ℚ)) :
    ∀ n : ℕ, NJ + NP + d < n →
      (Module.finrank k (quotientSection I n) : ℚ) =
        (pJ + shiftHilbertPolynomial pP d).eval (n : ℚ) := by
  intro n hn
  have hdn : d ≤ n := by omega
  have hnJ : NJ < n := by omega
  have hnP : NP < n-d := by omega
  have h := colon_hilbert_step I hI f hf (n-d)
  rw [Nat.sub_add_cancel hdn] at h
  have hc : (Module.finrank k (quotientSection I n) : ℚ) =
      (Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) : ℚ) +
      (Module.finrank k (quotientSection (I.colon {f}) (n-d)) : ℚ) := by
    exact_mod_cast h.symm
  rw [hc, hJ n hnJ, hP (n-d) hnP,
    Polynomial.eval_add, shiftHilbertPolynomial_eval pP d n hdn]

theorem colon_hilbert_polynomial_multiplicity
    (pJ pP : Polynomial ℚ) (d r : ℕ) (hP : pP.natDegree ≤ r-1) :
    hilbertMultiplicity (pJ + shiftHilbertPolynomial pP d) r =
      hilbertMultiplicity pJ r + hilbertMultiplicity pP r := by
  rw [hilbertMultiplicity_add, hilbertMultiplicity_shift pP d r hP]

end WeightedTorusJets.W64

end

section

namespace WeightedTorusJets.W64

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type v} [Field k]

theorem rational_hilbert_numerator {σ : Type u} [Fintype σ]
    (I : Ideal (MvPolynomial σ k)) (P : Polynomial ℤ)
    (hP : sectionHilbertSeries I =
      (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val) :
    rationalSectionHilbertSeries I =
      ((P.map (Int.castRingHom ℚ)) : PowerSeries ℚ) *
        (PowerSeries.invOneSubPow ℚ (Fintype.card σ)).val := by
  rw [rationalSectionHilbertSeries, hP, map_mul, map_int_invOneSubPow,
    ← Polynomial.polynomial_map_coe]

theorem exists_homogeneous_hilbert_polynomial
    (σ : Type u) [Fintype σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ p : Polynomial ℚ, ∃ N : ℕ, ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = p.eval (n : ℚ) := by
  obtain ⟨P, hP⟩ := exists_homogeneous_hilbert_numerator σ I hI
  refine ⟨Polynomial.hilbertPoly (P.map (Int.castRingHom ℚ)) (Fintype.card σ),
    (P.map (Int.castRingHom ℚ)).natDegree, ?_⟩
  intro n hn
  rw [← coeff_rationalSectionHilbertSeries, rational_hilbert_numerator I P hP]
  exact Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval _ hn

theorem exists_homogeneous_hilbert_polynomial_degree_le
    (σ : Type u) [Fintype σ] (hσ : 0 < Fintype.card σ)
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ p : Polynomial ℚ,
      (∃ N : ℕ, ∀ n : ℕ, N < n →
        (Module.finrank k (quotientSection I n) : ℚ) = p.eval (n : ℚ)) ∧
      p.natDegree ≤ Fintype.card σ - 1 := by
  obtain ⟨P, hP⟩ := exists_homogeneous_hilbert_numerator σ I hI
  refine ⟨Polynomial.hilbertPoly (P.map (Int.castRingHom ℚ)) (Fintype.card σ),
    ⟨(P.map (Int.castRingHom ℚ)).natDegree, ?_⟩,
    hilbertPolynomial_natDegree_le _ _ hσ⟩
  intro n hn
  rw [← coeff_rationalSectionHilbertSeries, rational_hilbert_numerator I P hP]
  exact Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval _ hn

end WeightedTorusJets.W64

end

section

namespace WeightedTorusJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem prime_quotient_right_regular (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (f : MvPolynomial σ k) (hfP : f ∉ P) :
    IsRightRegular (Ideal.Quotient.mk P f) := by
  have hf0 : Ideal.Quotient.mk P f ≠ 0 := by
    intro hz
    exact hfP (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  intro x y hxy
  exact mul_right_cancel₀ hf0 hxy

theorem regular_hypersurface_polynomial_eventually
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f))
    (p : Polynomial ℚ) (N : ℕ)
    (hP : ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = p.eval (n : ℚ)) :
    ∀ n : ℕ, N+d < n →
      (Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) : ℚ) =
        (p-shiftHilbertPolynomial p d).eval (n : ℚ) := by
  intro n hn
  have hdn : d ≤ n := by omega
  have hnP : N < n := by omega
  have hnshift : N < n-d := by omega
  have h := regular_hilbert_step I hI f hf hreg (n-d)
  rw [Nat.sub_add_cancel hdn] at h
  have hc : (Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) : ℚ) +
      (Module.finrank k (quotientSection I (n-d)) : ℚ) =
      (Module.finrank k (quotientSection I n) : ℚ) := by
    exact_mod_cast h
  rw [hP n hnP, hP (n-d) hnshift] at hc
  rw [Polynomial.eval_sub, shiftHilbertPolynomial_eval p d n hdn]
  exact eq_sub_of_add_eq hc

theorem prime_hypersurface_actual_hilbert_degree
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hfP : f ∉ P) (hd : 0 < d)
    (p : Polynomial ℚ) (N s : ℕ)
    (hp : ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection P n) : ℚ) = p.eval (n : ℚ))
    (hdegree : p.natDegree = s+1) :
    ∃ q : Polynomial ℚ,
      (∃ M : ℕ, ∀ n : ℕ, M < n →
        (Module.finrank k (quotientSection (Ideal.span {f} ⊔ P) n) : ℚ) = q.eval (n : ℚ)) ∧
      q.natDegree = s ∧
      q.leadingCoeff * (q.natDegree.factorial : ℚ) =
        (d : ℚ) * (p.leadingCoeff * (p.natDegree.factorial : ℚ)) := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  refine ⟨p-Polynomial.taylor (-(d : ℚ)) p, ⟨N+d, ?_⟩,
    (WeightedTorusJets.W27.backward_difference_degree_and_leading p s hdegree (d : ℚ) hdq).1,
    WeightedTorusJets.W27.backward_difference_multiplicity p s hdegree (d : ℚ) hdq⟩
  intro n hn
  rw [WeightedTorusJets.W27.backward_difference_eq_comp]
  exact regular_hypersurface_polynomial_eventually P hP f hf
    (prime_quotient_right_regular P f hfP) p N hp n hn

end WeightedTorusJets.W64

end

end SiegelZeros

end OAI
