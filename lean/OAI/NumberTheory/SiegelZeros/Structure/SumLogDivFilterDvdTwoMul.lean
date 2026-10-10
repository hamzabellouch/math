import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Characters.IntegerCharacter
import OAI.NumberTheory.SiegelZeros.Structure.SumLogPrimeFactors

namespace OAI

namespace SiegelZeros

section
open scoped BigOperators Topology

open scoped BigOperators

namespace WeightedTorusJets

theorem sum_log_div_filter_dvd_two_mul_le (q : ℕ) (hq : q ≠ 0) (s : Finset ℕ)
    (hprime : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s with p ∣ 2 * q, Real.log p / p ≤ Real.log q + Real.log 2 := by
  calc
    _ ≤ Real.log (2 * q : ℕ) :=
      sum_log_div_filter_dvd_le (2 * q) (Nat.mul_ne_zero (by decide) hq) s hprime
    _ = Real.log q + Real.log 2 := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (Nat.cast_ne_zero.mpr hq), add_comm]

theorem source_good_prime_mass_with_chebyshev_constant :
    ∃ C : ℝ, 0 < C ∧ Real.log 4 ≤ C ∧
      ∀ H : ℕ, 2 ≤ H → ∃ CH : ℝ,
        ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
          χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
          ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
          ∀ U : ℝ, 3 ≤ U →
            Real.log U - C * Real.log q -
              C * ((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q - CH ≤
              ∑ p ∈ Nat.primesLE ⌊U⌋₊ with
                H < p ∧ ¬p ∣ 2 * q ∧ χ ((p : ℕ) : ZMod q) = -1,
                  Real.log p / p := by
  obtain ⟨C₀, hC₀, _hpositive, hgood⟩ := source_analytic_lemma
  refine ⟨max C₀ (Real.log 4), hC₀.trans_le (le_max_left _ _), le_max_right _ _, ?_⟩
  intro H hH
  obtain ⟨CH, hCH⟩ := hgood H hH
  refine ⟨CH, ?_⟩
  intro q _ hq χ hprim hχ hreal β hβ0 hβ1 hzero U hU
  have hbase := hCH q hq χ hprim hχ hreal β hβ0 hβ1 hzero U hU
  have hell : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hdelta : 0 ≤ (1 - β) * Real.log q := mul_nonneg (by linarith) hell
  have herror : 0 ≤ ((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q :=
    div_nonneg (mul_nonneg hdelta (sq_nonneg _)) hell
  have hlinear := mul_le_mul_of_nonneg_right (le_max_left C₀ (Real.log 4)) hell
  have hquadratic := mul_le_mul_of_nonneg_right (le_max_left C₀ (Real.log 4)) herror
  have hbound : Real.log U - max C₀ (Real.log 4) * Real.log q -
      max C₀ (Real.log 4) *
        (((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q) - CH ≤
      ∑ p ∈ Nat.primesLE ⌊U⌋₊ with
        H < p ∧ ¬p ∣ 2 * q ∧ χ ((p : ℕ) : ZMod q) = -1, Real.log p / p := by
    linarith
  convert hbound using 1
  ring

end WeightedTorusJets

end

open scoped BigOperators

namespace WeightedTorusJets

theorem good_prime_filter_max_two (q H : ℕ) (c : ℕ → ℂ) (U : ℝ) :
    (Nat.primesLE ⌊U⌋₊).filter (fun p => max H 2 < p ∧ ¬p ∣ 2 * q ∧ c p = -1) =
      (Nat.primesLE ⌊U⌋₊).filter (fun p => H < p ∧ ¬p ∣ 2 * q ∧ c p = -1) := by
  apply Finset.filter_congr
  intro p hp
  by_cases hq : p ∣ 2 * q
  · simp [hq]
  have hpgt : 2 < p := lt_of_le_of_ne (Nat.prime_of_mem_primesLE hp).two_le (by
    rintro rfl
    exact hq (dvd_mul_right 2 q))
  simp [max_lt_iff, hpgt]

theorem good_prime_mass_extend_small_parameters (q H : ℕ) (c : ℕ → ℂ)
    {C ell delta CH : ℝ} (hC : 0 ≤ C) (hell : 0 ≤ ell) (hdelta : 0 ≤ delta)
    (hlarge : ∀ U : ℝ, 3 ≤ U →
      Real.log U - C * ell - C * delta * (Real.log U) ^ 2 / ell - CH ≤
        ∑ p ∈ (Nat.primesLE ⌊U⌋₊).filter
          (fun p => max H 2 < p ∧ ¬p ∣ 2 * q ∧ c p = -1), Real.log p / (p : ℝ))
    {U : ℝ} (hU : 0 ≤ U) :
    Real.log U - C * ell - C * delta * (Real.log U) ^ 2 / ell - max CH (Real.log 3) ≤
      ∑ p ∈ (Nat.primesLE ⌊U⌋₊).filter
        (fun p => H < p ∧ ¬p ∣ 2 * q ∧ c p = -1), Real.log p / (p : ℝ) := by
  by_cases hU3 : 3 ≤ U
  · have h := hlarge U hU3
    rw [good_prime_filter_max_two] at h
    exact le_trans (sub_le_sub_left (le_max_left _ _) _) h
  · have hlog : Real.log U ≤ Real.log 3 := by
      by_cases hU0 : U = 0
      · rw [hU0, Real.log_zero]
        exact Real.log_nonneg (by norm_num)
      · exact Real.log_le_log (lt_of_le_of_ne hU (Ne.symm hU0)) (by linarith)
    have hsum : 0 ≤ ∑ p ∈ (Nat.primesLE ⌊U⌋₊).filter
        (fun p => H < p ∧ ¬p ∣ 2 * q ∧ c p = -1), Real.log p / (p : ℝ) :=
      by positivity
    have hlin : 0 ≤ C * ell := by positivity
    have herr : 0 ≤ C * delta * (Real.log U) ^ 2 / ell := by positivity
    have hCH := le_max_right CH (Real.log 3)
    linarith

theorem source_good_prime_mass_all_parameters :
    ∃ C : ℝ, 0 < C ∧ Real.log 4 ≤ C ∧
      ∀ H : ℕ, ∃ CH : ℝ,
        ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
          χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
          ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
          ∀ U : ℝ, 0 ≤ U →
            Real.log U - C * Real.log q -
              C * ((1 - β) * Real.log q) * (Real.log U) ^ 2 / Real.log q - CH ≤
              ∑ p ∈ Nat.primesLE ⌊U⌋₊ with
                H < p ∧ ¬p ∣ 2 * q ∧ χ ((p : ℕ) : ZMod q) = -1,
                  Real.log p / p := by
  obtain ⟨C, hC, hC4, hmass⟩ := source_good_prime_mass_with_chebyshev_constant
  refine ⟨C, hC, hC4, ?_⟩
  intro H
  obtain ⟨CH, hCH⟩ := hmass (max H 2) (le_max_right _ _)
  refine ⟨max CH (Real.log 3), ?_⟩
  intro q _ hq χ hprim hne hreal β hβ0 hβ1 hzero U hU
  have hell : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hdelta : 0 ≤ (1 - β) * Real.log q := mul_nonneg (by linarith) hell
  exact good_prime_mass_extend_small_parameters q H (fun p => χ (p : ZMod q))
    hC.le hell hdelta (fun X hX => hCH q hq χ hprim hne hreal β hβ0 hβ1 hzero X hX) hU

theorem primitive_eighth_root_difference_pow {K : Type*} [Field K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 8) (u : (ZMod 8)ˣ) :
    ζ ^ u.val.val - (ζ ^ u.val.val) ^ 3 =
      (ZMod.χ₈ u : ℤ) * (ζ - ζ ^ 3) := by
  have h4 : ζ ^ 4 = -1 := by
    apply IsPrimitiveRoot.eq_neg_one_of_two_right
    simpa using hζ.pow_div_gcd 4 (by decide : Nat.gcd 8 4 ≠ 0)
  have hunit : IsUnit (u : ZMod 8) := u.isUnit
  generalize hu : (u : ZMod 8) = x at *
  fin_cases x
  · exact False.elim ((by decide : ¬ IsUnit (0 : ZMod 8)) hunit)
  · change ζ ^ 1 - (ζ ^ 1) ^ 3 = (1 : ℤ) * (ζ - ζ ^ 3)
    simp
  · exact False.elim ((by decide : ¬ IsUnit (2 : ZMod 8)) hunit)
  · change ζ ^ 3 - (ζ ^ 3) ^ 3 = (-1 : ℤ) * (ζ - ζ ^ 3)
    push_cast
    linear_combination (-ζ ^ 5 + ζ) * h4
  · exact False.elim ((by decide : ¬ IsUnit (4 : ZMod 8)) hunit)
  · change ζ ^ 5 - (ζ ^ 5) ^ 3 = (-1 : ℤ) * (ζ - ζ ^ 3)
    push_cast
    linear_combination (-ζ ^ 11 + ζ ^ 7 - ζ ^ 3 + ζ) * h4
  · exact False.elim ((by decide : ¬ IsUnit (6 : ZMod 8)) hunit)
  · change ζ ^ 7 - (ζ ^ 7) ^ 3 = (1 : ℤ) * (ζ - ζ ^ 3)
    push_cast
    linear_combination (-ζ ^ 17 + ζ ^ 13 - ζ ^ 9 + ζ ^ 5 + ζ ^ 3 - ζ) * h4

theorem cyclotomic_eight_sqrt_two_action {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {8} ℚ K] (σ : Gal(K/ℚ)) :
    let ζ := IsCyclotomicExtension.zeta 8 ℚ K
    σ (ζ - ζ ^ 3) = (ZMod.χ₈ (IsCyclotomicExtension.Rat.galEquivZMod 8 K σ) : ℤ) *
      (ζ - ζ ^ 3) := by
  dsimp only
  rw [map_sub, map_pow, IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq 8 K σ
    (IsCyclotomicExtension.zeta_spec 8 ℚ K).pow_eq_one]
  exact primitive_eighth_root_difference_pow (IsCyclotomicExtension.zeta_spec 8 ℚ K) _

theorem chiEight_not_factorsThrough_four :
    ¬ DirichletCharacter.FactorsThrough ZMod.χ₈ 4 := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (by decide : 4 ∣ 8)]
  intro h
  let u : (ZMod 8)ˣ := ZMod.unitOfCoprime 5 (by decide)
  have hu : u ∈ (ZMod.unitsMap (by decide : 4 ∣ 8)).ker := by decide
  have hχ := h hu
  change (ZMod.χ₈ : DirichletCharacter ℤ 8).toUnitHom u = 1 at hχ
  have hc := congrArg Units.val hχ
  norm_num [MulChar.coe_toUnitHom, u, ZMod.χ₈] at hc

theorem chiEight_isPrimitive :
    DirichletCharacter.IsPrimitive ZMod.χ₈ := by
  let χ : DirichletCharacter ℤ 8 := ZMod.χ₈
  have hd : χ.conductor ∣ 2 ^ 3 := by simpa using χ.conductor_dvd_level
  obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hf := χ.factorsThrough_conductor
  change χ.conductor = 8
  interval_cases k
  · have h4 : χ.FactorsThrough 4 := hf.mono χ (by simp [heq]) (by decide)
    exact (chiEight_not_factorsThrough_four h4).elim
  · have h4 : χ.FactorsThrough 4 := hf.mono χ (by simp [heq]) (by decide)
    exact (chiEight_not_factorsThrough_four h4).elim
  · have h4 : χ.FactorsThrough 4 := hf.mono χ (by simp [heq]) (by decide)
    exact (chiEight_not_factorsThrough_four h4).elim
  · simpa using heq

open NumberField IsCyclotomicExtension.Rat

theorem cyclotomic_eight_adjoin_eq_characterField {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {8} ℚ K] [IsAbelianGalois ℚ K] :
    let ζ := IsCyclotomicExtension.zeta 8 ℚ K
    IntermediateField.adjoin ℚ {ζ - ζ ^ 3} =
      characterField 8 K ℂ (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)) := by
  dsimp only
  let t := IsCyclotomicExtension.zeta 8 ℚ K - (IsCyclotomicExtension.zeta 8 ℚ K) ^ 3
  have ht : t ≠ 0 := by
    have hsq := primitive_eighth_root_difference_sq (IsCyclotomicExtension.zeta_spec 8 ℚ K)
    change t ^ 2 = 2 at hsq
    intro h
    rw [h] at hsq
    norm_num at hsq
  apply IsGalois.intermediateFieldEquivSubgroup.injective
  change (IntermediateField.adjoin ℚ {t}).fixingSubgroup =
    (characterField 8 K ℂ (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ))).fixingSubgroup
  ext σ
  have hfix : σ ∈ (IntermediateField.adjoin ℚ {t}).fixingSubgroup ↔ σ t = t := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h
      exact h t (IntermediateField.mem_adjoin_simple_self ℚ t)
    · intro h x hx
      have hmap : σ.toAlgHom.comp (IntermediateField.adjoin ℚ {t}).val =
          (IntermediateField.adjoin ℚ {t}).val := by
        apply IntermediateField.adjoin_algHom_ext
        intro y hy
        obtain rfl := Set.mem_singleton_iff.mp hy
        exact h
      exact DFunLike.congr_fun hmap ⟨x, hx⟩
  rw [hfix, mem_characterField_fixingSubgroup _ _ _ _
    (ZMod.isQuadratic_χ₈.comp (Int.castRingHom ℂ))]
  change (σ t = t) ↔ _
  rw [show σ t = (ZMod.χ₈ (galEquivZMod 8 K σ) : ℤ) * t from
    cyclotomic_eight_sqrt_two_action σ, mul_eq_right₀ ht]
  change ((ZMod.χ₈ (galEquivZMod 8 K σ) : K) = 1) ↔
    ((ZMod.χ₈ (galEquivZMod 8 K σ) : ℂ) = 1)
  norm_cast

theorem quadratic_character_eq_of_characterField_eq {n : ℕ} [NeZero n]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    [IsAbelianGalois ℚ K] {R : Type*} [CommRing R] [IsDomain R]
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]
    {χ ψ : DirichletCharacter R n} (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic)
    (hfield : characterField n K R χ = characterField n K R ψ) : χ = ψ := by
  apply MulChar.ext
  intro u
  have hiff : χ u = 1 ↔ ψ u = 1 := by
    have hm := congrArg (fun F : IntermediateField ℚ K =>
      (galEquivZMod n K).symm u ∈ F.fixingSubgroup) hfield
    simpa only [mem_characterField_fixingSubgroup n K R χ hχ,
      mem_characterField_fixingSubgroup n K R ψ hψ, MulEquiv.apply_symm_apply] using
      Iff.of_eq hm
  have hχ0 : χ u ≠ 0 := (u.isUnit.map χ).ne_zero
  have hψ0 : ψ u ≠ 0 := (u.isUnit.map ψ).ne_zero
  rcases hχ u with hx | hx | hx <;> rcases hψ u with hy | hy | hy <;> simp_all

theorem primitive_level_eq_eight_of_same_lifted_characterField
    {q m : ℕ} [NeZero m] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K] [IsAbelianGalois ℚ K]
    (hq : q ∣ m) (h8 : 8 ∣ m) (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    (hfield : characterField m K ℂ (DirichletCharacter.changeLevel hq χ) =
      characterField m K ℂ (DirichletCharacter.changeLevel h8
        (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)))) : q = 8 := by
  have hquadq : (DirichletCharacter.changeLevel hq χ).IsQuadratic := by
    rw [MulChar.isQuadratic_iff_sq_eq_one, ← map_pow, hquad.sq_eq_one, map_one]
  have hquad8 : (DirichletCharacter.changeLevel h8
      (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ))).IsQuadratic := by
    rw [MulChar.isQuadratic_iff_sq_eq_one, ← map_pow,
      (ZMod.isQuadratic_χ₈.comp (Int.castRingHom ℂ)).sq_eq_one, map_one]
  have heq := quadratic_character_eq_of_characterField_eq hquadq hquad8 hfield
  have hc := congrArg DirichletCharacter.conductor heq
  rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel,
    hprim, conductor_ringHomComp ZMod.χ₈ (Int.castRingHom ℂ)
      (Int.cast_injective (α := ℂ))] at hc
  exact hc.trans chiEight_isPrimitive

theorem primitive_level_eq_eight_of_sqrt_two_field
    {q m : ℕ} [NeZero m] {K L : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] [IsAbelianGalois ℚ K]
    [Field L] [NumberField L] [IsCyclotomicExtension {8} ℚ L] [IsAbelianGalois ℚ L]
    [Algebra L K] [IsScalarTower ℚ L K]
    (hq : q ∣ m) (h8 : 8 ∣ m) (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic) (b : K) (hb : b ^ 2 = 2)
    (hfield : characterField m K ℂ (DirichletCharacter.changeLevel hq χ) =
      IntermediateField.adjoin ℚ {b}) : q = 8 := by
  let t : L := IsCyclotomicExtension.zeta 8 ℚ L - (IsCyclotomicExtension.zeta 8 ℚ L) ^ 3
  let tK : K := algebraMap L K t
  have htK : tK ^ 2 = 2 := by
    change (algebraMap L K t) ^ 2 = 2
    rw [← map_pow, primitive_eighth_root_difference_sq
      (IsCyclotomicExtension.zeta_spec 8 ℚ L), map_ofNat]
  have hadj : IntermediateField.adjoin ℚ {b} = IntermediateField.adjoin ℚ {tK} := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hb.trans htK.symm) with h | h
    · rw [h]
    · rw [h]
      apply le_antisymm
      · apply IntermediateField.adjoin_simple_le_iff.mpr
        exact IntermediateField.neg_mem _ (IntermediateField.mem_adjoin_simple_self ℚ tK)
      · apply IntermediateField.adjoin_simple_le_iff.mpr
        have hm := IntermediateField.neg_mem (IntermediateField.adjoin ℚ {-tK})
          (IntermediateField.mem_adjoin_simple_self ℚ (-tK))
        simpa using hm
  apply primitive_level_eq_eight_of_same_lifted_characterField (K := K) hq h8 χ hprim hquad
  rw [hfield, characterField_changeLevel 8 L ℂ K h8 _
    (ZMod.isQuadratic_χ₈.comp (Int.castRingHom ℂ)),
    ← cyclotomic_eight_adjoin_eq_characterField, IntermediateField.adjoin_map,
    Set.image_singleton]
  exact hadj

theorem primitive_level_eq_eight_of_lifted_sqrt_two_field
    {q m : ℕ} [NeZero m] {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {m} ℚ K] [IsAbelianGalois ℚ K]
    (hq : q ∣ m) (h8 : 8 ∣ m) (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic) (b : K) (hb : b ^ 2 = 2)
    (hfield : characterField m K ℂ (DirichletCharacter.changeLevel hq χ) =
      IntermediateField.adjoin ℚ {b}) : q = 8 := by
  let ζ : K := IsCyclotomicExtension.zeta m ℚ K ^ (m / 8)
  have hζ : IsPrimitiveRoot ζ 8 :=
    (IsCyclotomicExtension.zeta_spec m ℚ K).pow (NeZero.pos m)
      (Nat.div_mul_cancel h8).symm
  let L := IntermediateField.adjoin ℚ {ζ}
  let : IsCyclotomicExtension {8} ℚ L :=
    hζ.intermediateField_adjoin_isCyclotomicExtension (K := ℚ)
  exact primitive_level_eq_eight_of_sqrt_two_field (L := L) hq h8 χ hprim hquad b hb hfield

end WeightedTorusJets

end SiegelZeros

end OAI
