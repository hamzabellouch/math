import OAI.NumberTheory.JointDickman.Arithmetic.SingleFormSieve
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeNormalizerUpper

namespace OAI

/-! # The combined normalizer and sieve density for an addition product -/

namespace JointDickman

open Finset

noncomputable def quarterOdds (p : ℕ) : ℝ := (1 / 4) / (1 - (1 / 4 : ℝ) / p)

noncomputable def additionSieveTheta (P p : ℕ) : ℝ := if p ≤ P then 0 else quarterOdds p

noncomputable def additionSieveDensity (P Z : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE Z, (1 - (1 - additionSieveTheta P p) / p)

theorem quarterOdds_bounds {p : ℕ} (hp : 2 ≤ p) : 0 ≤ quarterOdds p ∧ quarterOdds p ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith only [hp2]
  have hfrac : (1 / 4 : ℝ) / p ≤ 1 / 8 := by
    apply (div_le_iff₀ hp0).mpr
    linarith only [hp2]
  have hden : 0 < 1 - (1 / 4 : ℝ) / p := by linarith only [hfrac]
  exact ⟨div_nonneg (by norm_num) hden.le, (div_le_one hden).mpr (by linarith only [hfrac])⟩

theorem additionSieveTheta_bounds (P : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ additionSieveTheta P p ∧ additionSieveTheta P p ≤ 1 := by
  unfold additionSieveTheta
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact quarterOdds_bounds hp

theorem additionSieve_local_bound (P : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    (if P < p then 1 - (1 / 4 : ℝ) / p else 1) *
        (1 - (1 - additionSieveTheta P p) / p) ≤
      (1 - 1 / (p : ℝ)) * Real.exp (1 / (p : ℝ)^2) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith only [hp2]
  have hrec : 1 / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith only [hp2])
  have hbase : 0 ≤ 1 - 1 / (p : ℝ) := by linarith only [hrec]
  have hexp := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1 / (p : ℝ)^2)) hbase
  by_cases hP : p ≤ P
  · simp only [additionSieveTheta, hP, ite_true, Nat.not_lt.mpr hP, ite_false, sub_zero]
    have hsq : 0 ≤ (1 - 1 / (p : ℝ)) * (1 / (p : ℝ)^2) := mul_nonneg hbase (by positivity)
    nlinarith only [hexp, hsq]
  · have hden : 1 - (1 / 4 : ℝ) / p ≠ 0 := by
      have hh : (1 / 4 : ℝ) / p ≤ 1 / 8 := (div_le_iff₀ hp0).mpr (by linarith only [hp2])
      linarith only [hh]
    have heq : (1 - (1 / 4 : ℝ) / p) * (1 - (1 - quarterOdds p) / p) =
        (1 - 1 / (p : ℝ)) + (1 / 4 : ℝ) * (1 / (p : ℝ)^2) := by
      have hden' : -1 + (p : ℝ) * 4 ≠ 0 := by linarith only [hp2]
      unfold quarterOdds
      field_simp [hden']
      linear_combination (p : ℝ) * mul_inv_cancel₀ hden'
    simp only [additionSieveTheta, hP, ite_false, Nat.lt_of_not_ge hP, ite_true, heq]
    have hcoef : (1 / 4 : ℝ) * (1 / (p : ℝ)^2) ≤
        (1 - 1 / (p : ℝ)) * (1 / (p : ℝ)^2) :=
      mul_le_mul_of_nonneg_right (by linarith only [hrec]) (by positivity)
    nlinarith only [hexp, hcoef]

theorem additionSieve_normalizer_bound (P Z : ℕ) :
    primeNormalizer ((Nat.primesLE Z).filter (fun p => P < p)) (1 / 4) * additionSieveDensity P Z ≤
      Real.exp 1 * ∏ p ∈ Nat.primesLE Z, (1 - 1 / (p : ℝ)) := by
  classical
  have hprime : ∀ p ∈ Nat.primesLE Z, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hbase : 0 ≤ ∏ p ∈ Nat.primesLE Z, (1 - 1 / (p : ℝ)) := by
    apply prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).one_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    exact sub_nonneg.mpr ((div_le_one hp0).mpr hp1)
  calc
    _ = ∏ p ∈ Nat.primesLE Z,
        (if P < p then 1 - (1 / 4 : ℝ) / p else 1) *
          (1 - (1 - additionSieveTheta P p) / p) := by
      rw [primeNormalizer, prod_filter, additionSieveDensity, prod_mul_distrib]
    _ ≤ ∏ p ∈ Nat.primesLE Z, (1 - 1 / (p : ℝ)) * Real.exp (1 / (p : ℝ)^2) := by
      apply prod_le_prod₀
      · intro p hp
        have hθ := additionSieveTheta_bounds P (hprime p hp).two_le
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).one_le
        have hfrac : (1 - additionSieveTheta P p) / p ≤ 1 :=
          (div_le_one hp0).mpr (by linarith only [hθ.1, hp1])
        apply mul_nonneg _ (sub_nonneg.mpr hfrac)
        split_ifs
        · have hh : (1 / 4 : ℝ) / p ≤ 1 := (div_le_one hp0).mpr (by linarith only [hp1])
          exact sub_nonneg.mpr hh
        · exact zero_le_one
      · intro p hp
        exact additionSieve_local_bound P (hprime p hp).two_le
    _ = (∏ p ∈ Nat.primesLE Z, (1 - 1 / (p : ℝ))) *
        Real.exp (∑ p ∈ Nat.primesLE Z, 1 / (p : ℝ)^2) := by rw [prod_mul_distrib, Real.exp_sum]
    _ ≤ _ := by
      rw [mul_comm (Real.exp 1)]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hbase
      simpa using sum_reciprocal_square_tail (Nat.primesLE Z) (by norm_num : (1 : ℕ) ≠ 0)
        (fun p hp => (hprime p hp).one_lt)

theorem prime_roughness_product_log_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ Z : ℕ, 2 ≤ Z →
      (∏ p ∈ Nat.primesLE Z, (1 - 1 / (p : ℝ))) * Real.log Z ≤ K := by
  obtain ⟨M, A, hA, hMertens⟩ := hM
  refine ⟨Real.exp (-M + A / Real.log 2), Real.exp_pos _, ?_⟩
  intro Z hZ
  have hZ2 : (2 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hlog : 0 < Real.log Z := Real.log_pos (by linarith only [hZ2])
  have hm := (abs_le.mp (hMertens Z hZ2)).1
  rw [Nat.floor_natCast, ← primesLE_eq_filter] at hm
  have herror := div_le_div_of_nonneg_left hA (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    (Real.log_le_log (by norm_num) hZ2)
  have hp : (∏ p ∈ Nat.primesLE Z, (1 - 1 / (p : ℝ))) ≤
      Real.exp (-(∑ p ∈ Nat.primesLE Z, 1 / (p : ℝ))) := by
    rw [← sum_neg_distrib, Real.exp_sum]
    apply prod_le_prod₀
    · intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le
      exact sub_nonneg.mpr ((div_le_one hp0).mpr hp1)
    · intro p _
      exact Real.one_sub_le_exp_neg _
  calc
    _ ≤ Real.exp (-(∑ p ∈ Nat.primesLE Z, 1 / (p : ℝ))) * Real.log Z :=
      mul_le_mul_of_nonneg_right hp hlog.le
    _ = Real.exp (-(∑ p ∈ Nat.primesLE Z, 1 / (p : ℝ)) + Real.log (Real.log Z)) := by
      rw [Real.exp_add, Real.exp_log hlog]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hm, herror])

theorem additionSieve_density_log_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ P Z : ℕ, 2 ≤ Z →
      primeNormalizer ((Nat.primesLE Z).filter (fun p => P < p)) (1 / 4) *
        additionSieveDensity P Z * Real.log Z ≤ K := by
  obtain ⟨K, hK, hb⟩ := prime_roughness_product_log_bound hM
  refine ⟨Real.exp 1 * K, mul_pos (Real.exp_pos _) hK, ?_⟩
  intro P Z hZ
  have hl : 0 ≤ Real.log Z := Real.log_natCast_nonneg Z
  have hh := mul_le_mul_of_nonneg_right (additionSieve_normalizer_bound P Z) hl
  have hh' := mul_le_mul_of_nonneg_left (hb Z hZ) (Real.exp_pos 1).le
  nlinarith only [hh, hh']

theorem additionSieveDensity_nonneg (P Z : ℕ) : 0 ≤ additionSieveDensity P Z := by
  apply prod_nonneg
  intro p hp
  have hθ := additionSieveTheta_bounds P (Nat.mem_primesLE.mp hp).2.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le
  exact sub_nonneg.mpr ((div_le_one hp0).mpr (by linarith only [hθ.1, hp1]))

theorem quarterNormalizer_le_prefix {Q : Finset ℕ} {P Z : ℕ}
    (hQ : ∀ p ∈ Q, p.Prime) (hsub : (Nat.primesLE Z).filter (fun p => P < p) ⊆ Q) :
    primeNormalizer Q (1 / 4) ≤
      primeNormalizer ((Nat.primesLE Z).filter (fun p => P < p)) (1 / 4) := by
  apply prod_le_prod_of_subset_of_le_one₀ hsub
  · intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hQ p hp).pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQ p hp).one_le
    exact sub_nonneg.mpr ((div_le_one hp0).mpr (by linarith only [hp1]))
  · intro p hp _
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hf : (0 : ℝ) ≤ (1 / 4 : ℝ) / p := div_nonneg (by norm_num) hp0
    linarith only [hf]

end JointDickman

end OAI
