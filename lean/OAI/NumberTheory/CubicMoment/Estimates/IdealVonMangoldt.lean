import OAI.NumberTheory.CubicMoment.Estimates.IdealMoebiusBounds

namespace OAI

/-! The convolution definition of ideal von Mangoldt has exactly its usual
prime-power coefficients. This is the arithmetic bridge for prime replacement
in the short Möbius decomposition. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealLogNorm_prime_difference (ν : EisensteinIdealExponent)
    (p : EisensteinIdealPrime) (hp : 1 ≤ ν p) :
    MvPowerSeries.coeff ν idealLogNorm -
        MvPowerSeries.coeff (ν - Finsupp.single p 1) idealLogNorm =
      Real.log (normNat (idealPrimeRepresentative p)) := by
  have hle : Finsupp.single p 1 ≤ ν := Finsupp.single_le_iff.mpr hp
  have he : ν = (ν - Finsupp.single p 1) + Finsupp.single p 1 :=
    (tsub_add_cancel_of_le hle).symm
  change Real.log (idealExponentNorm ν) -
    Real.log (idealExponentNorm (ν - Finsupp.single p 1)) = _
  conv_lhs => lhs; rw [he, idealExponentNorm_add]
  rw [Real.log_mul (idealExponentNorm_pos _).ne' (idealExponentNorm_pos _).ne',
    idealExponentNorm_single, pow_one]
  ring

private lemma coeff_logNorm_finite_nonempty (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) (hS : S.Nonempty) (hν : S ⊆ ν.support) :
    MvPowerSeries.coeff ν (idealLogNorm * finiteIdealMoebius S) =
      if S.card = 1 then ∑ p ∈ S, Real.log (normNat (idealPrimeRepresentative p)) else 0 := by
  induction S using Finset.induction_on generalizing ν with
  | empty => exact (Finset.not_nonempty_empty hS).elim
  | @insert p S hp ih =>
    have hνp : 1 ≤ ν p := Nat.one_le_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp (hν (Finset.mem_insert_self _ _)))
    have he : idealLogNorm * finiteIdealMoebius (insert p S) =
        (idealLogNorm * finiteIdealMoebius S) * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, mul_sub, mul_one, map_sub, MvPowerSeries.X_def,
      MvPowerSeries.coeff_mul_monomial]
    simp only [Finsupp.single_le_iff, ite_eq_left hνp, mul_one]
    by_cases hSE : S = ∅
    · subst S
      simpa [finiteIdealMoebius] using idealLogNorm_prime_difference ν p hνp
    · have hS' : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSE
      have hνS : S ⊆ ν.support := fun q hq => hν (Finset.mem_insert_of_mem hq)
      have hνS' : S ⊆ (ν - Finsupp.single p 1 : EisensteinIdealExponent).support := by
        intro q hq
        apply Finsupp.mem_support_iff.mpr
        have hqp : q ≠ p := ne_of_mem_of_not_mem hq hp
        simpa [Finsupp.tsub_apply, hqp] using Finsupp.mem_support_iff.mp (hνS hq)
      rw [ih ν hS' hνS, ih _ hS' hνS', sub_self]
      have hc : (insert p S).card ≠ 1 := by
        rw [Finset.card_insert_of_notMem hp]
        have := Finset.card_pos.mpr hS'
        omega
      simp [hc]

lemma idealVonMangoldt_coeff_eq_finite (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      MvPowerSeries.coeff ν (idealLogNorm * finiteIdealMoebius ν.support) := by
  rw [idealVonMangoldt, mul_comm idealLogNorm, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have hle : a.1 ≤ ν := by
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp ha]
    exact le_add_of_nonneg_right zero_le
  rw [coeff_idealMoebiusSeries_eq_finite ν.support a.1 (Finsupp.support_mono hle)]

/-- The von Mangoldt coefficient is supported precisely on prime-ideal
powers and has weight the logarithm of that prime-ideal norm. -/
lemma idealVonMangoldt_coeff (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      if ν.support.card = 1 then
        ∑ p ∈ ν.support, Real.log (normNat (idealPrimeRepresentative p)) else 0 := by
  rw [idealVonMangoldt_coeff_eq_finite]
  by_cases hs : ν.support.Nonempty
  · exact coeff_logNorm_finite_nonempty _ _ hs (Finset.Subset.refl _)
  · have hz : ν = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hs)
    subst ν
    simp only [Finsupp.support_zero, finiteIdealMoebius, Finset.prod_empty, mul_one,
      Finset.card_empty, Nat.zero_ne_one, ite_false]
    change Real.log (idealExponentNorm 0) = 0
    simp [idealExponentNorm, idealExponentGenerator]

lemma idealVonMangoldt_not_prime_power (ν : EisensteinIdealExponent)
    (hν : ν.support.card ≠ 1) :
    MvPowerSeries.coeff ν idealVonMangoldt = 0 := by
  rw [idealVonMangoldt_coeff, ite_eq_right hν]

/-- Two distinct prime ideal factors annihilate the von Mangoldt weight. -/
lemma idealVonMangoldt_two_primes {ν : EisensteinIdealExponent}
    {p q : EisensteinIdealPrime} (hp : p ∈ ν.support) (hq : q ∈ ν.support)
    (hpq : p ≠ q) : MvPowerSeries.coeff ν idealVonMangoldt = 0 := by
  apply idealVonMangoldt_not_prime_power
  have htwo : ({p, q} : Finset EisensteinIdealPrime) ⊆ ν.support := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> assumption
  have hc := Finset.card_le_card htwo
  rw [Finset.card_pair hpq] at hc
  omega

lemma idealVonMangoldt_coeff_nonneg (ν : EisensteinIdealExponent) :
    0 ≤ MvPowerSeries.coeff ν idealVonMangoldt := by
  rw [idealVonMangoldt_coeff]
  split_ifs
  · apply Finset.sum_nonneg
    intro p hp
    apply Real.log_nonneg
    simpa only [idealExponentNorm_single, pow_one] using
      idealExponentNorm_ge_one (Finsupp.single p 1)
  · exact le_rfl

lemma idealVonMangoldt_coeff_le_logNorm (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt ≤ Real.log (idealExponentNorm ν) := by
  by_cases hc : ν.support.card = 1
  · obtain ⟨p,hp,he⟩ := Finsupp.card_support_eq_one.mp hc
    have hlog : 0 ≤ Real.log (normNat (idealPrimeRepresentative p)) := by
      apply Real.log_nonneg
      simpa only [idealExponentNorm_single, pow_one] using
        idealExponentNorm_ge_one (Finsupp.single p 1)
    have hn : (1 : ℝ) ≤ (ν p : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp
    rw [idealVonMangoldt_coeff, ite_eq_left hc, he, Finsupp.support_single _ hp,
      Finset.sum_singleton, idealExponentNorm_single, Real.log_pow]
    exact le_mul_of_one_le_left hlog hn
  · rw [idealVonMangoldt_not_prime_power ν hc]
    exact Real.log_nonneg (idealExponentNorm_ge_one ν)

lemma idealVonMangoldt_coeff_abs_le_logNorm (ν : EisensteinIdealExponent) :
    |MvPowerSeries.coeff ν idealVonMangoldt| ≤ Real.log (idealExponentNorm ν) := by
  rw [abs_of_nonneg (idealVonMangoldt_coeff_nonneg ν)]
  exact idealVonMangoldt_coeff_le_logNorm ν

lemma idealVonMangoldt_at_prime {a : Eisenstein} (ha : Prime a) :
    MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt = Real.log (norm a) := by
  have hcard : (idealExponentOf a).support.card = 1 := by
    rw [idealExponentOf_support_card ha.irreducible.squarefree,
      UniqueFactorizationMonoid.card_factors_of_irreducible ha.irreducible]
  obtain ⟨p,hp,he⟩ := Finsupp.card_support_eq_one.mp hcard
  have hone : idealExponentOf a p = 1 := by
    have hle := (idealExponentOf_squarefree_iff ha.ne_zero).mpr ha.irreducible.squarefree p
    omega
  calc
    _ = MvPowerSeries.coeff (Finsupp.single p 1) idealVonMangoldt := by rw [he, hone]
    _ = Real.log (normNat (idealPrimeRepresentative p)) := idealVonMangoldt_prime_power p 0
    _ = Real.log (idealExponentNorm (idealExponentOf a)) := by
      rw [he, hone, idealExponentNorm_single, pow_one]
    _ = _ := by rw [idealExponentOf_norm ha.ne_zero]

/-- A nonzero von Mangoldt coefficient at an actual primary element
comes from an actual power of a primary prime, with no residual unit. -/
lemma idealVonMangoldt_primary_support {a : Eisenstein} (ha : primary a)
    (hΛ : MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt ≠ 0) :
    ∃ p : Eisenstein, ∃ j : ℕ, primaryPrime p ∧ 0 < j ∧ a = p ^ j := by
  have hcard : (idealExponentOf a).support.card = 1 := by
    by_contra h
    exact hΛ (idealVonMangoldt_not_prime_power _ h)
  obtain ⟨p, hp, he⟩ := Finsupp.card_support_eq_one.mp hcard
  let j := idealExponentOf a p
  let r := idealPrimeRepresentative p
  have hj : 0 < j := Nat.pos_of_ne_zero hp
  have hgen : idealExponentGenerator (idealExponentOf a) = r ^ j := by
    rw [he]
    exact Finsupp.prod_single_index (h := fun q k => idealPrimeRepresentative q ^ k)
      (pow_zero _)
  have hassoc : Associated (r ^ j) a := by
    rw [← hgen]
    exact idealExponentOf_associated (primary_ne_zero ha)
  have hrdiv : r ∣ a := (dvd_pow_self r hj.ne').trans hassoc.dvd
  have hr : Prime r := (idealPrimeRepresentative_irreducible p).prime
  let q := primaryNormalize r
  have hq : primaryPrime q := ⟨primaryNormalize_primary
    (unit_residue_of_dvd_primary ha hrdiv), prime_primaryNormalize hr⟩
  have hqp : primary (q ^ j) := by
    induction j with
    | zero => simp [primary]
    | succ n ih => simpa only [pow_succ] using primary_mul ih hq.1
  refine ⟨q, j, hq, hj, ?_⟩
  apply primary_associated_eq ha hqp
  exact hassoc.symm.trans ((primaryNormalize_associated r).pow_pow (n := j))

lemma idealVonMangoldt_primary_nonprime_support {a : Eisenstein} (ha : primary a)
    (hprime : ¬ Prime a)
    (hΛ : MvPowerSeries.coeff (idealExponentOf a) idealVonMangoldt ≠ 0) :
    ∃ p : Eisenstein, ∃ j : ℕ, primaryPrime p ∧ 2 ≤ j ∧ a = p ^ j := by
  obtain ⟨p,j,hp,hj,he⟩ := idealVonMangoldt_primary_support ha hΛ
  refine ⟨p,j,hp,?_,he⟩
  by_contra h
  have hje : j = 1 := by omega
  have hae : a = p := by simpa [hje] using he
  apply hprime
  rw [hae]
  exact hp.2

end CubicFirstMoment

end

end OAI
