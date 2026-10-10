import OAI.NumberTheory.DirichletL.Foundation

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredExceptionalCount
open UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

def valuation (I P : Ideal O) : ℕ := (normalizedFactors I).count P

def factorMultiset (I : Ideal O) (e : ℕ → ℕ) : Multiset (Ideal O) :=
  ∑ P ∈ (normalizedFactors I).toFinset, Multiset.replicate (e (valuation I P)) P

theorem factorMultiset_subset (I : Ideal O) (e : ℕ → ℕ) :
    factorMultiset I e ⊆ normalizedFactors I := by
  intro P hP
  obtain ⟨Q, hQ, hPQ⟩ := Multiset.mem_sum.mp hP
  have he : P = Q := (Multiset.mem_replicate.mp hPQ).2
  exact he ▸ Multiset.mem_toFinset.mp hQ

theorem factorMultiset_count (I P : Ideal O) (e : ℕ → ℕ) (he : e 0 = 0) :
    (factorMultiset I e).count P = e (valuation I P) := by
  unfold factorMultiset
  simp only [Multiset.count_sum', Multiset.count_replicate, Finset.sum_ite_eq']
  split_ifs with hP
  · rfl
  · have hz : valuation I P = 0 := Multiset.count_eq_zero.mpr
      (fun h => hP (Multiset.mem_toFinset.mpr h))
    rw [hz, he]

def factorPart (I : Ideal O) (e : ℕ → ℕ) : Ideal O := (factorMultiset I e).prod

theorem factorPart_ne_zero (I : Ideal O) (e : ℕ → ℕ) : factorPart I e ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (factorMultiset_subset I e)

theorem factorPart_valuation (I P : Ideal O) (e : ℕ → ℕ) (he : e 0 = 0) :
    valuation (factorPart I e) P = e (valuation I P) := by
  unfold valuation factorPart
  rw [normalizedFactors_prod_eq_self_of_subset (factorMultiset_subset I e)]
  exact factorMultiset_count I P e he

def sixthRemainder (I : Ideal O) : Ideal O := factorPart I (fun n => n % 6)

def sixthQuotient (I : Ideal O) : Ideal O := factorPart I (fun n => n / 6)

theorem sixthRemainder_ne_zero (I : Ideal O) : sixthRemainder I ≠ 0 := factorPart_ne_zero I _
theorem sixthQuotient_ne_zero (I : Ideal O) : sixthQuotient I ≠ 0 := factorPart_ne_zero I _

@[simp] theorem sixthRemainder_valuation (I P : Ideal O) :
    valuation (sixthRemainder I) P = valuation I P % 6 :=
  factorPart_valuation I P _ (by norm_num)

@[simp] theorem sixthQuotient_valuation (I P : Ideal O) :
    valuation (sixthQuotient I) P = valuation I P / 6 :=
  factorPart_valuation I P _ (by norm_num)

theorem valuation_mul (I J P : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    valuation (I * J) P = valuation I P + valuation J P := by
  simp only [valuation, normalizedFactors_mul hI hJ, Multiset.count_add]

theorem valuation_pow (I P : Ideal O) (n : ℕ) :
    valuation (I ^ n) P = n * valuation I P := by
  simp only [valuation, normalizedFactors_pow, Multiset.count_nsmul]

theorem ideal_eq_of_valuation_eq {I J : Ideal O} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ P, valuation I P = valuation J P) : I = J := by
  rw [← Ideal.prod_normalizedFactors_eq_self hI, ← Ideal.prod_normalizedFactors_eq_self hJ]
  exact congrArg Multiset.prod (Multiset.ext.mpr h)

theorem sixth_normal_form (I : Ideal O) (hI : I ≠ 0) :
    sixthRemainder I * sixthQuotient I ^ 6 = I := by
  apply ideal_eq_of_valuation_eq
    (mul_ne_zero (sixthRemainder_ne_zero I) (pow_ne_zero _ (sixthQuotient_ne_zero I))) hI
  intro P
  rw [valuation_mul _ _ _ (sixthRemainder_ne_zero I)
    (pow_ne_zero _ (sixthQuotient_ne_zero I)), valuation_pow,
    sixthRemainder_valuation, sixthQuotient_valuation]
  omega

theorem sixthRemainder_valuation_lt (I P : Ideal O) : valuation (sixthRemainder I) P < 6 := by
  rw [sixthRemainder_valuation]
  omega

theorem sixthRemainder_eq_iff (I J : Ideal O) :
    sixthRemainder I = sixthRemainder J ↔
      ∀ P, valuation I P % 6 = valuation J P % 6 := by
  constructor
  · intro h P
    simpa only [sixthRemainder_valuation] using congrArg (fun K => valuation K P) h
  · intro h
    exact ideal_eq_of_valuation_eq (sixthRemainder_ne_zero I) (sixthRemainder_ne_zero J)
      (by simpa only [sixthRemainder_valuation] using h)

theorem sixth_normal_form_unique {A B C D : Ideal O}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hAf : ∀ P, valuation A P < 6) (hCf : ∀ P, valuation C P < 6)
    (h : A * B ^ 6 = C * D ^ 6) : A = C ∧ B = D := by
  have hv (P : Ideal O) := congrArg (fun I => valuation I P) h
  simp only [valuation_mul _ _ _ hA (pow_ne_zero _ hB),
    valuation_mul _ _ _ hC (pow_ne_zero _ hD), valuation_pow] at hv
  have he (P : Ideal O) : valuation A P = valuation C P ∧ valuation B P = valuation D P := by
    have := hv P
    have := hAf P
    have := hCf P
    omega
  exact ⟨ideal_eq_of_valuation_eq hA hC (fun P => (he P).1),
    ideal_eq_of_valuation_eq hB hD (fun P => (he P).2)⟩

theorem sixthQuotient_injective_on_remainder {I J : Ideal O}
    (hI : I ≠ 0) (hJ : J ≠ 0) (hr : sixthRemainder I = sixthRemainder J)
    (hq : sixthQuotient I = sixthQuotient J) : I = J := by
  rw [← sixth_normal_form I hI, ← sixth_normal_form J hJ, hr, hq]

theorem sixthRemainder_eq_of_profile {I R : Ideal O} (hR : R ≠ 0)
    (hprofile : ∀ P, valuation I P % 6 = valuation R P) : sixthRemainder I = R := by
  apply ideal_eq_of_valuation_eq (sixthRemainder_ne_zero I) hR
  intro P
  simpa only [sixthRemainder_valuation] using hprofile P

theorem forced_fourth_power_dvd (I D : Ideal O) (hD : Squarefree D)
    (hfour : ∀ P ∈ normalizedFactors D, valuation I P % 6 = 4) :
    D ^ 4 ∣ sixthRemainder I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hD.ne_zero)
    (sixthRemainder_ne_zero I)).mpr
  apply Multiset.le_iff_count.mpr
  intro P
  change valuation (D ^ 4) P ≤ valuation (sixthRemainder I) P
  rw [valuation_pow, sixthRemainder_valuation]
  have hcount : valuation D P ≤ 1 := Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors hD.ne_zero).mp hD) P
  by_cases hP : P ∈ normalizedFactors D
  · rw [hfour P hP]
    omega
  · have hz : valuation D P = 0 := Multiset.count_eq_zero.mpr hP
    simp only [hz, mul_zero, Nat.zero_le]

theorem norm_pos {I : Ideal O} (hI : I ≠ 0) : 0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_one_le {I : Ideal O} (hI : I ≠ 0) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_le_of_dvd {I J : Ideal O} (hJ : J ≠ 0) (hIJ : I ∣ J) :
    (Ideal.absNorm I : ℝ) ≤ (Ideal.absNorm J : ℝ) := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h)))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hIJ))

theorem forced_fourth_power_norm_le (I D : Ideal O) (hD : Squarefree D)
    (hfour : ∀ P ∈ normalizedFactors D, valuation I P % 6 = 4) :
    (Ideal.absNorm D : ℝ) ^ 4 ≤ (Ideal.absNorm (sixthRemainder I) : ℝ) := by
  simpa only [map_pow, Nat.cast_pow] using
    norm_le_of_dvd (sixthRemainder_ne_zero I) (forced_fourth_power_dvd I D hD hfour)

theorem sixth_normal_form_norm (I : Ideal O) (hI : I ≠ 0) :
    (Ideal.absNorm (sixthRemainder I) : ℝ) *
      (Ideal.absNorm (sixthQuotient I) : ℝ) ^ 6 = (Ideal.absNorm I : ℝ) := by
  have h := congrArg (fun J : Ideal O => (Ideal.absNorm J : ℝ)) (sixth_normal_form I hI)
  simpa only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] using h

theorem sixthRemainder_norm_le (I : Ideal O) (hI : I ≠ 0) :
    (Ideal.absNorm (sixthRemainder I) : ℝ) ≤ (Ideal.absNorm I : ℝ) :=
  norm_le_of_dvd hI ⟨sixthQuotient I ^ 6, (sixth_normal_form I hI).symm⟩

theorem sixthQuotient_norm_le (I : Ideal O) (hI : I ≠ 0) {H : ℝ} (hH : 0 ≤ H)
    (hNI : (Ideal.absNorm I : ℝ) ≤ H) :
    (Ideal.absNorm (sixthQuotient I) : ℝ) ≤
      (H / Ideal.absNorm (sixthRemainder I)) ^ (1 / 6 : ℝ) := by
  have hr := norm_pos (sixthRemainder_ne_zero I)
  have hp : (Ideal.absNorm (sixthQuotient I) : ℝ) ^ (6 : ℝ) ≤
      H / Ideal.absNorm (sixthRemainder I) := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, le_div_iff₀ hr]
    rw [mul_comm, sixth_normal_form_norm I hI]
    exact hNI
  simpa only [one_div] using
    (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) (div_nonneg hH hr.le)
      (by norm_num : (0 : ℝ) < 6)).mpr hp

theorem empty_of_below_remainder (S : Finset (Ideal O)) (R : Ideal O) {H : ℝ}
    (hS : ∀ I ∈ S, I ≠ 0) (hR : ∀ I ∈ S, sixthRemainder I = R)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H)
    (hH : H < Ideal.absNorm R) : S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro I hI
  have hn := sixthRemainder_norm_le I (hS I hI)
  rw [hR I hI] at hn
  exact (not_le_of_gt hH) (hn.trans (hN I hI))

theorem ideal_count_fixed_remainder (S : Finset (Ideal O)) (R : Ideal O) (hR : R ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hS : ∀ I ∈ S, I ≠ 0)
    (hrem : ∀ I ∈ S, sixthRemainder I = R)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (S.card : ℝ) ≤ 128 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
  by_cases hne : S.Nonempty
  · have hqbound (I : Ideal O) (hI : I ∈ S) :
        (Ideal.absNorm (sixthQuotient I) : ℝ) ≤ (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
      simpa only [hrem I hI] using sixthQuotient_norm_le I (hS I hI) hH (hN I hI)
    obtain ⟨I, hI⟩ := hne
    have hscale : 1 ≤ (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) :=
      (norm_one_le (sixthQuotient_ne_zero I)).trans (hqbound I hI)
    have hinj : Set.InjOn sixthQuotient S := by
      intro I hI J hJ he
      exact sixthQuotient_injective_on_remainder (hS I hI) (hS J hJ)
        ((hrem I hI).trans (hrem J hJ).symm) he
    have hc := DescentFiberCost.finite_ideal_count_real (S.image sixthQuotient)
      ((H / Ideal.absNorm R) ^ (1 / 6 : ℝ)) hscale
      (by intro J hJ; obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
          exact sixthQuotient_ne_zero I)
      (by intro J hJ; obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
          exact hqbound I hI)
    rwa [Finset.card_image_iff.mpr hinj] at hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (div_nonneg hH (norm_pos hR).le) _)

theorem ideal_count_valuation_profile (S : Finset (Ideal O)) (R : Ideal O) (hR : R ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hS : ∀ I ∈ S, I ≠ 0)
    (hprofile : ∀ I ∈ S, ∀ P, valuation I P % 6 = valuation R P)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (S.card : ℝ) ≤ 128 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) :=
  ideal_count_fixed_remainder S R hR H hH hS
    (fun I hI => sixthRemainder_eq_of_profile hR (hprofile I hI)) hN

theorem ideal_count_remainder_family (S Rs : Finset (Ideal O))
    (hRs : ∀ R ∈ Rs, R ≠ 0) (H : ℝ) (hH : 0 ≤ H)
    (hS : ∀ I ∈ S, I ≠ 0) (hrem : ∀ I ∈ S, sixthRemainder I ∈ Rs)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (S.card : ℝ) ≤ ∑ R ∈ Rs, 128 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
  rw [Finset.card_eq_sum_card_fiberwise (t := Rs) hrem, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro R hR
  exact ideal_count_fixed_remainder (S.filter (fun I => sixthRemainder I = R)) R
    (hRs R hR) H hH
    (fun I hI => hS I (Finset.mem_filter.mp hI).1)
    (fun I hI => (Finset.mem_filter.mp hI).2)
    (fun I hI => hN I (Finset.mem_filter.mp hI).1)

theorem ideal_count_of_remainder_norm_lower (S : Finset (Ideal O)) (R : Ideal O)
    (hR : R ≠ 0) (H L : ℝ) (hH : 0 ≤ H) (hL : 0 < L)
    (hLR : L ≤ Ideal.absNorm R) (hS : ∀ I ∈ S, I ≠ 0)
    (hrem : ∀ I ∈ S, sixthRemainder I = R)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (S.card : ℝ) ≤ 128 * (H / L) ^ (1 / 6 : ℝ) := by
  apply (ideal_count_fixed_remainder S R hR H hH hS hrem hN).trans
  gcongr

theorem element_count_le_six_ideal_count (S : Finset O) (hS : ∀ z ∈ S, z ≠ 0) :
    (S.card : ℝ) ≤ 6 * ((S.image (fun z => Ideal.span {z})).card : ℝ) := by
  have h := CompletedUnitRows.sum_nonzero_element_le_units S hS (fun _ => 1)
    (fun _ => by norm_num)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    CompletedUnitRows.unit_card, Nat.cast_ofNat] using h

theorem element_count_fixed_remainder (S : Finset O) (R : Ideal O) (hR : R ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hS : ∀ z ∈ S, z ≠ 0)
    (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) = R)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ H) :
    (S.card : ℝ) ≤ 768 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
  have hc := ideal_count_fixed_remainder (S.image (fun z => Ideal.span {z})) R hR H hH
    (by intro I hI; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
        exact Ideal.span_singleton_eq_bot.not.mpr (hS z hz))
    (by intro I hI; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
        exact hrem z hz)
    (by intro I hI; obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
        exact hN z hz)
  calc
    (S.card : ℝ) ≤ 6 * ((S.image (fun z => Ideal.span {z})).card : ℝ) :=
      element_count_le_six_ideal_count S hS
    _ ≤ 6 * (128 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ)) := by gcongr
    _ = 768 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by ring

theorem element_count_valuation_profile (S : Finset O) (R : Ideal O) (hR : R ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hS : ∀ z ∈ S, z ≠ 0)
    (hprofile : ∀ z ∈ S, ∀ P, valuation (Ideal.span {z}) P % 6 = valuation R P)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ H) :
    (S.card : ℝ) ≤ 768 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) :=
  element_count_fixed_remainder S R hR H hH hS
    (fun z hz => sixthRemainder_eq_of_profile hR (hprofile z hz)) hN

theorem element_count_remainder_family (S : Finset O) (Rs : Finset (Ideal O))
    (hRs : ∀ R ∈ Rs, R ≠ 0) (H : ℝ) (hH : 0 ≤ H)
    (hS : ∀ z ∈ S, z ≠ 0) (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) ∈ Rs)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ H) :
    (S.card : ℝ) ≤ ∑ R ∈ Rs, 768 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) := by
  rw [Finset.card_eq_sum_card_fiberwise (t := Rs) hrem, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro R hR
  exact element_count_fixed_remainder (S.filter (fun z => sixthRemainder (Ideal.span {z}) = R)) R
    (hRs R hR) H hH
    (fun z hz => hS z (Finset.mem_filter.mp hz).1)
    (fun z hz => (Finset.mem_filter.mp hz).2)
    (fun z hz => hN z (Finset.mem_filter.mp hz).1)

theorem elements_empty_of_below_remainder (S : Finset O) (R : Ideal O) {H : ℝ}
    (hS : ∀ z ∈ S, z ≠ 0) (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) = R)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ H)
    (hH : H < Ideal.absNorm R) : S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hn := sixthRemainder_norm_le (Ideal.span {z})
    (Ideal.span_singleton_eq_bot.not.mpr (hS z hz))
  rw [hrem z hz] at hn
  exact (not_le_of_gt hH) (hn.trans (hN z hz))

theorem element_count_power_scale (S : Finset O) (R : Ideal O) (hR : R ≠ 0)
    (Z C m d : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hRnorm : Z ^ d ≤ (Ideal.absNorm R : ℝ)) (hS : ∀ z ∈ S, z ≠ 0)
    (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) = R)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ m) :
    (S.card : ℝ) ≤ 768 * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
  have hM : 0 ≤ C * Z ^ m := mul_nonneg hC (Real.rpow_nonneg hZ.le _)
  have hdiv : (C * Z ^ m) / Ideal.absNorm R ≤ (C * Z ^ m) / Z ^ d :=
    div_le_div_of_nonneg_left hM (Real.rpow_pos_of_pos hZ _) hRnorm
  calc
    (S.card : ℝ) ≤ 768 * ((C * Z ^ m) / Ideal.absNorm R) ^ (1 / 6 : ℝ) :=
      element_count_fixed_remainder S R hR _ hM hS hrem hN
    _ ≤ 768 * ((C * Z ^ m) / Z ^ d) ^ (1 / 6 : ℝ) := by gcongr
    _ = 768 * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
      rw [mul_div_assoc, ← Real.rpow_sub hZ, Real.mul_rpow hC (Real.rpow_nonneg hZ.le _),
        ← Real.rpow_mul hZ.le]
      rw [show (m - d) * (1 / 6 : ℝ) = (m - d) / 6 by ring, mul_assoc]

theorem ideal_count_power_scale (S : Finset (Ideal O)) (R : Ideal O) (hR : R ≠ 0)
    (Z C m d : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hRnorm : Z ^ d ≤ (Ideal.absNorm R : ℝ)) (hS : ∀ I ∈ S, I ≠ 0)
    (hrem : ∀ I ∈ S, sixthRemainder I = R)
    (hN : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ C * Z ^ m) :
    (S.card : ℝ) ≤ 128 * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
  have hM : 0 ≤ C * Z ^ m := mul_nonneg hC (Real.rpow_nonneg hZ.le _)
  have hdiv : (C * Z ^ m) / Ideal.absNorm R ≤ (C * Z ^ m) / Z ^ d :=
    div_le_div_of_nonneg_left hM (Real.rpow_pos_of_pos hZ _) hRnorm
  calc
    (S.card : ℝ) ≤ 128 * ((C * Z ^ m) / Ideal.absNorm R) ^ (1 / 6 : ℝ) :=
      ideal_count_fixed_remainder S R hR _ hM hS hrem hN
    _ ≤ 128 * ((C * Z ^ m) / Z ^ d) ^ (1 / 6 : ℝ) := by gcongr
    _ = 128 * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
      rw [mul_div_assoc, ← Real.rpow_sub hZ, Real.mul_rpow hC (Real.rpow_nonneg hZ.le _),
        ← Real.rpow_mul hZ.le]
      rw [show (m - d) * (1 / 6 : ℝ) = (m - d) / 6 by ring, mul_assoc]

theorem element_count_forced_fourth_power (S : Finset O) (R D : Ideal O)
    (hR : R ≠ 0) (hD : Squarefree D) (Z C m f : ℝ)
    (hZ : 0 < Z) (hC : 0 ≤ C) (hDnorm : Z ^ (f / 2) ≤ (Ideal.absNorm D : ℝ))
    (hS : ∀ z ∈ S, z ≠ 0) (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) = R)
    (hfour : ∀ z ∈ S, ∀ P ∈ normalizedFactors D, valuation (Ideal.span {z}) P % 6 = 4)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ m) :
    (S.card : ℝ) ≤ 768 * C ^ (1 / 6 : ℝ) * Z ^ ((m - 2 * f) / 6) := by
  by_cases hne : S.Nonempty
  · obtain ⟨z, hz⟩ := hne
    have hforced := forced_fourth_power_norm_le (Ideal.span {z}) D hD (hfour z hz)
    rw [hrem z hz] at hforced
    have hRnorm : Z ^ (2 * f) ≤ (Ideal.absNorm R : ℝ) := by
      calc
        Z ^ (2 * f) = (Z ^ (f / 2)) ^ (4 : ℕ) := by
          rw [← Real.rpow_mul_natCast hZ.le]
          congr 1
          norm_num
          ring
        _ ≤ (Ideal.absNorm D : ℝ) ^ (4 : ℕ) := by gcongr
        _ ≤ (Ideal.absNorm R : ℝ) := hforced
    exact element_count_power_scale S R hR Z C m (2 * f) hZ hC hRnorm hS hrem hN
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    positivity

theorem element_count_forced_fourth_power_weaker (S : Finset O) (R D : Ideal O)
    (hR : R ≠ 0) (hD : Squarefree D) (Z C m f : ℝ)
    (hZ : 1 ≤ Z) (hC : 0 ≤ C) (hf : 0 ≤ f)
    (hDnorm : Z ^ (f / 2) ≤ (Ideal.absNorm D : ℝ))
    (hS : ∀ z ∈ S, z ≠ 0) (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) = R)
    (hfour : ∀ z ∈ S, ∀ P ∈ normalizedFactors D, valuation (Ideal.span {z}) P % 6 = 4)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ m) :
    (S.card : ℝ) ≤ 768 * C ^ (1 / 6 : ℝ) * Z ^ ((m - f) / 6) := by
  apply (element_count_forced_fourth_power S R D hR hD Z C m f
    (zero_lt_one.trans_le hZ) hC hDnorm hS hrem hfour hN).trans
  gcongr
  linarith

theorem valuation_eq_multiplicity {I P : Ideal O} (hI : I ≠ 0) (hP : Prime P) :
    valuation I P = multiplicity P I := by
  simpa only [valuation, normalize_eq] using
    (multiplicity_eq_count_normalizedFactors hP.irreducible hI).symm

theorem sixthRemainder_eq_of_prime_profile {I R : Ideal O} (hR : R ≠ 0)
    (hprofile : ∀ P, Prime P → valuation I P % 6 = valuation R P) :
    sixthRemainder I = R := by
  apply sixthRemainder_eq_of_profile hR
  intro P
  by_cases hP : Prime P
  · exact hprofile P hP
  · have hI0 : valuation I P = 0 := Multiset.count_eq_zero.mpr
      (fun h => hP (prime_of_normalized_factor P h))
    have hR0 : valuation R P = 0 := Multiset.count_eq_zero.mpr
      (fun h => hP (prime_of_normalized_factor P h))
    simp only [hI0, hR0, Nat.zero_mod]

theorem element_count_power_scale_family (S : Finset O) (Rs : Finset (Ideal O))
    (hRs : ∀ R ∈ Rs, R ≠ 0) (Z C m d : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hRnorm : ∀ R ∈ Rs, Z ^ d ≤ (Ideal.absNorm R : ℝ))
    (hS : ∀ z ∈ S, z ≠ 0) (hrem : ∀ z ∈ S, sixthRemainder (Ideal.span {z}) ∈ Rs)
    (hN : ∀ z ∈ S, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ m) :
    (S.card : ℝ) ≤ 768 * (Rs.card : ℝ) * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
  have hcard : (S.card : ℝ) =
      ∑ R ∈ Rs, ((S.filter (fun z => sixthRemainder (Ideal.span {z}) = R)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (t := Rs) hrem
  rw [hcard]
  calc
    _ ≤ ∑ R ∈ Rs, 768 * C ^ (1 / 6 : ℝ) * Z ^ ((m - d) / 6) := by
      apply Finset.sum_le_sum
      intro R hR
      exact element_count_power_scale
        (S.filter (fun z => sixthRemainder (Ideal.span {z}) = R)) R (hRs R hR)
        Z C m d hZ hC (hRnorm R hR)
        (fun z hz => hS z (Finset.mem_filter.mp hz).1)
        (fun z hz => (Finset.mem_filter.mp hz).2)
        (fun z hz => hN z (Finset.mem_filter.mp hz).1)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem element_count_squareNorm (S : Finset O) (R : Ideal O) (hR : R ≠ 0)
    (H : ℝ) (hH : 0 ≤ H) (hS : ∀ z ∈ S, z ≠ 0)
    (hprofile : ∀ z ∈ S, ∀ P, Prime P → valuation (Ideal.span {z}) P % 6 = valuation R P)
    (hN : ∀ z ∈ S, ‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 ≤ H) :
    (S.card : ℝ) ≤ 768 * (H / Ideal.absNorm R) ^ (1 / 6 : ℝ) :=
  element_count_fixed_remainder S R hR H hH hS
    (fun z hz => sixthRemainder_eq_of_prime_profile hR (hprofile z hz))
    (fun z hz => by simpa only [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] using hN z hz)

end SevenEighths.CenteredExceptionalCount
end

end OAI
