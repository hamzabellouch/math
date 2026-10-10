import OAI.NumberTheory.JointDickman.Counting.CoefficientCutoffRemoval

namespace OAI

/-! # The size-and-ratio event has probability O(1/B) -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem auxiliaryHalfMass_pair_le {B a c : ℕ} {D : ℝ}
    (hB : 0 < B) (ha : 0 < a) (hc : 0 < c) (hD : 0 ≤ D)
    (hma : primeProductMass (auxiliaryPrimes B) (1 / 2) a ≤
      D * coefficientWeight B a / ((B : ℝ) * a))
    (hmc : primeProductMass (auxiliaryPrimes B) (1 / 2) c ≤
      D * coefficientWeight B c / ((B : ℝ) * c)) :
    primeProductMass (auxiliaryPrimes B) (1 / 2) a *
      primeProductMass (auxiliaryPrimes B) (1 / 2) c ≤
      D^2 / ((B : ℝ)^2 * a * c) * (coefficientWeight B a * coefficientWeight B c) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  calc
    _ ≤ (D * coefficientWeight B a / ((B : ℝ) * a)) *
        (D * coefficientWeight B c / ((B : ℝ) * c)) :=
      mul_le_mul hma hmc (auxiliaryHalfMass_nonneg B c)
        (div_nonneg (mul_nonneg hD (coefficientWeight_nonneg B a)) (mul_nonneg hB0.le ha0.le))
    _ = _ := by field_simp

theorem coefficient_pair_box_mass_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T k : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) → k ∈ Ico B (4 * B) →
      (∑ ac ∈ coefficientDyadicBox T k,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤ K / (B : ℝ)^2 := by
  obtain ⟨D, hD, hdom⟩ := primeProductMass_coefficient_domination hM
  obtain ⟨M, hM0, hmean⟩ := single_coefficient_mean_bound hFord hM (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨3 * D^2 * M^2, by positivity, ?_⟩
  filter_upwards [hdom, hmean, coefficientDyadicBox_scales, eventually_gt_atTop 0]
    with B hd hm hs hB
  intro T k hT hTsize hk
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  let X := 2^k
  have hXnat : 0 < X := pow_pos (by norm_num) _
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hXnat
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hscale := hs T k hTsize hk
  have hlen : Real.exp ((1 / 2 : ℝ) * B) ≤ ((4 * T * X : ℕ) : ℝ) - (T * X : ℕ) := by
    push_cast
    nlinarith only [hscale.1, mul_le_mul_of_nonneg_right hT1 hX0.le]
  have hma := hm (T * X) (4 * T * X) (by nlinarith) hlen
  have hmc := hm X (2 * X) (by omega) (by push_cast; linarith only [hscale.1])
  have hcmean : 0 ≤ ∑ c ∈ Ico X (2 * X), coefficientWeight B c :=
    sum_nonneg fun c _ => coefficientWeight_nonneg B c
  have hprod := mul_le_mul hma hmc hcmean
    (mul_nonneg hM0.le (sub_nonneg.mpr (by exact_mod_cast (show T * X ≤ 4 * T * X by nlinarith))))
  have hpair : (∑ ac ∈ coefficientDyadicBox T k,
      primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤
      D^2 / ((B : ℝ)^2 * (T * X) * X) *
        (∑ a ∈ Ico (T * X) (4 * T * X), coefficientWeight B a) *
        (∑ c ∈ Ico X (2 * X), coefficientWeight B c) := by
    unfold coefficientDyadicBox
    rw [sum_product]
    have hfactor : D^2 / ((B : ℝ)^2 * (T * X) * X) *
        (∑ a ∈ Ico (T * X) (4 * T * X), coefficientWeight B a) *
        (∑ c ∈ Ico X (2 * X), coefficientWeight B c) =
        ∑ a ∈ Ico (T * X) (4 * T * X), ∑ c ∈ Ico X (2 * X),
          D^2 / ((B : ℝ)^2 * (T * X) * X) * (coefficientWeight B a * coefficientWeight B c) := by
      simp only [mul_sum, sum_mul, mul_assoc]
      exact sum_comm
    rw [hfactor]
    apply sum_le_sum
    intro a ha
    apply sum_le_sum
    intro c hc
    have ha' := mem_Ico.mp ha
    have hc' := mem_Ico.mp hc
    have ha0 : 0 < a := lt_of_lt_of_le (Nat.mul_pos hT hXnat) ha'.1
    have hc0 : 0 < c := hXnat.trans_le hc'.1
    have hasize : (a : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) :=
      (by exact_mod_cast ha'.2.le : (a : ℝ) ≤ (4 * T * X : ℝ)).trans hscale.2
    have hcsize : (c : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) := by
      have hh : (c : ℝ) ≤ 2 * X := by exact_mod_cast hc'.2.le
      exact hh.trans ((by nlinarith only [mul_le_mul_of_nonneg_right hT1 hX0.le] :
        (2 * X : ℝ) ≤ 4 * T * X).trans hscale.2)
    apply (auxiliaryHalfMass_pair_le hB ha0 hc0 hD.le (hd a ha0 hasize) (hd c hc0 hcsize)).trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (coefficientWeight_nonneg B a) (coefficientWeight_nonneg B c))
    apply div_le_div_of_nonneg_left (sq_nonneg D) (by positivity)
    have haR : (T * X : ℝ) ≤ a := by exact_mod_cast ha'.1
    have hcR : (X : ℝ) ≤ c := by exact_mod_cast hc'.1
    gcongr
  calc
    _ ≤ _ := hpair
    _ ≤ D^2 / ((B : ℝ)^2 * (T * X) * X) *
        ((M * (((4 * T * X : ℕ) : ℝ) - (T * X : ℕ))) *
          (M * (((2 * X : ℕ) : ℝ) - X))) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by
      push_cast
      field_simp
      ring

theorem coefficient_size_ratio_event_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      (B : ℝ) * (∑ ac ∈ amplificationCoefficientPairs B T,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤ K := by
  obtain ⟨K, hK, hbound⟩ := coefficient_pair_box_mass_bound hFord hM
  refine ⟨4 * K, by positivity, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hb hB
  intro T hT hTsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hsum : (∑ ac ∈ amplificationCoefficientPairs B T,
      primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤
      ((Ico B (4 * B)).card : ℝ) * (K / (B : ℝ)^2) := by
    calc
      _ ≤ ∑ ac ∈ coefficientDyadicCover B T,
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
            primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun ac _ _ => mul_nonneg (auxiliaryHalfMass_nonneg B ac.1) (auxiliaryHalfMass_nonneg B ac.2))
      _ = ∑ k ∈ Ico B (4 * B), ∑ ac ∈ coefficientDyadicBox T k,
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
            primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2 := by
        apply sum_biUnion
        intro k _ l _ hkl
        exact coefficientDyadicBox_disjoint T hkl
      _ ≤ ∑ _k ∈ Ico B (4 * B), K / (B : ℝ)^2 :=
        sum_le_sum fun k hk => hb T k hT hTsize hk
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  have hcard : ((Ico B (4 * B)).card : ℝ) ≤ 4 * B := by
    exact_mod_cast (show (Ico B (4 * B)).card ≤ 4 * B by rw [Nat.card_Ico]; omega)
  calc
    _ ≤ (B : ℝ) * (((Ico B (4 * B)).card : ℝ) * (K / (B : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left hsum hB0.le
    _ ≤ (B : ℝ) * ((4 * B) * (K / (B : ℝ)^2)) := by gcongr
    _ = _ := by field_simp

end JointDickman

end OAI
