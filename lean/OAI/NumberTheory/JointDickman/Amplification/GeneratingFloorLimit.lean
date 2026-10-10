import OAI.NumberTheory.JointDickman.Amplification.MarginalTupleDischarge
import OAI.NumberTheory.JointDickman.Arithmetic.BoundedPrimeSubsets

namespace OAI

/-! # Vanishing floor errors for the actual large-prime generating functions -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem allLargeBinPrimes_eq_largePrimeSet (J : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    allLargeBinPrimes J x = largePrimeSet x (x^((1 : ℝ)/J)) := by
  ext p
  simp only [allLargeBinPrimes,largePrimeSet,mem_filter,mem_Ioc,Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hl,hu⟩,hp⟩
    exact ⟨⟨hu,hp⟩,Nat.lt_of_floor_lt hl⟩
  · rintro ⟨⟨hu,hp⟩,hl⟩
    exact ⟨⟨(Nat.floor_lt (Real.rpow_nonneg hx _)).mpr hl,hu⟩,hp⟩

theorem primeTupleCount_mono_bound (P : Finset ℕ) (h : ℕ) {M N : ℝ} (hMN : M ≤ N) :
    primeTupleCount P h M ≤ primeTupleCount P h N := by
  classical
  apply card_le_card
  intro f hf
  exact mem_filter.mpr ⟨(mem_filter.mp hf).1,((mem_filter.mp hf).2).trans hMN⟩

theorem primeTupleCount_zero_le_one (P : Finset ℕ) (N : ℝ) :
    primeTupleCount P 0 N ≤ 1 := by
  classical
  exact (card_filter_le _ _).trans_eq (by simp)

theorem largePrimeTupleCount_floor_scaled_tendsto_zero (h : ℕ) {J : ℕ}
    (hJ : 0 < J) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ =>
      (primeTupleCount (allLargeBinPrimes J x) h (⌊A*x⌋₊ : ℝ) : ℝ)/(A*x))
      atTop (𝓝 0) := by
  cases h with
  | zero =>
    have hlim : Tendsto (fun x : ℝ => 1/(A*x)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop hA)
    apply squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg hA.le hx.le)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      apply div_le_div_of_nonneg_right _ (mul_nonneg hA.le hx.le)
      exact_mod_cast primeTupleCount_zero_le_one (allLargeBinPrimes J x) (⌊A*x⌋₊ : ℝ)
  | succ h =>
    have hc : 0 < (1 : ℝ)/J := by positivity
    have hc1 : (1 : ℝ)/J ≤ 1 := (div_le_one (by positivity)).mpr (by exact_mod_cast hJ)
    have hlim := largePrimeTupleCount_scaled_tendsto_zero h hA hc hc1
    apply squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg hA.le hx.le)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [allLargeBinPrimes_eq_largePrimeSet J hx.le]
      apply div_le_div_of_nonneg_right _ (mul_nonneg hA.le hx.le)
      exact_mod_cast primeTupleCount_mono_bound (largePrimeSet x (x^((1 : ℝ)/J))) (h+1)
        (Nat.floor_le (mul_nonneg hA.le hx.le))

theorem boundedPrimeSubsets_density_tendsto_zero {J : ℕ} (hJ : 0 < J)
    {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ =>
      ((boundedPrimeSubsets (allLargeBinPrimes J x) ⌊A*x⌋₊).card : ℝ)/(A*x))
      atTop (𝓝 0) := by
  have hlim := tendsto_finsetSum (range (J+1)) (fun h _ =>
    largePrimeTupleCount_floor_scaled_tendsto_zero h hJ hA)
  simp only [sum_const_zero] at hlim
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg hA.le hx.le)
  · filter_upwards [bounded_largePrimeSubsets_eventually J hJ A,
      eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have hb : ((boundedPrimeSubsets (allLargeBinPrimes J x) ⌊A*x⌋₊).card : ℝ) ≤
        ∑ h ∈ range (J+1), (primeTupleCount (allLargeBinPrimes J x) h (⌊A*x⌋₊ : ℝ) : ℝ) := by
      exact_mod_cast boundedPrimeSubsets_card_le (allLargeBinPrimes J x) ⌊A*x⌋₊ J hx
    simpa only [sum_div] using div_le_div_of_nonneg_right hb (mul_nonneg hA.le hx0.le)

theorem generating_floor_error_tendsto_zero {J : ℕ} (hJ : 0 < J)
    {A : ℝ} (hA : 0 < A) (z : ℝ → ℕ → ℝ)
    (hz : ∀ x p, 0 ≤ z x p ∧ z x p ≤ 1) :
    Tendsto (fun x : ℝ =>
      (primeGeneratingAverage (allLargeBinPrimes J x) (z x) ⌊A*x⌋₊ -
        primeGeneratingModel (allLargeBinPrimes J x) (z x) ⌊A*x⌋₊) *
          (⌊A*x⌋₊ : ℝ)/(A*x)) atTop (𝓝 0) := by
  have hN := tendsto_nat_floor_atTop.comp (tendsto_id.const_mul_atTop hA)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (boundedPrimeSubsets_density_tendsto_zero hJ hA)
  filter_upwards [hN.eventually (eventually_ge_atTop 1),
    eventually_gt_atTop (0 : ℝ)] with x hNx hx
  change 1 ≤ ⌊A*x⌋₊ at hNx
  have hn : 0 < ⌊A*x⌋₊ := hNx
  have hnr : (0 : ℝ) < ⌊A*x⌋₊ := by exact_mod_cast hn
  have hAx : 0 < A*x := mul_pos hA hx
  have hb := primeGeneratingModel_error (allLargeBinPrimes J x)
    (fun p hp => (mem_filter.mp hp).2) (z x) hn (by norm_num : (0 : ℝ) ≤ 1)
    (fun D _ => generating_coefficient_le_one (z x) (hz x) D)
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_nonneg (Nat.cast_nonneg ⌊A*x⌋₊ : (0 : ℝ) ≤ (⌊A*x⌋₊ : ℝ)),abs_of_pos hAx]
  calc
    _ ≤ ((1*((boundedPrimeSubsets (allLargeBinPrimes J x) ⌊A*x⌋₊).card : ℝ)/⌊A*x⌋₊) *
        ⌊A*x⌋₊)/(A*x) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb hnr.le) hAx.le
    _ = _ := by field_simp

end JointDickman

end OAI
