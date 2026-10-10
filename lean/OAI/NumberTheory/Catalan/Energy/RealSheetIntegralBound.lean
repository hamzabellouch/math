import OAI.NumberTheory.Catalan.Estimates.RealEnergyTwoProduct

namespace OAI


noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace InternalCatalan

private theorem pair_product_eq_zero_of_not_injective {m : ℕ}
    (v : Fin m → ℝ) (hv : ¬Function.Injective v) :
    (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (v j - v i)) = 0 := by
  have hd : (Matrix.vandermonde v).det = 0 := by
    by_contra hd
    exact hv (Matrix.det_vandermonde_ne_zero_iff.mp hd)
  simpa only [Matrix.det_vandermonde] using hd

theorem sheetRealIntegrand_eq_zero_of_not_injective_x (N : ℕ)
    (x s : Fin (n N) → ℝ) (hx : ¬Function.Injective x) :
    sheetRealIntegrand N x s = 0 := by
  have hcomp : ¬Function.Injective (fun i => realCoordinateInv (x i)) := by
    intro h
    apply hx
    intro i j hij
    exact h (congrArg realCoordinateInv hij)
  have hz := pair_product_eq_zero_of_not_injective
    (fun i => realCoordinateInv (x i)) hcomp
  simp only [sheetRealIntegrand, hz, mul_zero, zero_mul, zero_div]

theorem sheetRealIntegrand_eq_zero_of_not_injective_s (N : ℕ)
    (x s : Fin (n N) → ℝ) (hs : ¬Function.Injective s) :
    sheetRealIntegrand N x s = 0 := by
  have hz := pair_product_eq_zero_of_not_injective s hs
  simp only [sheetRealIntegrand, hz, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_mul, zero_div]

theorem ae_realCoordinate_pair_domain (N : ℕ) :
    ∀ᵐ p ∂realCoordinateListPairMeasure N,
      (∀ i, p.1 i ∈ Ioo (-1 : ℝ) 1 ∧ p.1 i ≠ 0) ∧
        (∀ j, p.2 j ∈ Ioo (0 : ℝ) 1) := by
  have hx : ∀ᵐ p ∂realCoordinateListPairMeasure N,
      ∀ i, p.1 i ∈ Ioo (-1 : ℝ) 1 ∧ p.1 i ≠ 0 :=
    (Measure.quasiMeasurePreserving_fst
      (μ := Measure.pi (fun _ : Fin (n N) => realCoordinateMeasure))
      (ν := Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))).tendsto_ae.eventually
        (ae_realCoordinate_list_regular N)
  have hslist : ∀ᵐ s ∂Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)),
      ∀ j, s j ∈ Ioo (0 : ℝ) 1 :=
    Filter.eventually_all.2 (fun j =>
      (Measure.tendsto_eval_ae_ae
        (μ := fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)) (i := j)).eventually
          (ae_restrict_mem measurableSet_Ioo))
  have hs : ∀ᵐ p ∂realCoordinateListPairMeasure N,
      ∀ j, p.2 j ∈ Ioo (0 : ℝ) 1 :=
    (Measure.quasiMeasurePreserving_snd
      (μ := Measure.pi (fun _ : Fin (n N) => realCoordinateMeasure))
      (ν := Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))).tendsto_ae.eventually
        hslist
  exact hx.and hs

theorem realCoordinateListPairMeasure_univ (N : ℕ) :
    realCoordinateListPairMeasure N univ = (2 : ℝ≥0∞) ^ n N := by
  unfold realCoordinateListPairMeasure
  rw [← Set.univ_prod_univ, Measure.prod_prod]
  simp [Measure.pi_univ, realCoordinateMeasure_univ]

theorem realCoordinateListPairMeasure_real_univ (N : ℕ) :
    (realCoordinateListPairMeasure N).real univ = (2 : ℝ) ^ n N := by
  rw [measureReal_def, realCoordinateListPairMeasure_univ, ENNReal.toReal_pow]
  norm_num

theorem ae_abs_sheetRealIntegrand_le_of_regular_bound (N : ℕ) {B : ℝ}
    (hB : 0 ≤ B)
    (hbound : ∀ (x s : Fin (n N) → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      |sheetRealIntegrand N x s| ≤ B) :
    ∀ᵐ p ∂realCoordinateListPairMeasure N, |sheetRealIntegrand N p.1 p.2| ≤ B := by
  filter_upwards [ae_realCoordinate_pair_domain N] with p hp
  by_cases hxi : Function.Injective p.1
  · by_cases hsi : Function.Injective p.2
    · exact hbound p.1 p.2 (fun i => (hp.1 i).1) hp.2 (fun i => (hp.1 i).2) hxi hsi
    · rw [sheetRealIntegrand_eq_zero_of_not_injective_s N p.1 p.2 hsi, abs_zero]
      exact hB
  · rw [sheetRealIntegrand_eq_zero_of_not_injective_x N p.1 p.2 hxi, abs_zero]
    exact hB

theorem determinant_eq_sheetRealPairIntegral {N : ℕ} (hN : 0 < N) :
    determinant N = 1 / (((n N).factorial : ℝ) ^ 2) *
      ∫ p, sheetRealIntegrand N p.1 p.2 ∂realCoordinateListPairMeasure N := by
  rw [determinant_eq_sheetRealIntegral hN]
  congr 1
  exact (integral_prod _ (integrable_sheetRealIntegrand hN)).symm

theorem abs_determinant_le_of_sheetRealIntegrand_bound {N : ℕ} (hN : 0 < N)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ (x s : Fin (n N) → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      |sheetRealIntegrand N x s| ≤ B) :
    |determinant N| ≤
      ((2 : ℝ) ^ n N / (((n N).factorial : ℝ) ^ 2)) * B := by
  let : IsFiniteMeasure (realCoordinateListPairMeasure N) := by
    unfold realCoordinateListPairMeasure
    infer_instance
  have hae := ae_abs_sheetRealIntegrand_le_of_regular_bound N hB hbound
  have hnorm : ∀ᵐ p ∂realCoordinateListPairMeasure N,
      ‖sheetRealIntegrand N p.1 p.2‖ ≤ B := by
    simpa only [Real.norm_eq_abs] using hae
  have hint : |∫ p, sheetRealIntegrand N p.1 p.2 ∂realCoordinateListPairMeasure N| ≤
      B * (2 : ℝ) ^ n N := by
    simpa only [Real.norm_eq_abs, realCoordinateListPairMeasure_real_univ] using
      norm_integral_le_of_norm_le_const hnorm
  have hfactor : 0 ≤ 1 / (((n N).factorial : ℝ) ^ 2) := by positivity
  rw [determinant_eq_sheetRealPairIntegral hN, abs_mul, abs_of_nonneg hfactor]
  calc
    _ ≤ (1 / (((n N).factorial : ℝ) ^ 2)) * (B * (2 : ℝ) ^ n N) :=
      mul_le_mul_of_nonneg_left hint hfactor
    _ = _ := by ring

theorem abs_determinant_le_of_majorantOne_bound {N : ℕ} (hN : 0 < N)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ (x s : Fin (n N) → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ j, s j ∈ Ioo (0 : ℝ) 1) →
      (∀ i, x i ≠ 0) → Function.Injective x → Function.Injective s →
      realEnergyMajorantOne N x s ≤ M) :
    |determinant N| ≤ ((2 : ℝ) ^ n N / (((n N).factorial : ℝ) ^ 2)) *
      ((3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2) * M) := by
  have hp : 0 ≤ (3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2) :=
    mul_nonneg (pow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (Nat.cast_nonneg (n N)) _)
  apply abs_determinant_le_of_sheetRealIntegrand_bound hN (mul_nonneg hp hM)
  intro x s hx hs hx0 hxi hsi
  exact (abs_sheetRealIntegrand_le_majorantOne hN x s hx hx0 hs).trans
    (mul_le_mul_of_nonneg_left (hbound x s hx hs hx0 hxi hsi) hp)

end InternalCatalan

end

end OAI
