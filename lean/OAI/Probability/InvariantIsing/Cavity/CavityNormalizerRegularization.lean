import OAI.Probability.InvariantIsing.Cavity.CavityBoundedReweighting

namespace OAI

/-! Removing a denominator regularizer for bounded replica tests. Small
normalizers are isolated as a measurable exceptional event. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavityWeightNumerator_abs_le_normalizer {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ) (hw : Measurable w)
    {r : ℕ} (F : (Fin r → X) → ℝ) (hF : Measurable F) {M B : ℝ}
    (_hM : 0 ≤ M) (_hB : 0 ≤ B) (hwb : ∀ x, w x ∈ Icc 0 M)
    (hFb : ∀ σ, |F σ| ≤ B) :
    |cavityWeightNumerator ν w F| ≤ B * cavityWeightNormalizer ν w ^ r := by
  let W := fun σ : Fin r → X => ∏ i, w (σ i)
  have hWM : Measurable W := Finset.measurable_prod _ fun i _ => hw.comp (measurable_pi_apply i)
  have hW0 σ : 0 ≤ W σ := Finset.prod_nonneg fun i _ => (hwb (σ i)).1
  have hWb σ : |W σ| ≤ M ^ r := by
    rw [abs_of_nonneg (hW0 σ)]
    exact (Finset.prod_le_prod₀ (fun i _ => (hwb (σ i)).1)
      (fun i _ => (hwb (σ i)).2)).trans_eq (by simp)
  have hWI : Integrable W (Measure.pi (fun _ : Fin r => ν)) :=
    integrable_of_measurable_abs_le hWM hWb
  have hWFI : Integrable (fun σ => W σ * F σ) (Measure.pi (fun _ : Fin r => ν)) :=
    hWI.mul_bdd hF.aestronglyMeasurable (ae_of_all _ fun σ => by
      simpa only [Real.norm_eq_abs] using hFb σ)
  change |∫ σ, W σ * F σ ∂Measure.pi (fun _ : Fin r => ν)| ≤ _
  calc
    _ ≤ ∫ σ, |W σ * F σ| ∂Measure.pi (fun _ : Fin r => ν) := abs_integral_le_integral_abs
    _ ≤ ∫ σ, B * W σ ∂Measure.pi (fun _ : Fin r => ν) := by
      apply integral_mono hWFI.abs (hWI.const_mul B)
      intro σ
      change |W σ * F σ| ≤ B * W σ
      rw [abs_mul, abs_of_nonneg (hW0 σ)]
      exact (mul_le_mul_of_nonneg_left (hFb σ) (hW0 σ)).trans_eq (mul_comm _ _)
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      simpa only [W, cavityWeightNormalizer, Fintype.card_fin] using
        integral_fintype_prod_eq_pow (ι := Fin r) (μ := ν) w

lemma cavity_one_sub_pow_le {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (r : ℕ) :
    1 - t ^ r ≤ r * (1 - t) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hp : t ^ r ≤ 1 := pow_le_one₀ ht ht1
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma cavity_normalized_numerator_bound {A Z B : ℝ} (hZ : 0 ≤ Z) (hB : 0 ≤ B)
    (r : ℕ) (hA : |A| ≤ B * Z ^ r) : |A / Z ^ r| ≤ B := by
  rw [abs_div, abs_of_nonneg (pow_nonneg hZ r)]
  exact div_le_of_le_mul₀ (pow_nonneg hZ r) hB hA

lemma cavity_regularized_numerator_bound {A Z B δ : ℝ} (hZ : 0 ≤ Z) (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (r : ℕ) (hA : |A| ≤ B * Z ^ r) : |A / (Z + δ) ^ r| ≤ B := by
  apply cavity_normalized_numerator_bound (add_nonneg hZ hδ) hB r
  exact hA.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hZ (by linarith) r) hB)

lemma cavity_normalizer_regularization_error {A Z B δ a : ℝ}
    (ha : 0 < a) (haZ : a ≤ Z) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (r : ℕ) (hA : |A| ≤ B * Z ^ r) :
    |A / Z ^ r - A / (Z + δ) ^ r| ≤ B * r * δ / a := by
  have hZ : 0 < Z := ha.trans_le haZ
  have hZd : 0 < Z + δ := by linarith
  let t := Z / (Z + δ)
  have ht : 0 ≤ t := div_nonneg hZ.le hZd.le
  have ht1 : t ≤ 1 := (div_le_one hZd).mpr (by linarith)
  have htp : 0 ≤ 1 - t ^ r := sub_nonneg.mpr (pow_le_one₀ ht ht1)
  have he : A / Z ^ r - A / (Z + δ) ^ r = A / Z ^ r * (1 - t ^ r) := by
    dsimp [t]
    rw [div_pow]
    field_simp [ne_of_gt hZ, ne_of_gt hZd]
  have hsub : 1 - t = δ / (Z + δ) := by
    dsimp [t]
    field_simp [ne_of_gt hZd]
    ring
  calc
    _ = |A / Z ^ r| * (1 - t ^ r) := by rw [he, abs_mul, abs_of_nonneg htp]
    _ ≤ B * (r * (1 - t)) :=
      mul_le_mul (cavity_normalized_numerator_bound hZ.le hB r hA)
        (cavity_one_sub_pow_le ht ht1 r) htp hB
    _ = B * r * (δ / (Z + δ)) := by rw [hsub]; ring
    _ ≤ B * r * (δ / a) := mul_le_mul_of_nonneg_left
      (div_le_div₀ hδ le_rfl ha (by linarith)) (mul_nonneg hB (Nat.cast_nonneg r))
    _ = _ := by ring

theorem cavity_normalizer_regularization_mean_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A Z : Ω → ℝ) (hA : Measurable A) (hZ : Measurable Z)
    {B δ a : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ) (ha : 0 < a) (r : ℕ)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hAZ : ∀ ω, |A ω| ≤ B * Z ω ^ r) :
    |∫ ω, (A ω / Z ω ^ r - A ω / (Z ω + δ) ^ r) ∂P| ≤
      B * r * δ / a + 2 * B * P.real {ω | Z ω < a} := by
  let D := fun ω => A ω / Z ω ^ r - A ω / (Z ω + δ) ^ r
  let c := B * r * δ / a
  let E := {ω | Z ω < a}
  have hE : MeasurableSet E := measurableSet_lt hZ measurable_const
  have hD : Measurable D := (hA.div (hZ.pow_const r)).sub
    (hA.div ((hZ.add_const δ).pow_const r))
  have hb ω : |D ω| ≤ 2 * B := by
    exact (abs_sub _ _).trans (by
      have h1 := cavity_normalized_numerator_bound (hZ0 ω) hB r (hAZ ω)
      have h2 := cavity_regularized_numerator_bound (hZ0 ω) hB hδ r (hAZ ω)
      linarith)
  have hi : Integrable D P := integrable_of_measurable_abs_le hD hb
  have hc : 0 ≤ c := by positivity
  have hind : Integrable (E.indicator (fun _ => 2 * B)) P := (integrable_const _).indicator hE
  calc
    _ ≤ ∫ ω, |D ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (c + E.indicator (fun _ => 2 * B) ω) ∂P := by
      apply integral_mono hi.abs ((integrable_const c).add hind)
      intro ω
      change |D ω| ≤ c + E.indicator (fun _ => 2 * B) ω
      by_cases hω : ω ∈ E
      · rw [indicator_of_mem hω]
        linarith [hb ω]
      · rw [indicator_of_notMem hω, add_zero]
        exact cavity_normalizer_regularization_error ha (le_of_not_gt hω) hB hδ r (hAZ ω)
    _ = _ := by
      rw [integral_add (integrable_const c) hind, integral_const, integral_indicator_const _ hE]
      simp only [probReal_univ, smul_eq_mul]
      dsimp [c, E]
      ring

end InvariantIsing

end

end OAI
