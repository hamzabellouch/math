import OAI.Probability.InvariantIsing.Cavity.CavityNormalizerRegularization

namespace OAI

/-! Continuous cutoffs for finite-replica passage. Their removal costs
only the discarded mass, including the zero-normalizer convention. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Topology

namespace InvariantIsing

lemma cavity_normalized_cutoff_algebra {A F Z B : ℝ} (r : ℕ)
    (hZ : Z ∈ Icc (0 : ℝ) 1) (hB : 0 ≤ B)
    (hA : |A| ≤ B * Z ^ r) (hAF : |A - F| ≤ B * (1 - Z ^ r)) :
    |A / Z ^ r - F| ≤ 2 * B * r * (1 - Z) := by
  have hp : Z ^ r ≤ 1 := pow_le_one₀ hZ.1 hZ.2
  have hnp : 0 ≤ 1 - Z ^ r := sub_nonneg.mpr hp
  have hb := cavity_normalized_numerator_bound hZ.1 hB r hA
  have he : A / Z ^ r - A = A / Z ^ r * (1 - Z ^ r) := by
    by_cases hz : Z ^ r = 0
    · have ha : A = 0 := abs_nonpos_iff.mp (by simpa only [hz, mul_zero] using hA)
      simp only [ha, zero_div, sub_self, zero_mul]
    · field_simp
  calc
    _ ≤ |A / Z ^ r - A| + |A - F| := abs_sub_le _ _ _
    _ = |A / Z ^ r| * (1 - Z ^ r) + |A - F| := by
      rw [he, abs_mul, abs_of_nonneg hnp]
    _ ≤ B * (1 - Z ^ r) + B * (1 - Z ^ r) :=
      add_le_add (mul_le_mul_of_nonneg_right hb hnp) hAF
    _ = 2 * B * (1 - Z ^ r) := by ring
    _ ≤ 2 * B * (r * (1 - Z)) := mul_le_mul_of_nonneg_left
      (cavity_one_sub_pow_le hZ.1 hZ.2 r) (by positivity)
    _ = _ := by ring

theorem cavity_soft_cutoff_replica_error {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (w : X → ℝ) (hw : Measurable w)
    (hwb : ∀ x, w x ∈ Icc (0 : ℝ) 1) {r : ℕ}
    (F : (Fin r → X) → ℝ) (hF : Measurable F) {B : ℝ}
    (hB : 0 ≤ B) (hFb : ∀ σ, |F σ| ≤ B) :
    |cavityWeightedReplicaMean ν w F - ∫ σ, F σ ∂Measure.pi (fun _ : Fin r => ν)| ≤
      2 * B * r * (1 - cavityWeightNormalizer ν w) := by
  let P := Measure.pi (fun _ : Fin r => ν)
  let V := fun σ : Fin r → X => ∏ i, w (σ i)
  have hVm : Measurable V := Finset.measurable_prod _ (fun i _ => hw.comp (measurable_pi_apply i))
  have hV0 σ : 0 ≤ V σ := Finset.prod_nonneg (fun i _ => (hwb (σ i)).1)
  have hV1 σ : V σ ≤ 1 := by
    exact (Finset.prod_le_prod₀ (fun i _ => (hwb (σ i)).1)
      (fun i _ => (hwb (σ i)).2)).trans_eq (by simp)
  have hiV : Integrable V P := integrable_of_measurable_abs_le hVm
    (fun σ => by rw [abs_of_nonneg (hV0 σ)]; exact hV1 σ)
  have hiF : Integrable F P := integrable_of_measurable_abs_le hF hFb
  have hiVF : Integrable (fun σ => V σ * F σ) P := hiV.mul_bdd hF.aestronglyMeasurable
    (ae_of_all _ (fun σ => by simpa only [Real.norm_eq_abs] using hFb σ))
  have hvi : (∫ σ, V σ ∂P) = cavityWeightNormalizer ν w ^ r := by
    simpa only [P, V, cavityWeightNormalizer, Fintype.card_fin] using
      integral_fintype_prod_eq_pow (ι := Fin r) (μ := ν) w
  apply cavity_normalized_cutoff_algebra r
    (cavityWeightNormalizer_mem ν w hw (by norm_num) hwb) hB
    (cavityWeightNumerator_abs_le_normalizer ν w hw F hF (by norm_num) hB hwb hFb)
  change |(∫ σ, V σ * F σ ∂P) - ∫ σ, F σ ∂P| ≤ _
  rw [← integral_sub hiVF hiF]
  calc
    _ ≤ ∫ σ, |V σ * F σ - F σ| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ σ, B * (1 - V σ) ∂P := by
      apply integral_mono (hiVF.sub hiF).abs (((integrable_const 1).sub hiV).const_mul B)
      intro σ
      change |V σ * F σ - F σ| ≤ B * (1 - V σ)
      rw [← sub_one_mul, abs_mul, abs_of_nonpos (sub_nonpos.mpr (hV1 σ)), neg_sub]
      exact (mul_le_mul_of_nonneg_left (hFb σ) (sub_nonneg.mpr (hV1 σ))).trans_eq (mul_comm _ _)
    _ = B * (1 - cavityWeightNormalizer ν w ^ r) := by
      rw [integral_const_mul, integral_sub (integrable_const 1) hiV, integral_const, hvi]
      simp only [probReal_univ, one_smul]

def cavityRadialCutoff (B x : ℝ) : ℝ := max 0 (min 1 (B + 1 - x))

lemma continuous_cavityRadialCutoff (B : ℝ) : Continuous (cavityRadialCutoff B) := by
  unfold cavityRadialCutoff
  fun_prop

lemma cavityRadialCutoff_mem (B x : ℝ) : cavityRadialCutoff B x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma cavityRadialCutoff_eq_one {B x : ℝ} (hx : x ≤ B) : cavityRadialCutoff B x = 1 := by
  unfold cavityRadialCutoff
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

lemma cavityRadialCutoff_eq_zero {B x : ℝ} (hx : B + 1 ≤ x) : cavityRadialCutoff B x = 0 := by
  unfold cavityRadialCutoff
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

lemma cavity_radial_cutoff_discarded_mass {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (R : X → ℝ) (hR : Measurable R) (B : ℝ) :
    1 - cavityWeightNormalizer ν (fun x => cavityRadialCutoff B (R x)) ≤
      ν.real {x | B < R x} := by
  let s := {x | B < R x}
  have hs : MeasurableSet s := measurableSet_lt measurable_const hR
  have hw := (continuous_cavityRadialCutoff B).measurable.comp hR
  have hi : Integrable (fun x => cavityRadialCutoff B (R x)) ν :=
    integrable_of_measurable_abs_le hw (fun x => by
      rw [abs_of_nonneg (cavityRadialCutoff_mem B (R x)).1]
      exact (cavityRadialCutoff_mem B (R x)).2)
  have hb := integral_mono ((integrable_const 1).sub hi) ((integrable_const 1).indicator hs)
    (fun x => by
      change 1 - cavityRadialCutoff B (R x) ≤ s.indicator (fun _ => (1 : ℝ)) x
      by_cases hx : x ∈ s
      · rw [indicator_of_mem hx]
        linarith [(cavityRadialCutoff_mem B (R x)).1]
      · rw [indicator_of_notMem hx, cavityRadialCutoff_eq_one (le_of_not_gt hx), sub_self])
  simpa only [Pi.sub_apply, integral_sub (integrable_const 1) hi, integral_const, probReal_univ,
    one_smul, integral_indicator_const _ hs, smul_eq_mul, mul_one, cavityWeightNormalizer] using hb

end InvariantIsing

end

end OAI
