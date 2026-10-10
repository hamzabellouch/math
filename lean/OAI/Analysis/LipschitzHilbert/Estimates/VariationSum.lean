import OAI.Analysis.LipschitzHilbert.Estimates.VariationPerturbation
import OAI.Analysis.LipschitzHilbert.Estimates.FiniteEnergySchur
import OAI.Analysis.LipschitzHilbert.Estimates.VariationMeasurable

namespace OAI

/-! Summing localized packet variations with summable box weights. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

def cubicVariation {E : Type*} [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) : ℝ :=
  (finiteCubicVariation F N) ^ (1 / 3 : ℝ)

theorem cubicVariation_nonneg {E : Type*} [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) :
    0 ≤ cubicVariation F N := Real.rpow_nonneg (finiteCubicVariation_nonneg F N) _

theorem cubicVariation_sq {E : Type*} [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) :
    cubicVariation F N ^ 2 = (finiteCubicVariation F N) ^ (2 / 3 : ℝ) := by
  unfold cubicVariation
  rw [← Real.rpow_natCast, ← Real.rpow_mul (finiteCubicVariation_nonneg F N)]
  norm_num

theorem cubicVariation_finset_sum {ι E : Type*} [NormedAddCommGroup E]
    (F : ι → ℕ → E) (s : Finset ι) (N : ℕ) :
    cubicVariation (fun n => ∑ i ∈ s, F i n) N ≤ ∑ i ∈ s, cubicVariation (F i) N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cubicVariation, finiteCubicVariation]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (finiteCubicVariation_add_rpow (F i) (fun n => ∑ j ∈ s, F j n) N).trans
      (add_le_add le_rfl ih)

theorem weighted_cubicVariation_sum {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (F : ι → ℕ → E) (N : ℕ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    (finiteCubicVariation (fun n => ∑ i, F i n) N) ^ (2 / 3 : ℝ) ≤
      (∑ i, w i) * ∑ i, (finiteCubicVariation (F i) N) ^ (2 / 3 : ℝ) / w i := by
  have hs := pow_le_pow_left₀ (cubicVariation_nonneg _ _)
    (cubicVariation_finset_sum F Finset.univ N) 2
  have hcs := weighted_sum_norm_square (fun i => cubicVariation (F i) N) w hw
  simp only [Real.norm_eq_abs, abs_of_nonneg (cubicVariation_nonneg _ _), cubicVariation_sq] at hcs hs
  rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => cubicVariation_nonneg (F i) N))] at hcs
  exact hs.trans hcs

theorem lintegral_weighted_cubicVariation_sum {Ω ι E : Type*} [MeasurableSpace Ω]
    [Fintype ι] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure Ω) (F : ι → ℕ → Ω → E)
    (hF : ∀ i n, Measurable (F i n)) (N : ℕ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => ∑ i, F i n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤
      ENNReal.ofReal (∑ i, w i) * ∑ i, ENNReal.ofReal ((w i)⁻¹) *
        ∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => F i n x) N) ^ (2 / 3 : ℝ) ∂μ := by
  have hsum : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  have hterm (i : ι) (x : Ω) :
      ENNReal.ofReal ((finiteCubicVariation (fun n => F i n x) N) ^ (2 / 3 : ℝ) / w i) =
        ENNReal.ofReal ((w i)⁻¹) *
          ENNReal.ofReal (finiteCubicVariation (fun n => F i n x) N) ^ (2 / 3 : ℝ) := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul
      (Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _),
      ← ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num)]
    exact mul_comm _ _
  have hm (i : ι) : Measurable (fun x => ENNReal.ofReal ((w i)⁻¹) *
      ENNReal.ofReal (finiteCubicVariation (fun n => F i n x) N) ^ (2 / 3 : ℝ)) :=
    ((measurable_finiteCubicVariation _ (hF i) N).ennreal_ofReal.pow_const _).const_mul _
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (∑ i, w i) * ∑ i, ENNReal.ofReal ((w i)⁻¹) *
        ENNReal.ofReal (finiteCubicVariation (fun n => F i n x) N) ^ (2 / 3 : ℝ) ∂μ := by
      apply lintegral_mono
      intro x
      have hpoint := ENNReal.ofReal_le_ofReal
        (weighted_cubicVariation_sum (fun i n => F i n x) N w hw)
      rw [ENNReal.ofReal_mul hsum, ENNReal.ofReal_sum_of_nonneg
        (fun i _ => div_nonneg (Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _) (hw i).le)] at hpoint
      simp_rw [hterm] at hpoint
      rw [← ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num)] at hpoint
      exact hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum _ (fun i _ => hm i)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact lintegral_const_mul _ ((measurable_finiteCubicVariation _ (hF i) N).ennreal_ofReal.pow_const _)

theorem lintegral_cubicVariation_sum_of_weighted_energy {Ω ι E : Type*} [MeasurableSpace Ω]
    [Fintype ι] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure Ω) (F : ι → ℕ → Ω → E)
    (hF : ∀ i n, Measurable (F i n)) (N : ℕ) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (A : ℝ≥0∞) {W : ℝ} (hweights : ∑ i, w i ≤ W)
    (henergy : ∀ i, (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
      (fun n => F i n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤ A * ENNReal.ofReal (w i ^ 2)) :
    (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => ∑ i, F i n x) N) ^
      (2 / 3 : ℝ) ∂μ) ≤ ENNReal.ofReal (W ^ 2) * A := by
  have hsum : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  have hinv (i : ι) : ENNReal.ofReal ((w i)⁻¹) * ENNReal.ofReal (w i ^ 2) =
      ENNReal.ofReal (w i) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (hw i).le)]
    congr 1
    field_simp
  calc
    _ ≤ ENNReal.ofReal (∑ i, w i) * ∑ i, ENNReal.ofReal ((w i)⁻¹) *
        ∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => F i n x) N) ^ (2 / 3 : ℝ) ∂μ :=
      lintegral_weighted_cubicVariation_sum μ F hF N w hw
    _ ≤ ENNReal.ofReal (∑ i, w i) * ∑ i, ENNReal.ofReal ((w i)⁻¹) *
        (A * ENNReal.ofReal (w i ^ 2)) := by
      gcongr with i
      exact henergy i
    _ = ENNReal.ofReal (∑ i, w i) * (A * ENNReal.ofReal (∑ i, w i)) := by
      congr 1
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => (hw i).le), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_left_comm, hinv]
    _ = ENNReal.ofReal ((∑ i, w i) ^ 2) * A := by
      rw [pow_two, ENNReal.ofReal_mul hsum]
      ac_rfl
    _ ≤ _ := by
      gcongr

end LipschitzHilbert

end

end OAI
