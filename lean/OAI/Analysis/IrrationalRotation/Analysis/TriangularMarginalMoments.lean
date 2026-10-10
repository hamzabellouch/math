import OAI.Analysis.IrrationalRotation.Analysis.TriangularLawProperties
import OAI.Analysis.IrrationalRotation.Couplings.ProductDensity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.ProductModel

private theorem rep_measurable : Measurable circleRepresentative :=
  Sampling.representative_measurable

private theorem rep_bounds (x : Circle) :
    0 ≤ circleRepresentative x ∧ circleRepresentative x ≤ 1 :=
  ⟨(Sampling.representative_mem_Ico x).1,
    (Sampling.representative_mem_Ico x).2.le⟩

theorem integral_circleRepresentative_pow (n : ℕ) :
    (∫ x, circleRepresentative x ^ n ∂circleMeasure) = 1 / (n + 1 : ℝ) := by
  have hmap : circleMeasure.map circleRepresentative =
      volume.restrict (Ico (0 : ℝ) 1) := Sampling.representative_map_haar
  calc
    (∫ x, circleRepresentative x ^ n ∂circleMeasure) =
        ∫ t in Ico (0 : ℝ) 1, t ^ n := by
      rw [← hmap, integral_map rep_measurable.aemeasurable]
      exact (measurable_id.pow_const n).aestronglyMeasurable
    _ = ∫ t in (0 : ℝ)..1, t ^ n := by
      rw [integral_Ico_eq_integral_Ioc,
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ = 1 / (n + 1 : ℝ) := by
      rw [integral_pow]
      simp

theorem integral_one_sub_circleRepresentative_pow (n : ℕ) :
    (∫ x, (1 - circleRepresentative x) ^ n ∂circleMeasure) =
      1 / (n + 1 : ℝ) := by
  have hmap : circleMeasure.map circleRepresentative =
      volume.restrict (Ico (0 : ℝ) 1) := Sampling.representative_map_haar
  calc
    (∫ x, (1 - circleRepresentative x) ^ n ∂circleMeasure) =
        ∫ t in Ico (0 : ℝ) 1, (1 - t) ^ n := by
      rw [← hmap, integral_map rep_measurable.aemeasurable]
      exact ((measurable_const.sub measurable_id).pow_const n).aestronglyMeasurable
    _ = ∫ t in (0 : ℝ)..1, (1 - t) ^ n := by
      rw [integral_Ico_eq_integral_Ioc,
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ = ∫ t in (0 : ℝ)..1, t ^ n := by
      simpa using (intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ n)
        (a := 0) (b := 1) 1)
    _ = 1 / (n + 1 : ℝ) := by
      rw [integral_pow]
      simp

private theorem representative_pow_integrable (n : ℕ) :
    Integrable (fun x => circleRepresentative x ^ n) circleMeasure := by
  apply (MemLp.of_bound (rep_measurable.pow_const n).aestronglyMeasurable 1 ?_
    : MemLp (fun x => circleRepresentative x ^ n) 1 circleMeasure).integrable (by norm_num)
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (rep_bounds x).1 n)]
    exact pow_le_one₀ (rep_bounds x).1 (rep_bounds x).2

private theorem one_sub_representative_pow_integrable (n : ℕ) :
    Integrable (fun x => (1 - circleRepresentative x) ^ n) circleMeasure := by
  apply (MemLp.of_bound ((measurable_const.sub rep_measurable).pow_const n).aestronglyMeasurable
    1 ?_ : MemLp (fun x => (1 - circleRepresentative x) ^ n) 1 circleMeasure).integrable
    (by norm_num)
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr (rep_bounds x).2) n)]
    exact pow_le_one₀ (sub_nonneg.mpr (rep_bounds x).2) (by linarith [(rep_bounds x).1])

theorem integral_triangularFirstDensity_pow (I : Finset ℕ) (n : ℕ) :
    (∫ x, triangularFirstDensity I x ^ n ∂baseMeasure) =
      (1 / (n + 1 : ℝ)) ^ I.card := by
  simp only [triangularFirstDensity, ← Finset.prod_pow]
  rw [baseMeasure, ProductDensity.integral_partial_product I
    (fun _ => one_sub_representative_pow_integrable n)]
  simp [integral_one_sub_circleRepresentative_pow]

theorem integral_triangularSecondDensity_pow (I : Finset ℕ) (n : ℕ) :
    (∫ x, triangularSecondDensity I x ^ n ∂baseMeasure) =
      (1 / (n + 1 : ℝ)) ^ I.card := by
  simp only [triangularSecondDensity, ← Finset.prod_pow]
  rw [baseMeasure, ProductDensity.integral_partial_product I
    (fun _ => representative_pow_integrable n)]
  simp [integral_circleRepresentative_pow]

theorem integral_triangularFirstDensity_sq (I : Finset ℕ) :
    (∫ x, triangularFirstDensity I x ^ 2 ∂baseMeasure) = (1 / 3 : ℝ) ^ I.card := by
  convert integral_triangularFirstDensity_pow I 2 using 1
  norm_num

theorem integral_triangularSecondDensity_sq (I : Finset ℕ) :
    (∫ x, triangularSecondDensity I x ^ 2 ∂baseMeasure) = (1 / 3 : ℝ) ^ I.card := by
  convert integral_triangularSecondDensity_pow I 2 using 1
  norm_num

theorem memLp_triangularFirstDensity (I : Finset ℕ) (p : ℝ≥0∞) :
    MemLp (triangularFirstDensity I) p baseMeasure := by
  have hm : Measurable (triangularFirstDensity I) := by
    unfold triangularFirstDensity
    exact Finset.measurable_prod I fun i _ =>
      measurable_const.sub (rep_measurable.comp (measurable_pi_apply i))
  apply MemLp.of_bound hm.aestronglyMeasurable 1
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Sampling.triangular_density_bounds I x).1.1]
    exact (Sampling.triangular_density_bounds I x).1.2

theorem memLp_triangularSecondDensity (I : Finset ℕ) (p : ℝ≥0∞) :
    MemLp (triangularSecondDensity I) p baseMeasure := by
  have hm : Measurable (triangularSecondDensity I) := by
    unfold triangularSecondDensity
    exact Finset.measurable_prod I fun i _ =>
      rep_measurable.comp (measurable_pi_apply i)
  apply MemLp.of_bound hm.aestronglyMeasurable 1
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Sampling.triangular_density_bounds I x).2.1]
    exact (Sampling.triangular_density_bounds I x).2.2

theorem eLpNorm_triangularFirstDensity (I : Finset ℕ) :
    eLpNorm (triangularFirstDensity I) 2 baseMeasure =
      ENNReal.ofReal (Real.sqrt ((1 / 3 : ℝ) ^ I.card)) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    (memLp_triangularFirstDensity I 2)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [integral_triangularFirstDensity_sq, Real.sqrt_eq_rpow]

theorem eLpNorm_triangularSecondDensity (I : Finset ℕ) :
    eLpNorm (triangularSecondDensity I) 2 baseMeasure =
      ENNReal.ofReal (Real.sqrt ((1 / 3 : ℝ) ^ I.card)) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    (memLp_triangularSecondDensity I 2)]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [integral_triangularSecondDensity_sq, Real.sqrt_eq_rpow]

theorem triangularLaw_exact_L2_marginals (I : Finset ℕ) :
    ∃ f g : Lp ℝ 2 baseMeasure,
      ((fun x => f x) =ᵐ[baseMeasure] triangularFirstDensity I) ∧
      ((fun x => g x) =ᵐ[baseMeasure] triangularSecondDensity I) ∧
      (0 ≤ᵐ[baseMeasure] f) ∧ (0 ≤ᵐ[baseMeasure] g) ∧
      (triangularLaw I).map Prod.fst =
        baseMeasure.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      (triangularLaw I).map Prod.snd =
        baseMeasure.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      ‖f‖ = Real.sqrt ((1 / 3 : ℝ) ^ I.card) ∧
      ‖g‖ = Real.sqrt ((1 / 3 : ℝ) ^ I.card) := by
  let hf := memLp_triangularFirstDensity I 2
  let hg := memLp_triangularSecondDensity I 2
  let f := hf.toLp (triangularFirstDensity I)
  let g := hg.toLp (triangularSecondDensity I)
  have hfeq : (fun x => f x) =ᵐ[baseMeasure] triangularFirstDensity I := hf.coeFn_toLp
  have hgeq : (fun x => g x) =ᵐ[baseMeasure] triangularSecondDensity I := hg.coeFn_toLp
  refine ⟨f, g, hfeq, hgeq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hfeq] with x hx
    rw [hx]
    exact (Sampling.triangular_density_bounds I x).1.1
  · filter_upwards [hgeq] with x hx
    rw [hx]
    exact (Sampling.triangular_density_bounds I x).2.1
  · rw [triangularLaw_first_marginal]
    exact withDensity_congr_ae (hfeq.symm.fun_comp ENNReal.ofReal)
  · rw [Sampling.triangularLaw_second_marginal]
    exact withDensity_congr_ae (hgeq.symm.fun_comp ENNReal.ofReal)
  · rw [Lp.norm_toLp, eLpNorm_triangularFirstDensity, ENNReal.toReal_ofReal
      (Real.sqrt_nonneg _)]
  · rw [Lp.norm_toLp, eLpNorm_triangularSecondDensity, ENNReal.toReal_ofReal
      (Real.sqrt_nonneg _)]

theorem triangularLaw_hasUniformL2Marginals (I : ℕ → Finset ℕ) :
    HasUniformL2Marginals (fun l => triangularLaw (I l)) := by
  refine ⟨1, zero_le_one, ?_⟩
  intro l
  obtain ⟨f, g, _hfeq, _hgeq, hf, hg, hmf, hmg, hnf, hng⟩ :=
    triangularLaw_exact_L2_marginals (I l)
  have hnorm : Real.sqrt ((1 / 3 : ℝ) ^ (I l).card) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    exact pow_le_one₀ (by norm_num) (by norm_num)
  exact ⟨f, g, hf, hg, hmf, hmg, hnf.le.trans hnorm, hng.le.trans hnorm⟩

end Invariant233.ProductModel

end

end OAI
