import Mathlib

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace PlanarEndpoint

lemma weak_lintegral_split {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : AEMeasurable f μ) (hn : 0 ≤ᵐ[μ] f)
    {p A T : ℝ} (hp : 1 < p) (hA : 0 ≤ A) (hT : 0 < T)
    (hw : ∀ t : ℝ, 0 < t → μ {x | t < f x} ≤ ENNReal.ofReal (A ^ p * t ^ (-p))) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
      ENNReal.ofReal ((μ univ).toReal * T + A ^ p * (T ^ (1-p) / (p-1))) := by
  rw [lintegral_eq_lintegral_meas_lt μ hn hf]
  have hs : Ioi (0 : ℝ) = Ioc 0 T ∪ Ioi T := by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro ht
      by_cases h : t ≤ T
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (⟨ht, _⟩ | ht)
      · exact ht
      · exact hT.trans ht
  rw [hs, lintegral_union measurableSet_Ioi (Set.disjoint_left.mpr
    (by intro x hx hy; exact (not_lt_of_ge hx.2) hy))]
  have hlo : (∫⁻ t in Ioc (0 : ℝ) T, μ {x | t < f x}) ≤
      ENNReal.ofReal ((μ univ).toReal * T) := by
    calc
      _ ≤ ∫⁻ _ in Ioc (0 : ℝ) T, μ univ := lintegral_mono (fun _ => measure_mono (subset_univ _))
      _ = ENNReal.ofReal ((μ univ).toReal * T) := by
        simp [Real.volume_Ioc, hT.le, ENNReal.ofReal_mul, mul_comm]
  have hi : IntegrableOn (fun t : ℝ => A ^ p * t ^ (-p)) (Ioi T) volume :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -p < -1) hT).const_mul _
  have htail : (∫⁻ t in Ioi T, μ {x | t < f x}) ≤
      ENNReal.ofReal (A ^ p * (T ^ (1-p) / (p-1))) := by
    calc
      _ ≤ ∫⁻ t in Ioi T, ENNReal.ofReal (A ^ p * t ^ (-p)) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact hw t (hT.trans ht)
      _ = ENNReal.ofReal (∫ t in Ioi T, A ^ p * t ^ (-p)) :=
        (ofReal_integral_eq_lintegral_ofReal hi (by
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          exact mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg (hT.trans ht).le _))).symm
      _ = ENNReal.ofReal (A ^ p * (T ^ (1-p) / (p-1))) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -p < -1) hT]
        congr 2
        rw [show -p + 1 = 1-p by ring]
        have h1 : 1-p ≠ 0 := by linarith
        have h2 : p-1 ≠ 0 := by linarith
        field_simp [h1, h2]
        ring
  exact (add_le_add hlo htail).trans_eq (by
    rw [← ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg hT.le)
      (mul_nonneg (Real.rpow_nonneg hA _)
        (div_nonneg (Real.rpow_nonneg hT.le _) (by linarith)))])

lemma weak_split_threshold {p A m : ℝ} (hp : 1 < p) (hA : 0 < A)
    (hm : 0 < m) :
    m * (A * m ^ (-p⁻¹)) + A ^ p * ((A * m ^ (-p⁻¹)) ^ (1-p) / (p-1)) =
      p / (p-1) * A * m ^ (1-1/p) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hp1 : p-1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hp)
  have he : (-p⁻¹) * (1-p) = 1 - 1/p := by field_simp; ring
  have hpow : A ^ p * (A * m ^ (-p⁻¹)) ^ (1-p) = A * m ^ (1-1/p) := by
    rw [Real.mul_rpow hA.le (Real.rpow_nonneg hm.le _), ← Real.rpow_mul hm.le,
      he, ← mul_assoc, ← Real.rpow_add hA, show p+(1-p) = 1 by ring, Real.rpow_one]
  have hlin : m * (A * m ^ (-p⁻¹)) = A * m ^ (1-1/p) := by
    calc
      _ = A * (m ^ (1 : ℝ) * m ^ (-p⁻¹)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hm]; congr 2; simp [sub_eq_add_neg]
  rw [hlin, ← mul_div_assoc, hpow]
  field_simp
  ring

lemma weak_lintegral_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : AEMeasurable f μ) (hn : 0 ≤ᵐ[μ] f)
    {p A : ℝ} (hp : 1 < p) (hA : 0 ≤ A)
    (hw : ∀ t : ℝ, 0 < t → μ {x | t < f x} ≤ ENNReal.ofReal ((A / t) ^ p)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
      ENNReal.ofReal (p/(p-1) * A * (μ univ).toReal ^ (1-1/p)) := by
  by_cases hm : μ univ = 0
  · have hμ : μ = 0 := Measure.measure_univ_eq_zero.mp hm
    simp [hμ]
  have hmpos : 0 < (μ univ).toReal := ENNReal.toReal_pos hm (measure_ne_top _ _)
  by_cases hAz : A = 0
  · subst A
    rw [lintegral_eq_lintegral_meas_lt μ hn hf]
    have hh : (fun t : ℝ => μ {x | t < f x}) =ᵐ[volume.restrict (Ioi 0)] 0 := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have h := hw t ht
      simpa [Real.zero_rpow (ne_of_gt (lt_trans zero_lt_one hp))] using h
    simp [lintegral_congr_ae hh]
  have hApos := lt_of_le_of_ne hA (Ne.symm hAz)
  have hwp (t : ℝ) (ht : 0 < t) :
      μ {x | t < f x} ≤ ENNReal.ofReal (A ^ p * t ^ (-p)) := by
    convert hw t ht using 2
    rw [Real.div_rpow hA ht.le, Real.rpow_neg ht.le, div_eq_mul_inv]
  have hbound := weak_lintegral_split μ hf hn hp hA
    (T := A * (μ univ).toReal ^ (-p⁻¹))
    (mul_pos hApos (Real.rpow_pos_of_pos hmpos _)) hwp
  simpa only [weak_split_threshold hp hApos hmpos] using hbound

lemma weak_integral_norm_bound {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → E} (hf : AEStronglyMeasurable f μ)
    {p A : ℝ} (hp : 1 < p) (hA : 0 ≤ A)
    (hw : ∀ t : ℝ, 0 < t → μ {x | t < ‖f x‖} ≤ ENNReal.ofReal ((A / t) ^ p)) :
    Integrable f μ ∧ ∫ x, ‖f x‖ ∂μ ≤ p/(p-1) * A * (μ univ).toReal ^ (1-1/p) := by
  have hl := weak_lintegral_bound μ hf.norm.aemeasurable
    (Filter.Eventually.of_forall (fun x => norm_nonneg (f x))) hp hA hw
  have hi : Integrable f μ := ⟨hf, (hasFiniteIntegral_iff_norm f).2
    (hl.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi.norm
    (Filter.Eventually.of_forall (fun x => norm_nonneg (f x)))] at hl
  apply (ENNReal.ofReal_le_ofReal_iff _).1 hl
  exact mul_nonneg (mul_nonneg (div_nonneg (by linarith) (by linarith)) hA)
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)

end PlanarEndpoint
end

end OAI
