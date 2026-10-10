import OAI.Combinatorics.Progressions.Probability.AllocatedEarlyCoverCoefficientMass

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {H J : Type*} [AddCommGroup H] [MeasurableSpace H] [Fintype J]
variable (μ : Measure H) (f : H →+ (J → UnitAddCircle))

noncomputable def ambientTentKernel (q : ℕ) (a y : H) : ℝ :=
  normalizedAmbientTent μ f q (f (y - a))

theorem ambientTentKernel_symm (q : ℕ) (a y : H) :
    ambientTentKernel μ f q a y = ambientTentKernel μ f q y a := by
  simp only [ambientTentKernel, normalizedAmbientTent, ambientTorusTent, map_sub]
  rw [norm_sub_rev (f y) (f a)]

theorem ambientTentKernel_support {q : ℕ} (hq : 0 < q) (a y : H) (h : ambientTentKernel μ f q a y ≠ 0) :
    ‖f y - f a‖ < 4 / (q : ℝ) := by
  have ht : ambientTorusTent q (f (y - a)) ≠ 0 := by
    intro he
    exact h (by simp only [ambientTentKernel, normalizedAmbientTent, he, zero_div])
  simpa only [map_sub] using ambientTorusTent_support hq (f (y - a)) ht

variable [TopologicalSpace H] [IsTopologicalAddGroup H] [BorelSpace H] [MeasurableAdd₂ H]
variable [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
variable (hf : Continuous f) {q : ℕ} (hq : 0 < q)

include hf hq

theorem ambientTentKernel_range (a y : H) :
    0 ≤ ambientTentKernel μ f q a y ∧ ambientTentKernel μ f q a y ≤ 2 * (q : ℝ) ^ Fintype.card J := by
  have hz := ambientTentMass_pos μ f hf hq
  have hi := ambientTentMass_inv_le μ f hf hq
  exact ⟨div_nonneg (ambientTorusTent_range q _).1 hz.le,
    (div_le_div_of_nonneg_right (ambientTorusTent_range q _).2 hz.le).trans hi⟩

theorem normalizedAmbientTent_shift_lipschitz (a : J → UnitAddCircle) :
    LipschitzWith ((q : ℝ≥0) ^ (Fintype.card J + 1))
      (fun z => normalizedAmbientTent μ f q (z - a)) := by
  have h := normalizedAmbientTent_lipschitz μ f q
    (ambientTentMass_pos μ f hf hq) (ambientTentMass_inv_le μ f hf hq)
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [dist_sub_right] using h.dist_le_mul (z - a) (w - a)

theorem ambientTentKernel_continuous (a : H) : Continuous (ambientTentKernel μ f q a) := by
  have h := normalizedAmbientTent_lipschitz μ f q
    (ambientTentMass_pos μ f hf hq) (ambientTentMass_inv_le μ f hf hq)
  exact h.continuous.comp (hf.comp (continuous_id.sub continuous_const))

theorem ambientTentKernel_integrable (a : H) : Integrable (ambientTentKernel μ f q a) μ :=
  Integrable.of_bound (ambientTentKernel_continuous μ f hf hq a).aestronglyMeasurable
    (2 * (q : ℝ) ^ Fintype.card J) (ae_of_all μ (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ambientTentKernel_range μ f hf hq a y).1]
      exact (ambientTentKernel_range μ f hf hq a y).2))

theorem ambientTentKernel_integral (a : H) : (∫ y, ambientTentKernel μ f q a y ∂μ) = 1 := by
  have htrans : (∫ y, ambientTentKernel μ f q a y ∂μ) =
      ∫ y, normalizedAmbientTent μ f q (f y) ∂μ := by
    simpa only [ambientTentKernel, sub_eq_add_neg, add_comm] using
      integral_add_left_eq_self (μ := μ) (fun y => normalizedAmbientTent μ f q (f y)) (-a)
  rw [htrans]
  change (∫ y, ambientTorusTent q (f y) / ambientTentMass μ f q ∂μ) = 1
  rw [integral_div]
  exact div_self (ambientTentMass_pos μ f hf hq).ne'

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {Ω Y : Type*} [Fintype Ω] [MeasurableSpace Y]
variable (law : FiniteProbabilityWeights Ω) (K : Ω → Y → ℝ)

noncomputable def finiteKernelObservable (C : ℝ) (F : Ω → ℂ) (y : Y) : ℂ :=
  law.complexMean (fun x => (K x y : ℂ) * F x) / (C : ℂ)

theorem finiteKernelObservable_measurable (hK : ∀ x, Measurable (K x)) (C : ℝ) (F : Ω → ℂ) :
    Measurable (finiteKernelObservable law K C F) := by
  unfold finiteKernelObservable FiniteProbabilityWeights.complexMean
  fun_prop

omit [MeasurableSpace Y] in
theorem finiteKernelObservable_norm_le (hK0 : ∀ x y, 0 ≤ K x y)
    {C : ℝ} (hC : 0 < C) (hden : ∀ y, law.mean (fun x => K x y) ≤ C)
    (F : Ω → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) (y : Y) :
    ‖finiteKernelObservable law K C F y‖ ≤ 1 := by
  have hbound : ‖law.complexMean (fun x => (K x y : ℂ) * F x)‖ ≤ C := by
    apply (law.norm_complexMean_le_mean_norm _).trans
    apply (law.mean_mono (fun x => ?_)).trans (hden y)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 x y)]
    exact (mul_le_mul_of_nonneg_left (hF x) (hK0 x y)).trans_eq (mul_one _)
  rw [finiteKernelObservable, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
  exact (div_le_one hC).mpr hbound

theorem finiteKernelObservable_integral (μ : Measure Y) (φ : Y → ℂ) (hφ : Integrable φ μ)
    (hK : ∀ x, Measurable (K x)) (hK0 : ∀ x y, 0 ≤ K x y)
    {M : ℝ} (hKM : ∀ x y, K x y ≤ M) (C : ℝ) (F : Ω → ℂ) :
    (∫ y, φ y * finiteKernelObservable law K C F y ∂μ) =
      law.complexMean (fun x => F x * ∫ y, φ y * (K x y : ℂ) ∂μ) / (C : ℂ) := by
  have hi (x : Ω) : Integrable (fun y => φ y * (K x y : ℂ)) μ :=
    hφ.mul_bdd (hK x).complex_ofReal.aestronglyMeasurable (ae_of_all μ (fun y => by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hK0 x y)] using hKM x y))
  have heq (y : Y) : φ y * finiteKernelObservable law K C F y =
      (∑ x, (law.weight x : ℂ) * (F x * (φ y * (K x y : ℂ)))) / (C : ℂ) := by
    unfold finiteKernelObservable FiniteProbabilityWeights.complexMean
    rw [← mul_div_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [heq]
  rw [integral_div, integral_finsetSum _ (fun x _ => (hi x).const_mul (F x) |>.const_mul (law.weight x : ℂ))]
  simp only [integral_const_mul, FiniteProbabilityWeights.complexMean]

theorem finiteKernelObservable_integrable (μ : Measure Y) (φ : Y → ℂ) (hφ : Integrable φ μ)
    (hK : ∀ x, Measurable (K x)) (hK0 : ∀ x y, 0 ≤ K x y)
    {C : ℝ} (hC : 0 < C) (hden : ∀ y, law.mean (fun x => K x y) ≤ C)
    (F : Ω → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) :
    Integrable (fun y => φ y * finiteKernelObservable law K C F y) μ :=
  hφ.mul_bdd (finiteKernelObservable_measurable law K hK C F).aestronglyMeasurable
    (ae_of_all μ (finiteKernelObservable_norm_le law K hK0 hC hden F hF))

theorem finiteKernelObservable_source_error (μ : Measure Y) (φ : Y → ℂ) (hφ : Integrable φ μ)
    (hK : ∀ x, Measurable (K x)) (hK0 : ∀ x y, 0 ≤ K x y)
    {M C : ℝ} (hKM : ∀ x y, K x y ≤ M) (hC : 0 < C)
    (v F : Ω → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) :
    ‖law.complexMean (fun x => v x * F x) -
      (∫ y, φ y * finiteKernelObservable law K C F y ∂μ) * (C : ℂ)‖ ≤
        law.mean (fun x => ‖v x - ∫ y, φ y * (K x y : ℂ) ∂μ‖) := by
  rw [finiteKernelObservable_integral law K μ φ hφ hK hK0 hKM C F,
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hC.ne')]
  apply law.norm_complexMean_sub_le
  intro x _
  calc
    ‖v x * F x - F x * ∫ y, φ y * (K x y : ℂ) ∂μ‖ =
        ‖(v x - ∫ y, φ y * (K x y : ℂ) ∂μ) * F x‖ := by congr 1; ring
    _ = ‖v x - ∫ y, φ y * (K x y : ℂ) ∂μ‖ * ‖F x‖ := norm_mul _ _
    _ ≤ ‖v x - ∫ y, φ y * (K x y : ℂ) ∂μ‖ :=
      (mul_le_mul_of_nonneg_left (hF x) (norm_nonneg _)).trans_eq (mul_one _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {H J : Type*} [AddCommGroup H] [MeasurableSpace H] [Fintype J]
variable [TopologicalSpace H] [IsTopologicalAddGroup H] [BorelSpace H] [MeasurableAdd₂ H]
variable (μ : Measure H) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
variable (f : H →+ (J → UnitAddCircle)) (hf : Continuous f) {q : ℕ} (hq : 0 < q)

include hf hq

theorem ambientTentKernel_lipschitz_error
    (ψ : (J → UnitAddCircle) → ℂ) {L : ℝ≥0} (hL : LipschitzWith L ψ)
    (hψ : Integrable (fun y => ψ (f y)) μ) (a : H) :
    ‖ψ (f a) - ∫ y, ψ (f y) * (ambientTentKernel μ f q a y : ℂ) ∂μ‖ ≤ (L : ℝ) * (4 / (q : ℝ)) := by
  have hk := ambientTentKernel_integrable μ f hf hq a
  have hkm := (ambientTentKernel_continuous μ f hf hq a).measurable
  have hmul : Integrable (fun y => ψ (f y) * (ambientTentKernel μ f q a y : ℂ)) μ :=
    hψ.mul_bdd hkm.complex_ofReal.aestronglyMeasurable (ae_of_all μ (fun y => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ambientTentKernel_range μ f hf hq a y).1]
      exact (ambientTentKernel_range μ f hf hq a y).2))
  have hconst := hk.ofReal.const_mul (ψ (f a))
  have hid : ψ (f a) - ∫ y, ψ (f y) * (ambientTentKernel μ f q a y : ℂ) ∂μ =
      ∫ y, (ψ (f a) - ψ (f y)) * (ambientTentKernel μ f q a y : ℂ) ∂μ := by
    calc
      _ = (∫ y, ψ (f a) * (ambientTentKernel μ f q a y : ℂ) ∂μ) -
          ∫ y, ψ (f y) * (ambientTentKernel μ f q a y : ℂ) ∂μ := by
        rw [integral_const_mul, integral_complex_ofReal, ambientTentKernel_integral μ f hf hq,
          Complex.ofReal_one, mul_one]
      _ = ∫ y, ψ (f a) * (ambientTentKernel μ f q a y : ℂ) -
          ψ (f y) * (ambientTentKernel μ f q a y : ℂ) ∂μ := (integral_sub hconst hmul).symm
      _ = _ := by congr 1; funext y; ring
  rw [hid]
  have hpoint (y : H) : ‖(ψ (f a) - ψ (f y)) * (ambientTentKernel μ f q a y : ℂ)‖ ≤
      ((L : ℝ) * (4 / (q : ℝ))) * ambientTentKernel μ f q a y := by
    by_cases hz : ambientTentKernel μ f q a y = 0
    · simp only [hz, Complex.ofReal_zero, mul_zero, norm_zero, le_refl]
    · have hs := ambientTentKernel_support μ f hq a y hz
      have hd : ‖ψ (f a) - ψ (f y)‖ ≤ (L : ℝ) * (4 / (q : ℝ)) := by
        calc
          _ = dist (ψ (f a)) (ψ (f y)) := (dist_eq_norm _ _).symm
          _ ≤ (L : ℝ) * dist (f a) (f y) := hL.dist_le_mul _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm, norm_sub_rev] using hs.le) L.coe_nonneg
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ambientTentKernel_range μ f hf hq a y).1]
      exact mul_le_mul_of_nonneg_right hd (ambientTentKernel_range μ f hf hq a y).1
  apply (norm_integral_le_of_norm_le (hk.const_mul ((L : ℝ) * (4 / (q : ℝ)))) (ae_of_all μ hpoint)).trans_eq
  rw [integral_const_mul, ambientTentKernel_integral μ f hf hq, mul_one]

theorem finiteAmbientKernel_transfer {Ω : Type*} [Fintype Ω]
    (law : FiniteProbabilityWeights Ω) (sample : Ω → H)
    {C : ℝ} (hC : 0 < C)
    (hden : ∀ y, law.mean (fun x => ambientTentKernel μ f q (sample x) y) ≤ C)
    (φ : H → ℂ) (hφ : Integrable φ μ)
    (ψ : (J → UnitAddCircle) → ℂ) {L : ℝ≥0} (hL : LipschitzWith L ψ)
    (hψ : Integrable (fun y => ψ (f y)) μ)
    (F : Ω → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1) :
    let obs := finiteKernelObservable law (fun x => ambientTentKernel μ f q (sample x)) C F
    Measurable obs ∧ (∀ y, ‖obs y‖ ≤ 1) ∧ Integrable (fun y => φ y * obs y) μ ∧
      ‖law.complexMean (fun x => φ (sample x) * F x) - (∫ y, φ y * obs y ∂μ) * (C : ℂ)‖ ≤
        law.mean (fun x => ‖φ (sample x) - ψ (f (sample x))‖) + (L : ℝ) * (4 / (q : ℝ)) +
          C * ∫ y, ‖ψ (f y) - φ y‖ ∂μ := by
  intro obs
  let K := fun x => ambientTentKernel μ f q (sample x)
  have hK (x : Ω) : Measurable (K x) := (ambientTentKernel_continuous μ f hf hq (sample x)).measurable
  have hK0 (x : Ω) (y : H) : 0 ≤ K x y := (ambientTentKernel_range μ f hf hq (sample x) y).1
  have hKM (x : Ω) (y : H) : K x y ≤ 2 * (q : ℝ) ^ Fintype.card J :=
    (ambientTentKernel_range μ f hf hq (sample x) y).2
  have hobs : Measurable obs := finiteKernelObservable_measurable law K hK C F
  have hb : ∀ y, ‖obs y‖ ≤ 1 := finiteKernelObservable_norm_le law K hK0 hC hden F hF
  have hiφ : Integrable (fun y => φ y * obs y) μ :=
    finiteKernelObservable_integrable law K μ φ hφ hK hK0 hC hden F hF
  have hiψ : Integrable (fun y => ψ (f y) * obs y) μ :=
    finiteKernelObservable_integrable law K μ (fun y => ψ (f y)) hψ hK hK0 hC hden F hF
  refine ⟨hobs, hb, hiφ, ?_⟩
  have hfirst : ‖law.complexMean (fun x => φ (sample x) * F x) -
      law.complexMean (fun x => ψ (f (sample x)) * F x)‖ ≤
      law.mean (fun x => ‖φ (sample x) - ψ (f (sample x))‖) := by
    apply law.norm_complexMean_sub_le
    intro x _
    rw [← sub_mul, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hF x) (norm_nonneg _)).trans_eq (mul_one _)
  have hsmooth : law.mean (fun x => ‖ψ (f (sample x)) - ∫ y, ψ (f y) * (K x y : ℂ) ∂μ‖) ≤
      (L : ℝ) * (4 / (q : ℝ)) :=
    (law.mean_mono (fun x => ambientTentKernel_lipschitz_error μ f hf hq ψ hL hψ (sample x))).trans_eq
      (law.mean_const _)
  have hmiddle : ‖law.complexMean (fun x => ψ (f (sample x)) * F x) -
      (∫ y, ψ (f y) * obs y ∂μ) * (C : ℂ)‖ ≤ (L : ℝ) * (4 / (q : ℝ)) :=
    (finiteKernelObservable_source_error law K μ (fun y => ψ (f y)) hψ hK hK0 hKM hC
      (fun x => ψ (f (sample x))) F hF).trans hsmooth
  have hlast : ‖(∫ y, ψ (f y) * obs y ∂μ) * (C : ℂ) -
      (∫ y, φ y * obs y ∂μ) * (C : ℂ)‖ ≤ C * ∫ y, ‖ψ (f y) - φ y‖ ∂μ := by
    rw [← sub_mul, ← integral_sub hiψ hiφ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC, mul_comm C]
    apply mul_le_mul_of_nonneg_right _ hC.le
    apply norm_integral_le_of_norm_le (hψ.sub hφ).norm
    apply ae_of_all μ
    intro y
    rw [← sub_mul, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hb y) (norm_nonneg _)).trans_eq (mul_one _)
  have htri := dist_triangle (law.complexMean (fun x => φ (sample x) * F x))
    (law.complexMean (fun x => ψ (f (sample x)) * F x)) ((∫ y, φ y * obs y ∂μ) * (C : ℂ))
  have htri2 := dist_triangle (law.complexMean (fun x => ψ (f (sample x)) * F x))
    ((∫ y, ψ (f y) * obs y ∂μ) * (C : ℂ)) ((∫ y, φ y * obs y ∂μ) * (C : ℂ))
  simp only [dist_eq_norm] at htri htri2
  linarith only [htri, htri2, hfirst, hmiddle, hlast]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem majorant_reweight_norm {v F : ℂ} {w : ℝ} (hv : ‖v‖ ≤ w) (hF : ‖F‖ ≤ 1) :
    ‖(v / (w : ℂ)) * F‖ ≤ 1 := by
  by_cases hw : w = 0
  · simp only [hw, Complex.ofReal_zero, div_zero, zero_mul, norm_zero, zero_le_one]
  · have hw0 : 0 < w := lt_of_le_of_ne ((norm_nonneg v).trans hv) (Ne.symm hw)
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
    exact (mul_le_mul ((div_le_one hw0).mpr hv) hF (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem majorant_reweight_exact {v F : ℂ} {w : ℝ} (hv : ‖v‖ ≤ w) :
    (w : ℂ) * ((v / (w : ℂ)) * F) = v * F := by
  by_cases hw : w = 0
  · have hv0 : v = 0 := norm_le_zero_iff.mp (by simpa only [hw] using hv)
    simp only [hw, hv0, Complex.ofReal_zero, zero_mul]
  · have hwc : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw
    field_simp

variable {H J : Type*} [AddCommGroup H] [MeasurableSpace H] [Fintype J]
variable [TopologicalSpace H] [IsTopologicalAddGroup H] [BorelSpace H] [MeasurableAdd₂ H]
variable (μ : Measure H) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
variable (f : H →+ (J → UnitAddCircle)) (hf : Continuous f) {q : ℕ} (hq : 0 < q)

include hf hq

theorem finiteAmbientMajorant_transfer {Ω : Type*} [Fintype Ω]
    (law : FiniteProbabilityWeights Ω) (sample : Ω → H)
    {C : ℝ} (hC : 0 < C)
    (hden : ∀ y, law.mean (fun x => ambientTentKernel μ f q (sample x) y) ≤ C)
    (ψ : (J → UnitAddCircle) → ℝ) {L : ℝ≥0} (hL : LipschitzWith L ψ)
    (hψ : Integrable (fun y => ψ (f y)) μ)
    (v F : Ω → ℂ) (hv : ∀ x, ‖v x‖ ≤ ψ (f (sample x))) (hF : ∀ x, ‖F x‖ ≤ 1) :
    let weight := fun x => (v x / (ψ (f (sample x)) : ℂ)) * F x
    let obs := finiteKernelObservable law (fun x => ambientTentKernel μ f q (sample x)) C weight
    Measurable obs ∧ (∀ y, ‖obs y‖ ≤ 1) ∧
      Integrable (fun y => (ψ (f y) : ℂ) * obs y) μ ∧
      ‖law.complexMean (fun x => v x * F x) -
        (∫ y, (ψ (f y) : ℂ) * obs y ∂μ) * (C : ℂ)‖ ≤ (L : ℝ) * (4 / (q : ℝ)) := by
  intro weight obs
  have hw : ∀ x, ‖weight x‖ ≤ 1 := fun x => majorant_reweight_norm (hv x) (hF x)
  have hLc : LipschitzWith L (fun z => (ψ z : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z t
    rw [Complex.isometry_ofReal.dist_eq]
    exact hL.dist_le_mul z t
  obtain ⟨hm, hb, hi, he⟩ := finiteAmbientKernel_transfer μ f hf hq law sample hC hden
    (fun y => (ψ (f y) : ℂ)) hψ.ofReal (fun z => (ψ z : ℂ)) hLc hψ.ofReal weight hw
  have heq : law.complexMean (fun x => (ψ (f (sample x)) : ℂ) * weight x) =
      law.complexMean (fun x => v x * F x) := by
    apply law.complexMean_congr_support
    intro x _
    exact majorant_reweight_exact (hv x)
  refine ⟨hm, hb, hi, ?_⟩
  simpa only [heq, sub_self, norm_zero, law.mean_const, integral_zero, mul_zero, zero_add, add_zero] using he

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {O J : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coveredJetAmbientHom (d : ℕ) :
    EuclideanJetLayers U O →+ (JetAmbientIndex O J → UnitAddCircle) where
  toFun := coveredJetAmbientTorus U d
  map_zero' := by ext a; simp [coveredJetAmbientTorus]
  map_add' x y := by ext a; simp [coveredJetAmbientTorus]

end Erdos3.VectorPolynomial

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))

variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))

noncomputable def physicalJetTentKernel (n : ℕ) : EuclideanJetLayers U jets → EuclideanJetLayers U jets → ℝ :=
  ambientTentKernel haar (coveredJetAmbientHom U 1) n

variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

theorem physicalJetTentKernel_properties {n : ℕ} (hn : 0 < n) (a : EuclideanJetLayers U jets) :
    Measurable (physicalJetTentKernel U ν n a) ∧
      Integrable (physicalJetTentKernel U ν n a) haar ∧
      (∫ y, physicalJetTentKernel U ν n a y ∂haar) = 1 ∧
      ∀ y, 0 ≤ physicalJetTentKernel U ν n a y ∧
        physicalJetTentKernel U ν n a y ≤ 2 * (n : ℝ) ^ Fintype.card (JetAmbientIndex jets J) := by
  let : ∀ j, (Measure.pi (fun _ : jets j => ν j)).IsAddLeftInvariant :=
    fun _ => Measure.pi.isAddLeftInvariant _
  let : (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))).IsAddLeftInvariant :=
    Measure.pi.isAddLeftInvariant _
  have hf : Continuous (coveredJetAmbientHom (O := jets) U 1) := coveredJetAmbientTorus_continuous U 1
  exact ⟨(ambientTentKernel_continuous haar (coveredJetAmbientHom U 1) hf hn a).measurable,
    ambientTentKernel_integrable haar (coveredJetAmbientHom U 1) hf hn a,
    ambientTentKernel_integral haar (coveredJetAmbientHom U 1) hf hn a,
    ambientTentKernel_range haar (coveredJetAmbientHom U 1) hf hn a⟩

theorem exists_physicalJetTent_fourier {n : ℕ} (hn : 0 < n)
    (a : EuclideanJetLayers U jets) {δ L : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    (hamb : (Fintype.card (JetAmbientIndex jets J) : ℝ) ≤ L)
    (hLip : (n : ℝ) ^ (Fintype.card (JetAmbientIndex jets J) + 1) ≤ Real.exp L)
    (hδL : δ⁻¹ ≤ Real.exp L) :
    ∃ (F : Type) (inst : Fintype F), let _ : Fintype F := inst
    ∃ (frequency : F → ∀ j, (Fin dim →₀ ℕ) → J j → ℤ) (c : F → ℂ),
      (∀ t j e, e.degree ≤ j.val + 1 → ∀ i,
        |(frequency t j e i : ℝ)| ≤ Real.exp ((2 * L + 2) ^ 4)) ∧
      (∑ t, ‖c t‖) ≤ Real.exp (2 * L * (2 * L + 2) ^ 4) *
        (2 * (n : ℝ) ^ Fintype.card (JetAmbientIndex jets J)) ∧
      ∀ y, ‖(physicalJetTentKernel U ν n a (standardPhysicalJetMap U y) : ℂ) -
        coefficientTorusFourierSum U frequency c y‖ ≤ δ := by
  let : ∀ j, (Measure.pi (fun _ : jets j => ν j)).IsAddLeftInvariant :=
    fun _ => Measure.pi.isAddLeftInvariant _
  let : (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))).IsAddLeftInvariant :=
    Measure.pi.isAddLeftInvariant _
  let f := coveredJetAmbientHom (O := jets) U 1
  have hf : Continuous f := coveredJetAmbientTorus_continuous U 1
  let Ltent : ℝ≥0 := (n : ℝ≥0) ^ (Fintype.card (JetAmbientIndex jets J) + 1)
  let Btent : ℝ≥0 := 2 * (n : ℝ≥0) ^ Fintype.card (JetAmbientIndex jets J)
  let k := fun z => normalizedAmbientTent haar f n (z - f a)
  have hk := normalizedAmbientTent_shift_lipschitz haar f hf hn (f a)
  have hkc : LipschitzWith Ltent (fun z => (k z : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [Complex.isometry_ofReal.dist_eq]
    exact hk.dist_le_mul z w
  have hz := ambientTentMass_pos haar f hf hn
  have hi := ambientTentMass_inv_le haar f hf hn
  have hb (z) : ‖(k z : ℂ)‖ ≤ Btent := by
    have h0 : 0 ≤ k z := div_nonneg (ambientTorusTent_range n _).1 hz.le
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    exact (div_le_div_of_nonneg_right (ambientTorusTent_range n _).2 hz.le).trans hi
  obtain ⟨F, inst, frequency, c, _hcard, hfreq, hsum, herr⟩ :=
    exists_ambient_torus_fourier_approximation (fun z => (k z : ℂ)) Ltent Btent hkc hb
      hδ hL hamb (by simpa only [Ltent, NNReal.coe_pow, NNReal.coe_natCast] using hLip) hδL
  let _ := inst
  refine ⟨F, inst, fun t => standardJetFrequency 1 (frequency t), c, ?_, ?_, ?_⟩
  · intro t j e he i
    simpa only [Nat.cast_one, mul_one] using standardJetFrequency_bound 1 (frequency t) (hfreq t) j e he i
  · simpa only [Btent, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow, NNReal.coe_natCast] using hsum
  · intro y
    change ‖(normalizedAmbientTent haar f n (f (standardPhysicalJetMap U y - a)) : ℂ) -
      coefficientTorusFourierSum U (fun t => standardJetFrequency 1 (frequency t)) c y‖ ≤ δ
    rw [map_sub]
    rw [show f (standardPhysicalJetMap U y) = coveredJetAmbientTorus U 1 (standardPhysicalJetMap U y) from rfl]
    simpa only [k, coefficientTorusFourierSum, standardJetFrequency_character] using
      herr (coveredJetAmbientTorus U 1 (standardPhysicalJetMap U y))

end Erdos3.BooleanCubeKernel

end

end OAI
