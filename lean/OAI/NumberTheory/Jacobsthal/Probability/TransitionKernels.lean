import Mathlib.Probability.Kernel.WithDensity
import OAI.NumberTheory.Jacobsthal.Analysis.WeightFutureIntegrals

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.TransitionKernels

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open LinearSieveFunctions BuchstabBridge NormalizedDeficits
open DerivativeWeights WeightFutureIntegrals

abbrev EvenState := {s : ℝ // 198 / 100 ≤ s}
abbrev OddState := {s : ℝ // 95 / 100 ≤ s}

noncomputable def tailDensity (left mass : ℝ) (B : ℝ → ℝ) : ℝ → ℝ :=
  (Ici left).indicator (fun t => B t / mass)

theorem tailDensity_nonneg {left mass : ℝ} {B : ℝ → ℝ} (hm : 0 < mass)
    (hB : ∀ t, left ≤ t → 0 ≤ B t) (t : ℝ) : 0 ≤ tailDensity left mass B t := by
  unfold tailDensity
  by_cases ht : left ≤ t
  · rw [indicator_of_mem (show t ∈ Ici left from ht)]
    exact div_nonneg (hB t ht) hm.le
  · rw [indicator_of_notMem (show t ∉ Ici left from ht)]

theorem tailDensity_integrable {left mass : ℝ} {B : ℝ → ℝ}
    (hB : IntegrableOn B (Ioi left)) : Integrable (tailDensity left mass B) := by
  unfold tailDensity
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  exact (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hB).div_const mass

theorem tailDensity_integral {left mass : ℝ} {B : ℝ → ℝ} (hm : 0 < mass)
    (hB : mass = ∫ t in Ioi left, B t) : ∫ t, tailDensity left mass B t = 1 := by
  unfold tailDensity
  rw [integral_indicator measurableSet_Ici, integral_div, integral_Ici_eq_integral_Ioi, ← hB]
  exact div_self (ne_of_gt hm)

theorem phiEven_measurable : Measurable phiEven := by
  have hF : Measurable (F sieveA) := by
    unfold F
    exact (measurable_const.mul
      (((plus_continuous.comp (continuous_id.sub continuous_const)).add
        (Dickman.rho_continuous.comp (continuous_id.sub continuous_const))).measurable)).div
      (measurable_const.mul measurable_id)
  unfold phiEven
  apply Measurable.ite measurableSet_Iic
  · unfold evenInitial
    exact measurable_const.mul ((measurable_id.div (measurable_id.sub measurable_const)).sub
      (Real.measurable_log.comp (measurable_id.sub measurable_const)))
  · exact measurable_id.mul (lowerDeficit_continuous.measurable.add
      ((hF.sub measurable_const).comp (measurable_id.sub measurable_const)))

theorem W_measurable : Measurable W := by
  unfold W
  exact (measurable_id.add measurable_const).div (measurable_id.pow_const 2)

noncomputable def evenDensity (s : EvenState) : ℝ → ℝ :=
  tailDensity (s.1 - 1) (phiEven s.1) (fun t => W t * phiOdd t)

noncomputable def oddDensity (s : OddState) : ℝ → ℝ :=
  tailDensity (max 2 (s.1 - 1)) (phiOdd s.1) (fun t => W t * phiEven t)

theorem evenDensity_measurable : Measurable (Function.uncurry evenDensity) := by
  change Measurable (fun x : EvenState × ℝ =>
    if x.1.1 - 1 ≤ x.2 then W x.2 * phiOdd x.2 / phiEven x.1.1 else 0)
  apply Measurable.ite
    (measurableSet_le ((measurable_subtype_coe.comp measurable_fst).sub measurable_const) measurable_snd)
  · exact ((W_measurable.comp measurable_snd).mul
      (phiOdd_continuous.measurable.comp measurable_snd)).div
      (phiEven_measurable.comp (measurable_subtype_coe.comp measurable_fst))
  · exact measurable_const

theorem oddDensity_measurable : Measurable (Function.uncurry oddDensity) := by
  change Measurable (fun x : OddState × ℝ =>
    if max 2 (x.1.1 - 1) ≤ x.2 then W x.2 * phiEven x.2 / phiOdd x.1.1 else 0)
  apply Measurable.ite
    (measurableSet_le (measurable_const.max
      ((measurable_subtype_coe.comp measurable_fst).sub measurable_const)) measurable_snd)
  · exact ((W_measurable.comp measurable_snd).mul
      (phiEven_measurable.comp measurable_snd)).div
      (phiOdd_continuous.measurable.comp (measurable_subtype_coe.comp measurable_fst))
  · exact measurable_const

theorem evenDensity_nonneg (s : EvenState) (t : ℝ) : 0 ≤ evenDensity s t := by
  have hs : 1 < s.1 := by linarith [s.2]
  apply tailDensity_nonneg (phiEven_pos hs) ?_ t
  intro u hu
  exact (mul_pos (W_pos (by linarith)) (phiOdd_pos u)).le

theorem oddDensity_nonneg (s : OddState) (t : ℝ) : 0 ≤ oddDensity s t := by
  apply tailDensity_nonneg (phiOdd_pos s.1) ?_ t
  intro u hu
  have hu1 : 1 < u := by linarith [le_max_left (2 : ℝ) (s.1 - 1)]
  exact (mul_pos (W_pos (by linarith)) (phiEven_pos hu1)).le

theorem evenDensity_integrable (s : EvenState) : Integrable (evenDensity s) :=
  tailDensity_integrable (phiEven_future_integral (s := s.1) (by linarith [s.2])).1

theorem oddDensity_integrable (s : OddState) : Integrable (oddDensity s) :=
  tailDensity_integrable (phiOdd_future_integral s.1).1

theorem evenDensity_integral (s : EvenState) : ∫ t, evenDensity s t = 1 :=
  tailDensity_integral (phiEven_pos (by linarith [s.2]))
    (phiEven_future_integral (s := s.1) (by linarith [s.2])).2

theorem oddDensity_integral (s : OddState) : ∫ t, oddDensity s t = 1 :=
  tailDensity_integral (phiOdd_pos s.1) (phiOdd_future_integral s.1).2

noncomputable def evenKernel : Kernel EvenState ℝ :=
  (Kernel.const EvenState volume).withDensity (fun s t => ENNReal.ofReal (evenDensity s t))

noncomputable def oddKernel : Kernel OddState ℝ :=
  (Kernel.const OddState volume).withDensity (fun s t => ENNReal.ofReal (oddDensity s t))

theorem evenKernel_apply (s : EvenState) (B : Set ℝ) :
    evenKernel s B = ∫⁻ t in B, ENNReal.ofReal (evenDensity s t) := by
  exact Kernel.withDensity_apply' (Kernel.const EvenState volume)
    (f := fun s t => ENNReal.ofReal (evenDensity s t))
    (ENNReal.measurable_ofReal.comp evenDensity_measurable) s B

theorem oddKernel_apply (s : OddState) (B : Set ℝ) :
    oddKernel s B = ∫⁻ t in B, ENNReal.ofReal (oddDensity s t) := by
  exact Kernel.withDensity_apply' (Kernel.const OddState volume)
    (f := fun s t => ENNReal.ofReal (oddDensity s t))
    (ENNReal.measurable_ofReal.comp oddDensity_measurable) s B

instance evenKernel_isMarkovKernel : IsMarkovKernel evenKernel := by
  constructor
  intro s
  constructor
  rw [evenKernel_apply, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (evenDensity_integrable s)
      (Eventually.of_forall (evenDensity_nonneg s)), evenDensity_integral]
  norm_num

instance oddKernel_isMarkovKernel : IsMarkovKernel oddKernel := by
  constructor
  intro s
  constructor
  rw [oddKernel_apply, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (oddDensity_integrable s)
      (Eventually.of_forall (oddDensity_nonneg s)), oddDensity_integral]
  norm_num

theorem evenKernel_below_support (s : EvenState) : evenKernel s (Iio (s.1 - 1)) = 0 := by
  rw [evenKernel_apply]
  apply setLIntegral_eq_zero measurableSet_Iio
  intro t ht
  have hn : t ∉ Ici (s.1 - 1) := by
    change ¬s.1 - 1 ≤ t
    change t < s.1 - 1 at ht
    exact not_le_of_gt ht
  simp only [evenDensity, tailDensity, indicator_of_notMem hn, ENNReal.ofReal_zero, Pi.zero_apply]

theorem oddKernel_below_support (s : OddState) : oddKernel s (Iio (max 2 (s.1 - 1))) = 0 := by
  rw [oddKernel_apply]
  apply setLIntegral_eq_zero measurableSet_Iio
  intro t ht
  have hn : t ∉ Ici (max 2 (s.1 - 1)) := by
    change ¬max 2 (s.1 - 1) ≤ t
    change t < max 2 (s.1 - 1) at ht
    exact not_le_of_gt ht
  simp only [oddDensity, tailDensity, indicator_of_notMem hn, ENNReal.ofReal_zero, Pi.zero_apply]

theorem evenKernel_ae_support (s : EvenState) : ∀ᵐ t ∂evenKernel s, s.1 - 1 ≤ t := by
  apply ae_iff.mpr
  convert! evenKernel_below_support s using 1
  congr 1
  ext t
  simp only [mem_ofPred_eq, mem_Iio, not_le]

theorem oddKernel_ae_support (s : OddState) : ∀ᵐ t ∂oddKernel s, max 2 (s.1 - 1) ≤ t := by
  apply ae_iff.mpr
  convert! oddKernel_below_support s using 1
  congr 1
  ext t
  simp only [mem_ofPred_eq, mem_Iio, not_le]

theorem evenKernel_ae_odd_domain (s : EvenState) : ∀ᵐ t ∂evenKernel s, 95 / 100 ≤ t := by
  filter_upwards [evenKernel_ae_support s] with t ht
  linarith [s.2]

theorem oddKernel_ae_even_domain (s : OddState) : ∀ᵐ t ∂oddKernel s, 198 / 100 ≤ t := by
  filter_upwards [oddKernel_ae_support s] with t ht
  linarith [le_max_left (2 : ℝ) (s.1 - 1)]

end NumberTheoryLean.TransitionKernels

end

end Erdos970

end OAI
