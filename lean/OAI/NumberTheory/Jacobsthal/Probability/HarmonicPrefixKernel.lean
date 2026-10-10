import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic

namespace OAI

namespace Erdos970

section

namespace ErdosPrimeInputs.WeightedKernelMass

open Set Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

noncomputable def mass (K : Kernel α α) (n : ℕ) (x : α) : ℝ≥0∞ := (K^n) x univ

@[simp] theorem mass_zero (K : Kernel α α) (x : α) : mass K 0 x = 1 := by
  change (Measure.dirac x) univ = 1
  simp

lemma mass_succ (K : Kernel α α) (n : ℕ) (x : α) :
    mass K (n+1) x = ∫⁻ y, mass K n y ∂K x := by
  unfold mass
  rw [pow_succ]
  exact Kernel.comp_apply' _ _ _ MeasurableSet.univ

lemma mass_measurable (K : Kernel α α) (n : ℕ) : Measurable (mass K n) :=
  (K^n).measurable_coe MeasurableSet.univ

theorem weighted_sum_succ (K : Kernel α α) (c : ℝ≥0∞) (N : ℕ) (x : α) :
    (∑ n ∈ range (N+1), c^n * mass K n x) =
      1 + c * ∫⁻ y, (∑ n ∈ range N, c^n * mass K n y) ∂K x := by
  rw [lintegral_finsetSum (range N) (f := fun n y => c^n * mass K n y) (fun n _ => measurable_const.mul (mass_measurable K n)),mul_sum]
  simp_rw [lintegral_const_mul _ (mass_measurable K _),← mass_succ]
  rw [Finset.sum_range_succ']
  simp only [pow_zero,mass_zero,one_mul]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [pow_succ]
  ring

theorem weighted_finite_bound (K : Kernel α α) (c : ℝ≥0∞) (V : α → ℝ≥0∞)
    (hV : ∀ x, 1 + c * (∫⁻ y, V y ∂K x) ≤ V x) :
    ∀ N : ℕ, ∀ x : α, (∑ n ∈ range N, c^n * mass K n x) ≤ V x := by
  intro N
  induction N with
  | zero => intro x; simp
  | succ N ih =>
    intro x
    rw [weighted_sum_succ]
    exact (add_le_add le_rfl (mul_le_mul le_rfl (lintegral_mono (fun y => ih y)) zero_le zero_le)).trans (hV x)

theorem weighted_total_bound (K : Kernel α α) (c : ℝ≥0∞) (V : α → ℝ≥0∞)
    (hV : ∀ x, 1 + c * (∫⁻ y, V y ∂K x) ≤ V x) (x : α) :
    (∑' n : ℕ, c^n * mass K n x) ≤ V x := by
  exact ENNReal.tsum_le_of_sum_range_le (fun N => weighted_finite_bound K c V hV N x)

end ErdosPrimeInputs.WeightedKernelMass

end

section

namespace ErdosPrimeInputs.HarmonicPrefixKernel

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open WeightedKernelMass

noncomputable def density (ell B t : ℝ) : ℝ≥0∞ :=
  if ell<t ∧ t≤B then ENNReal.ofReal (t⁻¹) else 0

lemma density_measurable (ell : ℝ) : Measurable (Function.uncurry (density ell)) := by
  exact Measurable.ite
    ((measurableSet_lt measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_fst))
    (ENNReal.measurable_ofReal.comp measurable_snd.inv) measurable_const

noncomputable def kernel (ell : ℝ) : Kernel ℝ ℝ :=
  (Kernel.const ℝ (volume : Measure ℝ)).withDensity (density ell)

instance kernel_isSFinite (ell : ℝ) : IsSFiniteKernel (kernel ell) := by
  unfold kernel
  apply Kernel.IsSFiniteKernel.withDensity
  intro B t
  unfold density
  split_ifs <;> simp

theorem kernel_lintegral (ell B : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ t, f t ∂kernel ell B) = ∫⁻ t in Ioc ell B, ENNReal.ofReal (t⁻¹)*f t := by
  rw [kernel,Kernel.lintegral_withDensity _ (density_measurable ell) B hf,Kernel.const_apply]
  have heq : (fun t => density ell B t * f t) = (Ioc ell B).indicator (fun t => ENNReal.ofReal (t⁻¹)*f t) := by
    funext t
    simp only [density,Set.indicator,mem_Ioc,ite_mul,zero_mul]
  rw [heq,lintegral_indicator measurableSet_Ioc]

theorem kernel_eq_restrict (ell B : ℝ) : kernel ell B =
    (volume.restrict (Ioc ell B)).withDensity (fun t : ℝ => ENNReal.ofReal (t⁻¹)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [kernel_lintegral ell B hf]
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (t⁻¹)) := ENNReal.measurable_ofReal.comp measurable_inv
  exact (lintegral_withDensity_eq_lintegral_mul _ hm hf).symm

lemma kernel_eq_zero {ell B : ℝ} (hB : B≤ell) : kernel ell B = 0 := by
  rw [kernel_eq_restrict,Ioc_eq_empty_of_le hB]
  simp

noncomputable def bound (ell B : ℝ) : ℝ := max 1 (B/ell)
noncomputable def boundE (ell B : ℝ) : ℝ≥0∞ := ENNReal.ofReal (bound ell B)

lemma bound_measurable (ell : ℝ) : Measurable (bound ell) :=
  measurable_const.max (measurable_id.div_const ell)

lemma boundE_measurable (ell : ℝ) : Measurable (boundE ell) :=
  ENNReal.measurable_ofReal.comp (bound_measurable ell)

lemma bound_on {ell B : ℝ} (hell : 0<ell) (hB : ell≤B) : bound ell B = B/ell := by
  exact max_eq_right ((le_div_iff₀ hell).mpr (by linarith))

lemma bound_below {ell B : ℝ} (hell : 0<ell) (hB : B≤ell) : bound ell B = 1 := by
  exact max_eq_left ((div_le_iff₀ hell).mpr (by linarith))

lemma harmonic_bound_integral {ell B : ℝ} (hell : 0<ell) :
    (∫⁻ t, boundE ell t ∂kernel ell B) = ENNReal.ofReal ((B-ell)/ell) := by
  rw [kernel_lintegral ell B (boundE_measurable ell)]
  calc
    _ = ∫⁻ _t in Ioc ell B, ENNReal.ofReal (1/ell) := by
      apply lintegral_congr_ae
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro t ht
      have ht0 : 0<t := hell.trans ht.1
      change ENNReal.ofReal (t⁻¹) * ENNReal.ofReal (bound ell t) = _
      rw [bound_on hell ht.1.le,← ENNReal.ofReal_mul (inv_nonneg.mpr ht0.le)]
      congr 1
      field_simp
    _ = _ := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioc,
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ)≤1/ell)]
      congr 1
      ring

theorem schur_one {ell : ℝ} (hell : 0<ell) (B : ℝ) :
    1 + (∫⁻ t, boundE ell t ∂kernel ell B) = boundE ell B := by
  by_cases hB : ell≤B
  · rw [harmonic_bound_integral hell,boundE,bound_on hell hB]
    calc
      _ = ENNReal.ofReal (1+(B-ell)/ell) := by
        rw [ENNReal.ofReal_add (by norm_num) (div_nonneg (sub_nonneg.mpr hB) hell.le)]
        simp
      _ = _ := by
        congr 1
        field_simp
        ring
  · rw [kernel_eq_zero (le_of_not_ge hB),boundE,bound_below hell (le_of_not_ge hB)]
    simp

theorem total_prefix_mass {ell B : ℝ} (hell : 0<ell) (hB : ell≤B) :
    (∑' n : ℕ, mass (kernel ell) n B) ≤ ENNReal.ofReal (B/ell) := by
  have h := weighted_total_bound (kernel ell) 1 (boundE ell)
    (fun x => by simpa only [one_mul] using (schur_one hell x).le) B
  simpa only [one_pow,one_mul,boundE,bound_on hell hB] using h

end ErdosPrimeInputs.HarmonicPrefixKernel

end

end Erdos970

end OAI
