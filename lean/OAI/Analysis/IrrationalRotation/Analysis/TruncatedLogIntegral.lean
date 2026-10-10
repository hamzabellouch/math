import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem lintegral_cost_eq_iSup_truncations (g : X → ℝ) (hm : Measurable g) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂μ) =
      ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (g x) (n : ℝ)) ∂μ := by
  have hsup (x : X) :
      (⨆ n : ℕ, ENNReal.ofReal (min (g x) (n : ℝ))) = ENNReal.ofReal (g x) := by
    apply le_antisymm
    · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · obtain ⟨n, hn⟩ := exists_nat_gt (g x)
      exact le_iSup_of_le n (by rw [min_eq_left hn.le])
  rw [← lintegral_iSup]
  · exact lintegral_congr (fun x => (hsup x).symm)
  · intro n
    exact (hm.min measurable_const).ennreal_ofReal
  · intro n m hnm x
    exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hnm))

theorem integrable_min_nat_cost [IsFiniteMeasure μ]
    (g : X → ℝ) (hm : Measurable g) (hg : ∀ x, 0 ≤ g x) (n : ℕ) :
    Integrable (fun x => min (g x) (n : ℝ)) μ := by
  refine (integrable_const (μ := μ) (n : ℝ)).mono'
    (hm.min measurable_const).aestronglyMeasurable ?_
  exact ae_of_all μ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hg x) (Nat.cast_nonneg n))]
    exact min_le_right _ _

theorem exists_integral_truncation_gt [IsFiniteMeasure μ]
    (g : X → ℝ) (hm : Measurable g) (hg : ∀ x, 0 ≤ g x)
    (hinf : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ∞) (A : ℝ) :
    ∃ n : ℕ, A < ∫ x, min (g x) (n : ℝ) ∂μ := by
  have hs : (⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (g x) (n : ℝ)) ∂μ) = ∞ := by
    rw [← lintegral_cost_eq_iSup_truncations g hm, hinf]
  have ht : ENNReal.ofReal A <
      ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (g x) (n : ℝ)) ∂μ := by
    rw [hs]
    exact ENNReal.ofReal_lt_top
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp ht
  refine ⟨n, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_min_nat_cost g hm hg n)
    (ae_of_all μ fun x => le_min (hg x) (Nat.cast_nonneg n))] at hn
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp hn).1

theorem log_max_exp_neg (g M : ℝ) :
    Real.log (max (Real.exp (-g)) (Real.exp (-M))) = -min g M := by
  rcases le_total g M with h | h
  · rw [max_eq_left (Real.exp_le_exp.mpr (neg_le_neg h)), Real.log_exp, min_eq_left h]
  · rw [max_eq_right (Real.exp_le_exp.mpr (neg_le_neg h)), Real.log_exp, min_eq_right h]

theorem integral_truncated_log_eq_neg_cost
    (f g : X → ℝ) (hfg : f =ᵐ[μ] fun x => Real.exp (-g x)) (M : ℝ) :
    (∫ x, Real.log (max (f x) (Real.exp (-M))) ∂μ) =
      -(∫ x, min (g x) M ∂μ) := by
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx, log_max_exp_neg]

theorem exists_truncated_log_integral_lt_of_cost [IsFiniteMeasure μ]
    (f g : X → ℝ) (hm : Measurable g) (hg : ∀ x, 0 ≤ g x)
    (hfg : f =ᵐ[μ] fun x => Real.exp (-g x))
    (hinf : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ∞) (A : ℝ) :
    ∃ n : ℕ, (∫ x, Real.log (max (f x) (Real.exp (-(n : ℝ)))) ∂μ) < -A := by
  obtain ⟨n, hn⟩ := exists_integral_truncation_gt g hm hg hinf A
  refine ⟨n, ?_⟩
  rw [integral_truncated_log_eq_neg_cost f g hfg]
  exact neg_lt_neg hn

theorem exists_truncated_log_integral_lt [IsFiniteMeasure μ]
    (f : X → ℝ) (hm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hpos : ∀ᵐ x ∂μ, 0 < f x)
    (hinf : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ) = ∞) (A : ℝ) :
    ∃ n : ℕ, (∫ x, Real.log (max (f x) (Real.exp (-(n : ℝ)))) ∂μ) < -A := by
  refine exists_truncated_log_integral_lt_of_cost f (fun x => -Real.log (f x))
    hm.log.neg (fun x => neg_nonneg.mpr (Real.log_nonpos (hf0 x) (hf1 x))) ?_ hinf A
  filter_upwards [hpos] with x hx
  simp [Real.exp_log hx]

theorem tendsto_integral_truncations_atTop [IsFiniteMeasure μ]
    (g : X → ℝ) (hm : Measurable g) (hg : ∀ x, 0 ≤ g x)
    (hinf : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ∞) :
    Tendsto (fun n : ℕ => ∫ x, min (g x) (n : ℝ) ∂μ) atTop atTop := by
  apply tendsto_atTop.2
  intro A
  obtain ⟨n, hn⟩ := exists_integral_truncation_gt g hm hg hinf A
  filter_upwards [eventually_ge_atTop n] with m hnm
  refine hn.le.trans (integral_mono (integrable_min_nat_cost g hm hg n)
    (integrable_min_nat_cost g hm hg m) ?_)
  intro x
  exact min_le_min (le_refl (g x)) (Nat.cast_le.mpr hnm)

theorem tendsto_truncated_log_integrals_atBot [IsFiniteMeasure μ]
    (f : X → ℝ) (hm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hpos : ∀ᵐ x ∂μ, 0 < f x)
    (hinf : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ) = ∞) :
    Tendsto (fun n : ℕ => ∫ x, Real.log (max (f x) (Real.exp (-(n : ℝ)))) ∂μ)
      atTop atBot := by
  have hfg : f =ᵐ[μ] fun x => Real.exp (-(-Real.log (f x))) := by
    filter_upwards [hpos] with x hx
    simp [Real.exp_log hx]
  have h := tendsto_neg_atTop_atBot.comp
    (tendsto_integral_truncations_atTop (fun x => -Real.log (f x)) hm.log.neg
      (fun x => neg_nonneg.mpr (Real.log_nonpos (hf0 x) (hf1 x))) hinf)
  convert h using 1
  funext n
  exact integral_truncated_log_eq_neg_cost f (fun x => -Real.log (f x)) hfg (n : ℝ)

theorem exists_pos_truncated_log_integral_lt [IsFiniteMeasure μ]
    (f : X → ℝ) (hm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hpos : ∀ᵐ x ∂μ, 0 < f x)
    (hinf : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ) = ∞) (a : ℝ) :
    ∃ M : ℝ, 0 < M ∧
      (∫ x, Real.log (max (f x) (Real.exp (-M))) ∂μ) < -2 * a := by
  have hlim := tendsto_truncated_log_integrals_atBot f hm hf0 hf1 hpos hinf
  have hneg : ∀ᶠ n : ℕ in atTop,
      (∫ x, Real.log (max (f x) (Real.exp (-(n : ℝ)))) ∂μ) < -2 * a :=
    hlim.eventually (eventually_lt_atBot (-2 * a))
  obtain ⟨n, hn, hnint⟩ := ((eventually_gt_atTop (0 : ℕ)).and hneg).exists
  exact ⟨n, Nat.cast_pos.mpr hn, hnint⟩

theorem continuous_truncated_log {Y : Type*} [TopologicalSpace Y]
    (f : Y → ℝ) (hf : Continuous f) (M : ℝ) :
    Continuous (fun x => Real.log (max (f x) (Real.exp (-M)))) := by
  apply (hf.max continuous_const).log
  intro x
  exact ne_of_gt ((Real.exp_pos (-M)).trans_le (le_max_right _ _))

end Invariant233

end OAI
