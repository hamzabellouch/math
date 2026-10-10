import OAI.Probability.BenjaminiSchramm.RestrictedMomentHolder
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma ennreal_exp_rpow (t a : ℝ) (ha : 0 ≤ a) :
    ENNReal.ofReal (Real.exp t)^a=ENNReal.ofReal (Real.exp (t*a)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) ha,←Real.exp_mul]

lemma fractional_height_slice_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Set Ω)
    (X : Ω → ℝ≥0∞) (hX : Measurable X) (C B : ℝ≥0∞) (t s : ℝ) (n : ℕ)
    (hfirst : (∫⁻ ω in S, X ω ∂μ) ≤ C*ENNReal.ofReal (Real.exp (t*n)))
    (hprob : μ S ≤ B*ENNReal.ofReal (Real.exp (-s*n)))
    {a δ : ℝ} (ha : 0 < a) (ha1 : a < 1) (hδ : 0 ≤ δ) (hδa : δ ≤ 1-a) :
    (∫⁻ ω in S, X ω^a ∂μ) ≤
      C^a*B^δ*ENNReal.ofReal (Real.exp ((t*a-s*δ)*n)) := by
  have hmeasure : (μ S)^(1-a) ≤ (B*ENNReal.ofReal (Real.exp (-s*n)))^δ :=
    (ENNReal.rpow_le_rpow_of_exponent_ge (prob_le_one (μ := μ)) hδa).trans
      (ENNReal.rpow_le_rpow hprob hδ)
  have hh := (restricted_fractional_moment_holder μ S X hX ha ha1).trans
    (mul_le_mul' (ENNReal.rpow_le_rpow hfirst ha.le) hmeasure)
  rw [ENNReal.mul_rpow_of_nonneg _ _ ha.le,ENNReal.mul_rpow_of_nonneg _ _ hδ,
    ennreal_exp_rpow _ _ ha.le,ennreal_exp_rpow _ _ hδ] at hh
  have he : (C^a*ENNReal.ofReal (Real.exp (t*n*a)))*
      (B^δ*ENNReal.ofReal (Real.exp (-s*n*δ))) =
      C^a*B^δ*ENNReal.ofReal (Real.exp ((t*a-s*δ)*n)) := by
    calc
      _ = (C^a*B^δ)*(ENNReal.ofReal (Real.exp (t*n*a))*ENNReal.ofReal (Real.exp (-s*n*δ))) := by ac_rfl
      _ = _ := by
        rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
        rw [show t*(n : ℝ)*a+ -s*n*δ=(t*a-s*δ)*n by ring]
  exact hh.trans_eq he

theorem fractional_moment_of_height_slices {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : ℕ → Set Ω) (hS : ∀ n, MeasurableSet (S n))
    (hcover : ∀ᵐ ω ∂μ, ∃ n, ω ∈ S n) (X : Ω → ℝ≥0∞) (hX : Measurable X)
    (C B : ℝ≥0∞) (t s : ℝ)
    (hfirst : ∀ n : ℕ, (∫⁻ ω in S n, X ω ∂μ) ≤ C*ENNReal.ofReal (Real.exp (t*n)))
    (hprob : ∀ n : ℕ, μ (S n) ≤ B*ENNReal.ofReal (Real.exp (-s*n)))
    {a δ : ℝ} (ha : 0 < a) (ha1 : a < 1) (hδ : 0 ≤ δ) (hδa : δ ≤ 1-a) :
    (∫⁻ ω, X ω^a ∂μ) ≤
      C^a*B^δ*(∑' n : ℕ, ENNReal.ofReal (Real.exp ((t*a-s*δ)*n))) := by
  have he : (fun ω => X ω^a) =ᵐ[μ] (⋃ n, S n).indicator (fun ω => X ω^a) := by
    filter_upwards [hcover] with ω hω
    exact (Set.indicator_of_mem (Set.mem_iUnion.mpr hω) (fun ω => X ω^a)).symm
  calc
    _ = ∫⁻ ω in ⋃ n, S n, X ω^a ∂μ := by
      rw [lintegral_congr_ae he,lintegral_indicator (MeasurableSet.iUnion hS) (fun ω => X ω^a)]
    _ ≤ ∑' n : ℕ, ∫⁻ ω in S n, X ω^a ∂μ := lintegral_iUnion_le S _
    _ ≤ ∑' n : ℕ, C^a*B^δ*ENNReal.ofReal (Real.exp ((t*a-s*δ)*n)) :=
      ENNReal.tsum_le_tsum fun n => fractional_height_slice_bound μ (S n) X hX C B t s n
        (hfirst n) (hprob n) ha ha1 hδ hδa
    _ = _ := ENNReal.tsum_mul_left

lemma fractional_height_geometric_sum_lt_top {t s a δ : ℝ} (hgap : t*a < s*δ) :
    (∑' n : ℕ, ENNReal.ofReal (Real.exp ((t*a-s*δ)*n))) < ⊤ := by
  have hh := Real.summable_exp_nat_mul_iff.mpr (sub_neg.mpr hgap)
  convert hh.tsum_ofReal_lt_top using 1
  congr 1
  funext n
  congr 1
  congr 1
  ring

end Percolation.BenjaminiSchramm

end

end OAI
