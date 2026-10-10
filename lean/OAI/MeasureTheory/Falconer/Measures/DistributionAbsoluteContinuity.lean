import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped ENNReal

 theorem locallyIntegrable_rnDeriv_smul (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    (hac : μ ≪ ν) (f : ℝ → ℂ) (hf : LocallyIntegrable f μ) :
    LocallyIntegrable (fun x => (μ.rnDeriv ν x).toReal • f x) ν := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hi := (integrable_rnDeriv_smul_iff hac).mpr
    ((hf.integrableOn_isCompact hK).integrable_indicator hK.measurableSet)
  apply (integrable_indicator_iff hK.measurableSet).mp
  apply hi.congr
  filter_upwards with x
  by_cases hx : x ∈ K <;> simp [hx]

 theorem absolutelyContinuous_of_smooth_test_density (τ : Measure ℝ) [IsFiniteMeasure τ]
    (f : ℝ → ℂ) (hf : LocallyIntegrable f volume)
    (ht : ∀ (g : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      (∫ x, (g x : ℂ) ∂τ) = ∫ x, g x • f x) : τ ≪ volume := by
  let μ : Measure ℝ := τ+volume
  have hτ : τ ≪ μ := Measure.absolutelyContinuous_of_le (by
    apply Measure.le_iff.mpr
    intro s _
    exact le_add_right le_rfl)
  have hv : volume ≪ μ := Measure.absolutelyContinuous_of_le (by
    apply Measure.le_iff.mpr
    intro s _
    exact le_add_left le_rfl)
  let a : ℝ → ℂ := fun x => ((τ.rnDeriv μ x).toReal : ℂ)
  let b : ℝ → ℂ := fun x => (volume.rnDeriv μ x).toReal • f x
  have ha : LocallyIntegrable a μ := by
    simpa only [smul_eq_mul, Complex.real_smul, mul_one] using
      locallyIntegrable_rnDeriv_smul τ μ hτ (fun _ => (1:ℂ))
        (continuous_const.locallyIntegrable)
  have hb : LocallyIntegrable b μ := locallyIntegrable_rnDeriv_smul volume μ hv f hf
  have hab : a =ᵐ[μ] b := by
    apply ae_eq_of_integral_contDiff_smul_eq ha hb
    intro g hg hc
    calc
      _ = ∫ x, (τ.rnDeriv μ x).toReal • (g x : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp [a, Complex.real_smul, mul_comm]
      _ = ∫ x, (g x : ℂ) ∂τ := integral_rnDeriv_smul hτ
      _ = ∫ x, g x • f x := ht g hg hc
      _ = ∫ x, (volume.rnDeriv μ x).toReal • (g x • f x) ∂μ :=
        (integral_rnDeriv_smul hv).symm
      _ = _ := by simp only [b, smul_comm (g _) ((volume.rnDeriv μ _).toReal)]
  intro S hS
  have hS' : ∀ᵐ x ∂volume, x ∉ S := by simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hS
  rw [← Measure.withDensity_rnDeriv_eq volume μ hv] at hS'
  have hz := (ae_withDensity_iff (Measure.measurable_rnDeriv volume μ)).mp hS'
  have hgoal : ∀ᵐ x ∂τ, x ∉ S := by
    rw [← Measure.withDensity_rnDeriv_eq τ μ hτ]
    apply (ae_withDensity_iff (Measure.measurable_rnDeriv τ μ)).mpr
    filter_upwards [hz,hab,Measure.rnDeriv_lt_top τ μ] with x hx he hfin
    intro hax hxS
    have hzero : volume.rnDeriv μ x = 0 := by
      by_contra hn
      exact hx hn hxS
    have hzreal : (τ.rnDeriv μ x).toReal = 0 := by
      have he' : ((τ.rnDeriv μ x).toReal : ℂ) = 0 := by
        simpa only [a,b,hzero,ENNReal.toReal_zero,zero_smul] using he
      exact Complex.ofReal_eq_zero.mp he'
    have heq := ENNReal.ofReal_toReal hfin.ne
    rw [hzreal, ENNReal.ofReal_zero] at heq
    exact hax heq.symm
  simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hgoal

end PlanarFalconer

end OAI
