import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Shells.FourierNormSqContinuous

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CriticalFourierSupport
namespace CurrentFalconer
open MeasureTheory Set
open scoped ENNReal

theorem lintegral_biUnion_finset_le {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ≥0∞) (I : Finset ι) (s : ι → Set α) :
    (∫⁻ x in ⋃ i ∈ I, s i, f x ∂μ) ≤ ∑ i ∈ I, ∫⁻ x in s i, f x ∂μ := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, Finset.sum_insert hi]
    exact (lintegral_union_le f (s i) (⋃ i ∈ I, s i)).trans (add_le_add le_rfl ih)

theorem dyadic_scalar_cover {H : ℝ} {n : ℕ} (hH : H < (2 : ℝ)^(n+1)) :
    Set.Icc (-H) H ⊆ Set.Icc (-1) 1 ∪
      ⋃ j ∈ Finset.range (n+1), annularScalarSet ((2 : ℝ)^j) H := by
  intro s hs
  have hsH : |s| ≤ H := abs_le.mpr ⟨hs.1, hs.2⟩
  by_cases hs1 : |s| ≤ 1
  · exact Or.inl (abs_le.mp hs1)
  · right
    obtain ⟨j,hj,hsj⟩ := exists_nat_pow_near (le_of_lt (lt_of_not_ge hs1))
      (by norm_num : (1 : ℝ) < 2)
    have hjn : j < n+1 :=
      (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (hj.trans_lt (hsH.trans_lt hH))
    refine mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨Finset.mem_range.mpr hjn,?_⟩⟩
    exact ⟨hj, le_min (by simpa only [pow_succ, mul_comm] using hsj.le) hsH⟩

section AngularEnergySum
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def angularFourierEnergy (μ ξ : Measure V) (s : ℝ) : ℝ :=
  ∫ w : V, ‖PlanarFalconer.sourceFourier μ (s • w)‖^2 ∂ξ

omit [FiniteDimensional ℝ V] [BorelSpace V] in
theorem angularFourierEnergy_nonneg (μ ξ : Measure V) (s : ℝ) :
    0 ≤ angularFourierEnergy μ ξ s := integral_nonneg (fun _ => sq_nonneg _)

theorem angularFourierEnergy_le_one (μ ξ : Measure V) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ξ] (hmass : ξ Set.univ ≤ 1) (s : ℝ) :
    angularFourierEnergy μ ξ s ≤ 1 := by
  have hb (w : V) : ‖PlanarFalconer.sourceFourier μ (s • w)‖^2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (sourceFourier_norm_le_one μ (s • w)) 2
  have hi : Integrable (fun w : V => ‖PlanarFalconer.sourceFourier μ (s • w)‖^2) ξ := by
    apply (integrable_const (1 : ℝ)).mono' _ (ae_of_all ξ (fun w => ?_))
    · exact ((sourceFourier_norm_sq_continuous μ).comp (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hb w
  have hh := integral_mono hi (integrable_const (1 : ℝ)) hb
  have hm : ξ.real Set.univ ≤ 1 := by
    simpa only [measureReal_def, ENNReal.toReal_one] using
      ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) hmass
  simp only [integral_const, smul_eq_mul, mul_one] at hh
  exact hh.trans hm

theorem angularFourierEnergy_continuous (μ ξ : Measure V) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ξ] : Continuous (angularFourierEnergy μ ξ) := by
  have hc := sourceFourier_norm_sq_continuous μ
  apply continuous_of_dominated (bound := fun _ : V => (1 : ℝ))
  · intro s
    exact (hc.comp (by fun_prop)).aestronglyMeasurable
  · intro s
    filter_upwards with w
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
      (sourceFourier_norm_le_one μ (s • w)) 2
  · exact integrable_const _
  · filter_upwards with w
    exact hc.comp (by fun_prop)

end AngularEnergySum
end CurrentFalconer
end CriticalFourierSupport
end
end

end OAI
