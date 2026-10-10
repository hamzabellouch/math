import OAI.Analysis.IrrationalRotation.Model.Spectral

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233

section Spectrum

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem spectralRadius_eq_zero_of_normRoot_tendsto {a : A}
    (h : Tendsto (fun n : ℕ => ‖a ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0)) :
    spectralRadius ℂ a = 0 := by
  have h' : Tendsto (fun n : ℕ => ENNReal.ofReal (‖a ^ n‖ ^ (1 / (n : ℝ))))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp h
  exact tendsto_nhds_unique (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a) h'

theorem spectrum_eq_singleton_zero_of_normRoot_tendsto [Nontrivial A] {a : A}
    (h : Tendsto (fun n : ℕ => ‖a ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0)) :
    spectrum ℂ a = {0} := by
  have hr := spectralRadius_eq_zero_of_normRoot_tendsto h
  have hz : ∀ z ∈ spectrum ℂ a, z = 0 := by
    intro z hz
    have hnorm : (‖z‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ a := by
      rw [spectralRadius_eq_of_unital]
      exact le_iSup_of_le z (le_iSup_of_le hz le_rfl)
    rw [hr] at hnorm
    have hn : ‖z‖₊ = 0 := by exact_mod_cast le_antisymm hnorm bot_le
    exact nnnorm_eq_zero.mp hn
  apply Set.Subset.antisymm
  · intro z hz'
    simpa using hz z hz'
  · obtain ⟨z, hz'⟩ := spectrum.nonempty a
    simpa [hz z hz'] using hz'

end Spectrum

theorem exp_half_log_eq_sqrt {t : ℝ} (ht : 0 < t) :
    Real.exp (Real.log t / 2) = Real.sqrt t := by
  rw [← Real.log_sqrt ht.le, Real.exp_log (Real.sqrt_pos.mpr ht)]

theorem iInf_sqrt_sq_add_pos (c : ℝ) (hc : 0 ≤ c) :
    (⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal (Real.sqrt (c ^ 2 + ε.val))) =
      ENNReal.ofReal c := by
  apply le_antisymm
  · have hlim : Tendsto
        (fun n : ℕ => ENNReal.ofReal (Real.sqrt (c ^ 2 + 1 / ((n : ℝ) + 1))))
        atTop (𝓝 (ENNReal.ofReal c)) := by
      have hreal : Tendsto (fun n : ℕ => c ^ 2 + 1 / ((n : ℝ) + 1))
          atTop (𝓝 (c ^ 2)) := by
        simpa using tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [Function.comp_def, Real.sqrt_sq hc] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (Real.continuous_sqrt.continuousAt.tendsto.comp hreal)
    apply ge_of_tendsto' hlim
    intro n
    exact iInf_le (fun ε : {r : ℝ // 0 < r} =>
      ENNReal.ofReal (Real.sqrt (c ^ 2 + ε.val))) ⟨1 / ((n : ℝ) + 1), by positivity⟩
  · apply le_iInf
    intro ε
    apply ENNReal.ofReal_le_ofReal
    calc
      c = Real.sqrt (c ^ 2) := (Real.sqrt_sq hc).symm
      _ ≤ Real.sqrt (c ^ 2 + ε.val) := Real.sqrt_le_sqrt (by linarith [ε.property])

theorem logarithmicPotentialDeterminant_dirac (w z : ℂ) :
    logarithmicPotentialDeterminant (Measure.dirac w) z = ENNReal.ofReal ‖w - z‖ := by
  simp only [logarithmicPotentialDeterminant, integral_dirac]
  have h : ∀ ε : {r : ℝ // 0 < r},
      Real.exp (Real.log (‖w - z‖ ^ 2 + ε.val) / 2) =
        Real.sqrt (‖w - z‖ ^ 2 + ε.val) := by
    intro ε
    exact exp_half_log_eq_sqrt (by nlinarith [ε.property, sq_nonneg ‖w - z‖])
  simp_rw [h]
  exact iInf_sqrt_sq_add_pos _ (norm_nonneg _)


variable {A : Type*} [CStarAlgebra A]

theorem TracialState.map_real (τ : TracialState A) (r : ℝ) :
    τ (algebraMap ℝ A r) = (r : ℂ) := by
  rw [Algebra.algebraMap_eq_smul_one,
    τ.toContinuousLinearMap.map_smul_of_tower, τ.map_one, Complex.real_smul, mul_one]

theorem fugledeKadisonDeterminant_zero (τ : TracialState A) :
    fugledeKadisonDeterminant τ 0 = 0 := by
  unfold fugledeKadisonDeterminant
  simp only [star_zero, zero_mul, zero_add, ← Algebra.algebraMap_eq_smul_one,
    CFC.log_algebraMap, TracialState.map_real, Complex.ofReal_re]
  have h : ∀ ε : {r : ℝ // 0 < r},
      Real.exp (Real.log ε.val / 2) = Real.sqrt ε.val :=
    fun ε => exp_half_log_eq_sqrt ε.property
  simp_rw [h]
  simpa using iInf_sqrt_sq_add_pos 0 le_rfl

theorem fugledeKadisonDeterminant_unitary_mul (τ : TracialState A)
    (u : unitary A) (a : A) :
    fugledeKadisonDeterminant τ ((u : A) * a) = fugledeKadisonDeterminant τ a := by
  have h : star ((u : A) * a) * ((u : A) * a) = star a * a := by
    rw [star_mul, mul_assoc, ← mul_assoc (star (u : A)), Unitary.star_mul_self_of_mem u.property]
    simp
  simp only [fugledeKadisonDeterminant, h]


end Invariant233

end

end OAI
