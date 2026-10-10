import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWindowMultiplier

namespace OAI

/-! Plancherel for the actual finite logarithmic windows. The coefficient
function is arbitrary; multiplicativity plays no role in this bridge. -/

namespace TwoPointCorrelations

open Complex MeasureTheory FourierTransform Finset

lemma mrt_fourier_finsetSum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ S, Integrable (f i)) (t : ℝ) :
    𝓕 (fun x => ∑ i ∈ S, f i x) t = ∑ i ∈ S, 𝓕 (f i) t := by
  simp only [Real.fourier_eq, smul_sum]
  apply integral_finsetSum
  intro i hi
  exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
    (show Continuous (fun p : ℝ × ℝ => (innerₗ ℝ p.1) p.2) from continuous_inner) t).mpr
      (hf i hi)

lemma mrt_fourier_const_mul (c : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    𝓕 (fun x => c * f x) t = c * 𝓕 f t := by
  simpa only [Pi.smul_apply, smul_eq_mul] using! congrFun
    (VectorFourier.fourierIntegral_const_smul Real.fourierChar volume (innerₗ ℝ) f c) t

noncomputable def mrtLogDirichlet (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, a n * Complex.exp (-((1 : ℂ) + (t : ℂ) * I) * Real.log (n : ℝ))

lemma mrt_log_window_integrable (S : Finset ℕ) (a : ℕ → ℂ) (v : ℝ) :
    Integrable (mrtLogWindow S a v) :=
  integrable_finsetSum S (fun n _ =>
    (mrtLogWindowAtom_integrable (Real.log (n : ℝ)) v).const_mul (a n))

lemma mrt_log_window_memLp (S : Finset ℕ) (a : ℕ → ℂ) (v : ℝ) :
    MemLp (mrtLogWindow S a v) 2 :=
  memLp_finsetSum S (fun n _ =>
    (mrtLogWindowAtom_memLp (Real.log (n : ℝ)) v 2).const_mul (a n))

theorem mrt_log_window_transform (S : Finset ℕ) (a : ℕ → ℂ)
    {v : ℝ} (hv : 0 ≤ v) (t : ℝ) :
    𝓕 (mrtLogWindow S a v) t =
      mrtWindowMultiplier v (2 * Real.pi * t) * mrtLogDirichlet S a (2 * Real.pi * t) := by
  change 𝓕 (fun y => ∑ n ∈ S, a n * mrtLogWindowAtom (Real.log (n : ℝ)) v y) t = _
  rw [mrt_fourier_finsetSum S _ (fun n _ =>
    (mrtLogWindowAtom_integrable (Real.log (n : ℝ)) v).const_mul (a n))]
  simp only [mrt_fourier_const_mul, mrt_log_window_fourier _ hv,
    mrtLogDirichlet, mul_sum]
  apply sum_congr rfl
  intro n _
  ring

lemma mrt_log_window_fourier_memLp (S : Finset ℕ) (a : ℕ → ℂ)
    {v : ℝ} (hv : 0 ≤ v) : MemLp (𝓕 (mrtLogWindow S a v)) 2 := by
  have hh := memLp_finsetSum S (fun n _ =>
    (mrt_log_window_atom_fourier_memLp (Real.log (n : ℝ)) hv).const_mul (a n))
  convert hh using 1
  ext t
  change 𝓕 (fun y => ∑ n ∈ S, a n * mrtLogWindowAtom (Real.log (n : ℝ)) v y) t = _
  rw [mrt_fourier_finsetSum S _ (fun n _ =>
    (mrtLogWindowAtom_integrable (Real.log (n : ℝ)) v).const_mul (a n))]
  simp only [mrt_fourier_const_mul]

theorem mrt_log_window_plancherel (S : Finset ℕ) (a : ℕ → ℂ)
    {v : ℝ} (hv : 0 ≤ v) :
    (∫ y : ℝ, ‖mrtLogWindow S a v y‖ ^ 2) =
      ∫ t : ℝ, ‖mrtWindowMultiplier v (2 * Real.pi * t) *
        mrtLogDirichlet S a (2 * Real.pi * t)‖ ^ 2 := by
  have hh := (mrt_plancherel (mrt_log_window_integrable S a v)
    (mrt_log_window_memLp S a v) (mrt_log_window_fourier_memLp S a hv)).symm
  simpa only [mrt_log_window_transform S a hv] using hh

end TwoPointCorrelations

end OAI
