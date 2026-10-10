import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RegularizedSlowSolution
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace OAI

/-! # Removal of the singularity at the regularized integral's lower endpoint -/

open MeasureTheory Filter Topology Asymptotics

namespace DefocusingNLS

theorem regularizedSlowKernel_norm_le (q : ℂ) (m : ℕ) (x : ℂ)
    {u C : ℝ} (hu : 0 < u)
    (hb : ‖regularizingBracket ((m : ℂ) - 1 - q) x u‖ ≤ C * u) :
    ‖regularizedSlowKernel q m x u‖ ≤ C * u ^ q.re := by
  have hexp : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpow : u ^ (q.re - 1) * u = u ^ q.re := by
    calc
      u ^ (q.re - 1) * u = u ^ (q.re - 1) * u ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = u ^ (q.re - 1 + 1) := (Real.rpow_add hu _ _).symm
      _ = u ^ q.re := by congr 1; ring
  calc
    ‖regularizedSlowKernel q m x u‖ = Real.exp (-u) * u ^ (q.re - 1) *
        ‖regularizingBracket ((m : ℂ) - 1 - q) x u‖ := by
      simp only [regularizedSlowKernel, norm_mul, Complex.norm_exp, Complex.neg_re,
        Complex.ofReal_re, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.sub_re,
        Complex.one_re]
    _ ≤ 1 * u ^ (q.re - 1) * (C * u) := by gcongr
    _ = C * (u ^ (q.re - 1) * u) := by ring
    _ = C * u ^ q.re := by rw [hpow]

/-- The regularized kernel is no worse than `u ^ Re(q)` at zero. -/
theorem regularizedSlowKernel_isBigO_zero (q : ℂ) (m : ℕ) (x : ℂ) :
    regularizedSlowKernel q m x =O[𝓝[>] (0 : ℝ)] (fun u : ℝ => u ^ q.re) := by
  obtain ⟨C, _, hC⟩ :=
    (regularizingBracket_isBigO ((m : ℂ) - 1 - q) x).exists_pos
  have ht : Tendsto (fun u : ℝ => (u : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hb := ht.eventually hC.bound
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [hb, self_mem_nhdsWithin] with u hb hu
  have hu' : 0 < u := hu
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu'] at hb
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu'.le _)] using
    regularizedSlowKernel_norm_le q m x hu' hb

theorem measurable_regularizedSlowKernel (q : ℂ) (m : ℕ) (x : ℂ) :
    Measurable (regularizedSlowKernel q m x) := by
  have hpow (r : ℂ) : Measurable (fun z : ℂ => z ^ r) := by
    simp only [Complex.cpow_def]
    exact Measurable.ite (measurableSet_singleton 0) measurable_const
      (Complex.measurable_exp.comp (Complex.measurable_log.mul_const r))
  have hbase : Measurable (fun u : ℝ => 1 + (u : ℂ) / x) := by fun_prop
  exact ((Complex.measurable_exp.comp Complex.measurable_ofReal.neg).mul
    ((hpow (q - 1)).comp Complex.measurable_ofReal)).mul
    (((hpow ((m : ℂ) - 1 - q)).comp hbase).sub measurable_const)

/-- The lower endpoint is integrable throughout the half-plane required
by the matching calculation. -/
theorem regularizedSlowKernel_integrableAt_zero (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) :
    IntegrableAtFilter (regularizedSlowKernel q m x) (𝓝[>] (0 : ℝ)) := by
  apply (regularizedSlowKernel_isBigO_zero q m x).integrableAtFilter
  · exact ⟨Set.univ, univ_mem, (measurable_regularizedSlowKernel q m x).aestronglyMeasurable.restrict⟩
  · refine ⟨Set.Ioo 0 1, Ioo_mem_nhdsGT (by norm_num), ?_⟩
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mpr hq

end DefocusingNLS

end OAI
