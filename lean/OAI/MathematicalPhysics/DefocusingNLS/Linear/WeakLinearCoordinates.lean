import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! # Linear coordinates of a weak limit -/

open Filter Topology

namespace DefocusingNLS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem weakLimit_map_eq_zero (A : E →L[ℝ] F) (u : ℕ → E) (v : E)
    (hweak : ∀ ℓ : E →L[ℝ] ℂ, Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ v)))
    (hz : ∀ n, A (u n) = 0) : A v = 0 := by
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
  intro ℓ
  have h := hweak (Complex.ofRealCLM.comp (ℓ.comp A))
  have he : (fun n => (Complex.ofRealCLM.comp (ℓ.comp A)) (u n)) = fun _ => 0 := by
    funext n
    simp only [ContinuousLinearMap.comp_apply, hz n, map_zero]
  rw [he] at h
  have hv := tendsto_nhds_unique tendsto_const_nhds h
  have hreal := congrArg Complex.re hv
  simpa only [Complex.zero_re, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    Complex.ofReal_re] using hreal.symm

theorem tendsto_finite_coordinates_of_weak [FiniteDimensional ℝ F]
    (A : E →L[ℝ] F) (u : ℕ → E) (v : E)
    (hweak : ∀ ℓ : E →L[ℝ] ℂ, Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ v))) :
    Tendsto (fun n => A (u n)) atTop (𝓝 (A v)) := by
  let e := (Module.finBasis ℝ F).equivFunL
  have hc : Tendsto (fun n => e (A (u n))) atTop (𝓝 (e (A v))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    let d : E →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp (e.toContinuousLinearMap.comp A)
    have h := (Complex.continuous_re.tendsto _).comp (hweak (Complex.ofRealCLM.comp d))
    change Tendsto (fun n => Complex.re ((Complex.ofRealCLM.comp d) (u n))) atTop
      (𝓝 (Complex.re ((Complex.ofRealCLM.comp d) v))) at h
    simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
      Complex.ofReal_re, d, ContinuousLinearMap.proj_apply, ContinuousLinearEquiv.coe_coe] using h
  have h := e.symm.continuous.continuousAt.tendsto.comp hc
  change Tendsto (fun n => e.symm (e (A (u n)))) atTop (𝓝 (e.symm (e (A v)))) at h
  simpa only [e.symm_apply_apply] using h

end DefocusingNLS

end OAI
