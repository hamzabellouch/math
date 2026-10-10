import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic

namespace OAI

namespace Ostmann

open MeasureTheory Set Filter Asymptotics
open scoped Topology SchwartzMap

theorem schwartz_isBigO_rpow_atTop (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) :
    (ρ : ℝ → ℂ) =O[atTop] (fun x : ℝ => x ^ a) := by
  have h := (ρ.isBigO_cocompact_rpow a).mono (atTop_le_cocompact (α := ℝ))
  apply h.congr' Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp [Real.norm_eq_abs, abs_of_nonneg hx]

theorem schwartz_isBigO_one_zero (ρ : 𝓢(ℝ, ℂ)) :
    (ρ : ℝ → ℂ) =O[𝓝[>] 0] (fun _ : ℝ => (1 : ℝ)) :=
  ρ.continuous.continuousAt.isBigO.mono nhdsWithin_le_nhds

theorem schwartz_mellin_convergent (ρ : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (ρ : ℝ → ℂ) s := by
  apply mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := 0)
  · exact (ρ.continuous.locallyIntegrable (μ := volume)).locallyIntegrableOn _
  · exact schwartz_isBigO_rpow_atTop ρ _
  · linarith
  · simpa using schwartz_isBigO_one_zero ρ
  · exact hs

theorem schwartz_mellin_differentiableAt (ρ : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (ρ : ℝ → ℂ)) s := by
  apply mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0)
  · exact (ρ.continuous.locallyIntegrable (μ := volume)).locallyIntegrableOn _
  · exact schwartz_isBigO_rpow_atTop ρ _
  · linarith
  · simpa using schwartz_isBigO_one_zero ρ
  · exact hs

end Ostmann

end OAI
