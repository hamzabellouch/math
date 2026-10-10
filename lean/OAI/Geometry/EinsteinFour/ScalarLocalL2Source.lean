import OAI.Geometry.EinsteinFour.ScalarPoissonKernelLocalTests

namespace OAI

/-! Compact-test forcing with an L2 localization gives a genuine order-zero
Sobolev source, without requiring a smooth right-hand side. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)

theorem scalar_localize_memSobolev_zero_of_L2_source (U : Set V)
    (u : T) (f : V → ℂ)
    (htest : ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ U → u φ = ∫ x, φ x * f x)
    (ψ : S) (hc : HasCompactSupport (ψ : V → ℂ))
    (hs : tsupport (ψ : V → ℂ) ⊆ U)
    (hmem : MemLp (fun x => ψ x * f x) 2 (volume : Measure V)) :
    MemSobolev 0 2 (smulLeftCLM ℂ ψ u) := by
  let F : Lp ℂ 2 (volume : Measure V) := hmem.toLp (fun x => ψ x * f x)
  apply memSobolev_zero_iff.mpr
  refine ⟨F, ?_⟩
  ext φ
  change u (SchwartzMap.smulLeftCLM ℂ ψ φ) = _
  have hcompact : HasCompactSupport (SchwartzMap.smulLeftCLM ℂ ψ φ : V → ℂ) := by
    rw [SchwartzMap.smulLeftCLM_apply ψ.hasTemperateGrowth]
    exact hc.smul_right
  have hsupport : tsupport (SchwartzMap.smulLeftCLM ℂ ψ φ : V → ℂ) ⊆ U := by
    intro x hx
    exact hs ((SchwartzMap.tsupport_smulLeftCLM_subset (ψ : V → ℂ) φ hx).2)
  rw [htest _ hcompact hsupport, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hmem.coeFn_toLp] with x hx
  change (SchwartzMap.smulLeftCLM ℂ ψ φ) x * f x = φ x * F x
  rw [SchwartzMap.smulLeftCLM_apply_apply ψ.hasTemperateGrowth, hx]
  simp only [smul_eq_mul]
  ring

end
end PositiveEinsteinFour.Geometry

end OAI
