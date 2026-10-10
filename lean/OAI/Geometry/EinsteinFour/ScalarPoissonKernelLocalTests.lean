import OAI.Geometry.EinsteinFour.ScalarPoissonKernelMultiplier

namespace OAI

/-! Compact tests determine every inner localization of a distribution.
A source smooth only on the test domain becomes a Schwartz source after
localization, and therefore has all Sobolev orders. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Filter
open scoped SchwartzMap ENNReal Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "M" => smulLeftCLM ℂ

private theorem scalarSchwartz_cutoff_compact (ψ φ : S)
    (hc : HasCompactSupport (ψ : V → ℂ)) :
    HasCompactSupport (SchwartzMap.smulLeftCLM ℂ ψ φ : V → ℂ) := by
  rw [SchwartzMap.smulLeftCLM_apply ψ.hasTemperateGrowth]
  exact hc.smul_right

private theorem scalarSchwartz_cutoff_support (ψ φ : S) {U : Set V}
    (hs : tsupport (ψ : V → ℂ) ⊆ U) :
    tsupport (SchwartzMap.smulLeftCLM ℂ ψ φ : V → ℂ) ⊆ U := by
  intro x hx
  exact hs ((SchwartzMap.tsupport_smulLeftCLM_subset (ψ : V → ℂ) φ hx).2)

/-- Equality on compact tests in U gives equality after any compact
Schwartz cutoff supported in U. -/
theorem scalar_localize_eq_of_compact_tests (U : Set V) (u v : T)
    (htest : ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ U → u φ = v φ)
    (ψ : S) (hc : HasCompactSupport (ψ : V → ℂ))
    (hs : tsupport (ψ : V → ℂ) ⊆ U) :
    M ψ u = M ψ v := by
  ext φ
  exact htest (SchwartzMap.smulLeftCLM ℂ ψ φ)
    (scalarSchwartz_cutoff_compact ψ φ hc) (scalarSchwartz_cutoff_support ψ φ hs)

theorem scalar_localize_zero_of_compact_tests (U : Set V) (u : T)
    (htest : ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ U → u φ = 0)
    (ψ : S) (hc : HasCompactSupport (ψ : V → ℂ))
    (hs : tsupport (ψ : V → ℂ) ⊆ U) :
    M ψ u = 0 := by
  have h := scalar_localize_eq_of_compact_tests U u 0
    (fun φ hφ hsφ => by simpa using htest φ hφ hsφ) ψ hc hs
  simpa only [map_zero] using h

private theorem scalarLocalSource_smooth (ψ : S) (f : V → ℂ)
    (hf : ∀ x ∈ tsupport (ψ : V → ℂ), ContDiffAt ℝ (⊤ : ℕ∞) f x) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (ψ : V → ℂ)
  · exact (ψ.smooth ⊤).contDiffAt.mul (hf x hx)
  · have he : (fun y => ψ y * f y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [hy, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- A smooth source restricted by a compact Schwartz cutoff is Schwartz,
even if it has no regularity or growth control outside the cutoff. -/
def scalarLocalSourceSchwartz (ψ : S) (f : V → ℂ)
    (hc : HasCompactSupport (ψ : V → ℂ))
    (hf : ∀ x ∈ tsupport (ψ : V → ℂ), ContDiffAt ℝ (⊤ : ℕ∞) f x) : S :=
  hc.mul_right.toSchwartzMap (scalarLocalSource_smooth ψ f hf)

theorem scalarLocalSourceSchwartz_apply (ψ : S) (f : V → ℂ)
    (hc : HasCompactSupport (ψ : V → ℂ))
    (hf : ∀ x ∈ tsupport (ψ : V → ℂ), ContDiffAt ℝ (⊤ : ℕ∞) f x) (x : V) :
    scalarLocalSourceSchwartz ψ f hc hf x = ψ x * f x := rfl

/-- The actual compact-test equation identifies the localized source
with a constructed Schwartz function. -/
theorem scalar_localize_eq_smooth_source (U : Set V) (u : T) (f : V → ℂ)
    (hf : ∀ x ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) f x)
    (htest : ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ U → u φ = ∫ x, φ x * f x)
    (ψ : S) (hc : HasCompactSupport (ψ : V → ℂ))
    (hs : tsupport (ψ : V → ℂ) ⊆ U) :
    M ψ u = (scalarLocalSourceSchwartz ψ f hc (fun x hx => hf x (hs hx)) : T) := by
  ext φ
  change u (SchwartzMap.smulLeftCLM ℂ ψ φ) = _
  rw [htest _ (scalarSchwartz_cutoff_compact ψ φ hc)
    (scalarSchwartz_cutoff_support ψ φ hs), SchwartzMap.coe_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [SchwartzMap.smulLeftCLM_apply_apply ψ.hasTemperateGrowth,
    scalarLocalSourceSchwartz_apply, smul_eq_mul]
  ring

/-- A compact-test equation with a locally smooth source supplies all
orders of the inner localized forcing used by the elliptic bootstrap. -/
theorem scalar_localize_smooth_source_memSobolev (U : Set V) (u : T) (f : V → ℂ)
    (hf : ∀ x ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) f x)
    (htest : ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ U → u φ = ∫ x, φ x * f x)
    (ψ : S) (hc : HasCompactSupport (ψ : V → ℂ))
    (hs : tsupport (ψ : V → ℂ) ⊆ U) (s : ℝ) :
    MemSobolev s 2 (M ψ u) := by
  rw [scalar_localize_eq_smooth_source U u f hf htest ψ hc hs]
  exact SchwartzMap.memSobolev _

end
end PositiveEinsteinFour.Geometry

end OAI
