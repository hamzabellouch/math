import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicWeakLaplacian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

namespace OAI

/-! # Every annular test is a smooth test of the squared radius

The scalar test vanishes near zero, so its square-root pullback is smooth
on the whole line. This removes the squared-radius restriction in the
Cartesian-to-radial weak Laplacian identity.
-/

open Set Filter Topology
open scoped ContDiff SchwartzMap

namespace DefocusingNLS

noncomputable def radialSquarePullback (φ : 𝓢(ℝ, ℂ)) (s : ℝ) : ℂ :=
  φ (Real.sqrt s)

theorem radialSquarePullback_contDiff (φ : 𝓢(ℝ, ℂ))
    (hs : tsupport φ ⊆ Ioi (0 : ℝ)) :
    ContDiff ℝ ∞ (radialSquarePullback φ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro s
  by_cases hz : s = 0
  · subst s
    have hzero : (0 : ℝ) ∉ tsupport φ := fun h => (lt_irrefl 0) (Set.mem_Ioi.mp (hs h))
    have he : radialSquarePullback φ =ᶠ[𝓝 0] (fun _ => (0 : ℂ)) := by
      have ht := notMem_tsupport_iff_eventuallyEq.mp hzero
      have hsqrt : Tendsto Real.sqrt (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa only [Real.sqrt_zero] using Real.continuous_sqrt.tendsto (0 : ℝ)
      exact ht.comp_tendsto hsqrt
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (φ.smooth ⊤).contDiffAt.comp s (Real.contDiffAt_sqrt hz)

theorem tsupport_radialSquarePullback (φ : 𝓢(ℝ, ℂ))
    (hs : tsupport φ ⊆ Ioi (0 : ℝ)) :
    tsupport (radialSquarePullback φ) ⊆ Ioi (0 : ℝ) := by
  intro s hs'
  have hmem : Real.sqrt s ∈ tsupport φ :=
    tsupport_comp_subset_preimage φ Real.continuous_sqrt hs'
  exact Real.sqrt_pos.mp (hs hmem)

theorem radialSquarePullback_hasCompactSupport (φ : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi (0 : ℝ)) :
    HasCompactSupport (radialSquarePullback φ) := by
  obtain ⟨B, hB⟩ := hc.isBounded.exists_norm_le
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ℝ) ((max B 1) ^ 2))
  intro s hs'
  have hφ : Real.sqrt s ∈ Function.support φ := hs'
  have hpos : 0 < s := Real.sqrt_pos.mp (hs (subset_tsupport φ hφ))
  have hb : Real.sqrt s ≤ max B 1 := by
    have := hB (Real.sqrt s) (subset_tsupport φ hφ)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s)] using
      this.trans (le_max_left B 1)
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg s) hb 2
  rw [Real.sq_sqrt hpos.le] at hsq
  simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
    abs_of_pos hpos] using hsq

noncomputable def radialSquareSchwartz (φ : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi (0 : ℝ)) : 𝓢(ℝ, ℂ) :=
  (radialSquarePullback_hasCompactSupport φ hc hs).toSchwartzMap
    (radialSquarePullback_contDiff φ hs)

@[simp] theorem radialSquareSchwartz_apply (φ : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi (0 : ℝ)) (s : ℝ) :
    radialSquareSchwartz φ hc hs s = φ (Real.sqrt s) := rfl

theorem radialSquareSchwartz_square (φ : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi (0 : ℝ))
    (r : ℝ) (hr : 0 < r) : radialSquareSchwartz φ hc hs (r ^ 2) = φ r := by
  simp only [radialSquareSchwartz_apply, Real.sqrt_sq hr.le]

/-- Exact derivative conversion, without dividing at the origin. -/
theorem radialSquareSchwartz_derivatives (φ : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi (0 : ℝ))
    (r : ℝ) (hr : 0 < r) :
    deriv φ r = ((2 * r : ℝ) : ℂ) * deriv (radialSquareSchwartz φ hc hs) (r ^ 2) ∧
    deriv (deriv φ) r = ((4 * r ^ 2 : ℝ) : ℂ) *
      deriv (deriv (radialSquareSchwartz φ hc hs)) (r ^ 2) +
        2 * deriv (radialSquareSchwartz φ hc hs) (r ^ 2) := by
  let ψ := radialSquareSchwartz φ hc hs
  have hq : ContDiffAt ℝ 2 ψ (r ^ 2) := (ψ.smooth 2).contDiffAt
  have he : (fun s : ℝ => ψ (s ^ 2)) =ᶠ[𝓝 r] φ := by
    filter_upwards [Ioi_mem_nhds hr] with s hs'
    exact radialSquareSchwartz_square φ hc hs s hs'
  constructor
  · rw [← he.deriv_eq]
    have h := hq.differentiableAt (by norm_num) |>.hasDerivAt
    simpa [Function.comp_def, Complex.real_smul] using
      (h.scomp (h := fun s : ℝ => s ^ 2) r ((hasDerivAt_id r).pow 2)).deriv
  · have h := iteratedDeriv_scomp_two (g := ψ) (f := fun s : ℝ => s ^ 2)
      (x := r) hq (contDiffAt_id.pow 2)
    have hfirst : deriv (fun s : ℝ => s ^ 2) = fun s => 2 * s := by
      funext s
      simp
    have hsecond : deriv (deriv (fun s : ℝ => s ^ 2)) r = 2 := by
      rw [hfirst]
      simpa only [mul_one, id_eq] using ((hasDerivAt_id r).const_mul 2).deriv
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, Function.comp_def] at h
    rw [hsecond, hfirst] at h
    rw [← he.deriv.deriv_eq, h]
    simp only [Complex.real_smul]
    push_cast
    ring

theorem radialSquareSchwartz_laplacian_test (φ : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi (0 : ℝ))
    (lam : ℂ) (r : ℝ) (hr : 0 < r) :
    ((4 * r ^ 2 : ℝ) : ℂ) * deriv (deriv (radialSquareSchwartz φ hc hs)) (r ^ 2) +
      24 * deriv (radialSquareSchwartz φ hc hs) (r ^ 2) -
      lam / (r ^ 2 : ℝ) * radialSquareSchwartz φ hc hs (r ^ 2) =
    deriv (deriv φ) r + ((11 / r : ℝ) : ℂ) * deriv φ r -
      lam / (r ^ 2 : ℝ) * φ r := by
  obtain ⟨hfirst, hsecond⟩ := radialSquareSchwartz_derivatives φ hc hs r hr
  rw [radialSquareSchwartz_square φ hc hs r hr, hfirst, hsecond]
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  push_cast
  field_simp [hrC]
  ring

end DefocusingNLS

end OAI
