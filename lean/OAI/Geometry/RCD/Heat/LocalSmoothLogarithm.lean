import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-! # A bounded C² logarithm on a prescribed positive interval

Only the first two derivatives are used in the local weak-Laplacian
chain rule. The function and its derivative vanish at zero.
-/

open Set Filter Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem exists_local_smooth_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ (φ ψ χ : ℝ → ℝ) (C D B E : ℝ≥0),
      LipschitzWith C φ ∧ LipschitzWith D ψ ∧ Continuous χ ∧
      φ 0=0 ∧ ψ 0=0 ∧
      (∀ x, HasDerivAt φ (ψ x) x) ∧ (∀ x, HasDerivAt ψ (χ x) x) ∧
      (∀ x, |ψ x| ≤ B) ∧ (∀ x, |χ x| ≤ E) ∧
      ∀ x ∈ Icc a b, φ x=Real.log x ∧ ψ x=x⁻¹ ∧ χ x=-(x^2)⁻¹ := by
  let c := b+1
  let κ : ContDiffBump c := ⟨c-a/2,c-a/4,by dsimp [c]; linarith,by linarith⟩
  let f := fun x => κ x*Real.log x
  have hcz : κ.rOut < dist (0 : ℝ) c := by
    change c-a/4 < |0-c|
    rw [zero_sub,abs_neg,abs_of_pos (show 0 < c by dsimp [c]; linarith)]
    linarith
  have hκ0 : (κ : ℝ → ℝ) =ᶠ[𝓝 0] 0 := by
    have hn := (isOpen_lt continuous_const (continuous_id.dist continuous_const)).mem_nhds hcz
    filter_upwards [hn] with x hx
    exact κ.zero_of_le_dist hx.le
  have hf0 : f =ᶠ[𝓝 0] (fun _ => 0) := hκ0.mono fun x hx => by
    change κ x*Real.log x=0
    simp only [hx,Pi.zero_apply,zero_mul]
  have hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x=0
    · subst x
      exact contDiffAt_const.congr_of_eventuallyEq hf0
    · exact κ.contDiff.contDiffAt.mul (Real.contDiffAt_log.mpr hx)
  have hfs : HasCompactSupport f := κ.hasCompactSupport.mul_right
  have hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv (deriv f)) := (contDiff_infty_iff_deriv.mp hψ).2
  obtain ⟨B,hB⟩ := hfs.deriv.exists_bound_of_continuous hψ.continuous
  obtain ⟨E,hE⟩ := hfs.deriv.deriv.exists_bound_of_continuous hχ.continuous
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hE0 : 0 ≤ E := (norm_nonneg _).trans (hE 0)
  let Bn : ℝ≥0 := ⟨B,hB0⟩
  let En : ℝ≥0 := ⟨E,hE0⟩
  have hl : LipschitzWith Bn f := lipschitzWith_of_nnnorm_deriv_le
    (hf.differentiable (by simp)) (fun x => NNReal.coe_le_coe.mp (hB x))
  have hlψ : LipschitzWith En (deriv f) := lipschitzWith_of_nnnorm_deriv_le
    (hψ.differentiable (by simp)) (fun x => NNReal.coe_le_coe.mp (hE x))
  refine ⟨f,deriv f,deriv (deriv f),Bn,En,Bn,En,hl,hlψ,hχ.continuous,
    hf0.eq_of_nhds,?_,?_,?_,?_,?_,?_⟩
  · simpa only [deriv_const] using hf0.deriv_eq
  · intro x; exact (hf.differentiable (by simp) x).hasDerivAt
  · intro x; exact (hψ.differentiable (by simp) x).hasDerivAt
  · exact hB
  · exact hE
  · intro x hx
    have hxin : x ∈ ball c κ.rIn := by
      change |x-c| < c-a/2
      rw [abs_of_nonpos (show x-c ≤ 0 by dsimp [c]; linarith [hx.2])]
      linarith [hx.1]
    have he : f =ᶠ[𝓝 x] Real.log := (κ.eventuallyEq_one_of_mem_ball hxin).mono fun y hy => by
      change κ y*Real.log y=Real.log y
      simp only [hy,Pi.one_apply,one_mul]
    refine ⟨he.eq_of_nhds,?_,?_⟩
    · rw [he.deriv_eq,Real.deriv_log]
    · rw [he.deriv.deriv_eq,Real.deriv_log',deriv_inv]

end RegularPointCoordinates

end

end OAI
