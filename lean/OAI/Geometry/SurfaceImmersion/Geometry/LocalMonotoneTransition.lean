import OAI.Geometry.SurfaceImmersion.Geometry.MonotoneGermDiffeomorphism

namespace OAI

/-! A smooth oriented transition on an open real interval extends to a
global smooth change of parameter while retaining its germ. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem local_increasing_diffeomorphism {h : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) {a : ℝ}
    (haU : a ∈ U) (ha : 0 < deriv h a) :
    ∃ e : ℝ ≃ₜ ℝ, ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      StrictMono e ∧ e =ᶠ[𝓝 a] h := by
  obtain ⟨W,hW,haW,hWU,H,hH,heq⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := a)) hU (singleton_subset_iff.mpr haU) hh
  have he : H =ᶠ[𝓝 a] h := heq.eventuallyEq_of_mem (hW.mem_nhds (haW (by simp)))
  have hd : 0 < deriv H a := by rw [he.deriv_eq]; exact ha
  obtain ⟨e,hes,hei,hem,hee⟩ := increasing_smooth_germ_diffeomorphism hH a hd
  exact ⟨e,hes,hei,hem,hee.trans he⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
