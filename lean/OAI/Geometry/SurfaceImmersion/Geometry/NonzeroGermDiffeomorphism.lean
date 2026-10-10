import OAI.Geometry.SurfaceImmersion.Geometry.LocalMonotoneTransition

namespace OAI

/-! A scalar smooth coordinate with nonzero derivative has a global smooth
homeomorphism representative of either orientation. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem nonzero_smooth_germ_diffeomorphism {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (a : ℝ) (ha : deriv h a ≠ 0) :
    ∃ e : ℝ ≃ₜ ℝ, ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      (StrictMono e ∨ StrictAnti e) ∧ e =ᶠ[𝓝 a] h := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hn : ContDiff ℝ ∞ (fun x => -h x) := hh.neg
    have hd : 0 < deriv (fun x => -h x) a := by
      rw [show (fun x => -h x) = -h from rfl, deriv.neg]
      exact neg_pos.mpr hneg
    obtain ⟨e,hes,hei,hem,he⟩ := increasing_smooth_germ_diffeomorphism hn a hd
    let E := e.trans (Homeomorph.neg ℝ)
    have hEs : ContDiff ℝ ∞ E := contDiff_neg.comp hes
    have hEi : ContDiff ℝ ∞ E.symm := hei.comp contDiff_neg
    have hEm : StrictAnti E := by
      intro x y hxy
      exact neg_lt_neg (hem hxy)
    refine ⟨E,hEs,hEi,Or.inr hEm,?_⟩
    filter_upwards [he] with x hx
    change -e x = h x
    rw [hx,neg_neg]
  · obtain ⟨e,hes,hei,hem,he⟩ := increasing_smooth_germ_diffeomorphism hh a hpos
    exact ⟨e,hes,hei,Or.inl hem,he⟩

theorem nonzero_local_germ_diffeomorphism {h : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) {a : ℝ}
    (haU : a ∈ U) (ha : deriv h a ≠ 0) :
    ∃ e : ℝ ≃ₜ ℝ, ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      (StrictMono e ∨ StrictAnti e) ∧ e =ᶠ[𝓝 a] h := by
  obtain ⟨W,hW,haW,_,H,hH,hEH⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := a)) hU (singleton_subset_iff.mpr haU) hh
  have he : H =ᶠ[𝓝 a] h := hEH.eventuallyEq_of_mem (hW.mem_nhds (haW (by simp)))
  have hd : deriv H a ≠ 0 := by rw [he.deriv_eq]; exact ha
  obtain ⟨e,hes,hei,hem,hee⟩ := nonzero_smooth_germ_diffeomorphism hH a hd
  exact ⟨e,hes,hei,hem,hee.trans he⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
