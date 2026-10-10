import OAI.Geometry.SurfaceImmersion.Whitney.OrientedDoubleTransition

namespace OAI

/-! Two regular smooth real parameters admit a local smooth change of
parameter, constructed using the proved global extension of an oriented germ. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem local_parameter_transition {h k : ℝ → ℝ} {U V : Set ℝ} {a b : ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (ha : a ∈ U) (hb : b ∈ V)
    (hh : ContDiffOn ℝ ∞ h U) (hk : ContDiffOn ℝ ∞ k V)
    (hhn : deriv h a ≠ 0) (hkn : deriv k b ≠ 0) (heq : h a = k b) :
    ∃ H : ℝ → ℝ, ContDiffOn ℝ ∞ H U ∧ H a = b ∧ deriv H a ≠ 0 ∧
      h =ᶠ[𝓝 a] k ∘ H := by
  have hs : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ 0 < deriv (fun t => s*k t) b := by
    by_cases hp : 0 < deriv k b
    · exact ⟨1,Or.inl rfl,by simpa only [one_mul] using hp⟩
    · refine ⟨-1,Or.inr rfl,?_⟩
      have hn := lt_of_le_of_ne (le_of_not_gt hp) hkn
      simpa only [neg_one_mul,deriv.fun_neg] using neg_pos.mpr hn
  obtain ⟨s,hs,hpos⟩ := hs
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  obtain ⟨e,hes,hei,hem,heg⟩ := local_increasing_diffeomorphism hV
    (contDiffOn_const.mul hk) hb hpos
  have heb : e b = s*k b := heg.eq_of_nhds
  let H : ℝ → ℝ := fun t => e.symm (s*h t)
  have hHs : ContDiffOn ℝ ∞ H U := hei.comp_contDiffOn (contDiffOn_const.mul hh)
  have hHa : H a = b := by
    change e.symm (s*h a) = b
    rw [heq,← heb,e.symm_apply_apply]
  have hD := ((hei.differentiable (by simp) (s*h a)).hasDerivAt.comp a
    (((hh.contDiffAt (hU.mem_nhds ha)).differentiableAt (by simp)).hasDerivAt.const_mul s)).deriv
  dsimp only [Function.comp_def] at hD
  have hHn : deriv H a ≠ 0 := by
    rw [hD]
    exact mul_ne_zero (smooth_real_homeomorph_deriv_ne_zero e.symm hei hes (s*h a))
      (mul_ne_zero hs0 hhn)
  have hHt : Tendsto H (𝓝 a) (𝓝 b) := hHa ▸ (hHs.continuousOn.continuousAt (hU.mem_nhds ha))
  have hcomp := heg.comp_tendsto hHt
  refine ⟨H,hHs,hHa,hHn,?_⟩
  filter_upwards [hcomp] with t ht
  change h t = k (H t)
  apply mul_left_cancel₀ hs0
  exact (e.apply_symm_apply (s*h t)).symm.trans ht

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
