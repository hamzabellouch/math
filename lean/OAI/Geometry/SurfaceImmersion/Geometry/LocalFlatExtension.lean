import OAI.Geometry.SurfaceImmersion.Geometry.FlatExtension

namespace OAI

/-! Boundary flatness only needs smoothness on the admissible neighborhood. -/
noncomputable section
open Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iteratedFDeriv_zero_on_local_closure {F : A → E} {O U : Set A}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hO : IsOpen O) (hOU : O ⊆ U) (hz : ∀ p ∈ O, F p = 0) (n : ℕ) :
    EqOn (iteratedFDeriv ℝ n F) (fun _ => 0) (closure O ∩ U) := by
  have he : EqOn (iteratedFDeriv ℝ n F) (fun _ => 0) O := by
    intro p hp
    have hg : F =ᶠ[𝓝 p] (fun _ : A => (0 : E)) := by
      filter_upwards [hO.mem_nhds hp] with q hq
      exact hz q hq
    have hd := (hg.iteratedFDeriv ℝ n).eq_of_nhds
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hd
  have hc : ContinuousOn (iteratedFDeriv ℝ n F) U := by
    apply (hF.continuousOn_iteratedFDerivWithin (m := n) (by simp) hU.uniqueDiffOn).congr
    intro p hp
    exact (iteratedFDerivWithin_of_isOpen n hU hp).symm
  exact he.of_subset_closure (hc.mono inter_subset_right) continuousOn_const
    (fun p hp => ⟨subset_closure hp, hOU hp⟩) inter_subset_left

theorem fderiv_eq_on_local_closure {F G : A → E} {O U : Set A}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    (hO : IsOpen O) (hOU : O ⊆ U) (heq : EqOn F G O) :
    EqOn (fderiv ℝ F) (fderiv ℝ G) (closure O ∩ U) := by
  have he : EqOn (fderiv ℝ F) (fderiv ℝ G) O := by
    intro p hp
    have hg : F =ᶠ[𝓝 p] G := by
      filter_upwards [hO.mem_nhds hp] with q hq
      exact heq hq
    exact hg.fderiv_eq
  have hcF := (hF.fderiv_of_isOpen hU (m := ∞) (by simp)).continuousOn
  have hcG := (hG.fderiv_of_isOpen hU (m := ∞) (by simp)).continuousOn
  exact he.of_subset_closure (hcF.mono inter_subset_right) (hcG.mono inter_subset_right)
    (fun p hp => ⟨subset_closure hp, hOU hp⟩) inter_subset_left

end ClosedSurfaceR4

end

end OAI
