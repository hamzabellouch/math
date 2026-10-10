import OAI.Analysis.CircleDomains.Reflection.UnitAnalyticJordanParametrization
import OAI.Analysis.CircleDomains.Topology.HolomorphicPlaneChart
import OAI.Analysis.CircleDomains.Topology.CompactChartConjugation
import OAI.Analysis.CircleDomains.Transfer.RadialShrinkImages
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

namespace OAI

/-! Shrink one actual analytic Jordan cap within any prescribed open
neighborhood. The ambient map and its inverse are smooth and fix every
point outside one compact subset of that neighborhood. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_analytic_cap_shrinker {H : ℂ ≃ₜ ℂ} (ha : IsAnalyticJordanCap H)
    {O : Set ℂ} (hO : IsOpen O) (hHO : closure (jordanInterior H)⊆O) :
    ∃ (β : ℂ → ℂ) (S K : Set ℂ), IsOpen S ∧ closedBall 0 1⊆S ∧
      DifferentiableOn ℂ β S ∧ InjOn β S ∧ IsCompact K ∧ K⊆O ∧
      β '' closedBall 0 1=closure (jordanInterior H) ∧
      (∀t:ℝ,0<t → t≤1 → ∃G : ℂ ≃ₜ ℂ,
        ContDiff ℝ ∞ (G : ℂ → ℂ) ∧ ContDiff ℝ ∞ (G.symm : ℂ → ℂ) ∧
        (∀z∉K,G z=z) ∧ G '' closure (jordanInterior H)=β '' closedBall 0 t) := by
  obtain ⟨S,β,hS,hDS,hβ,hi,hclosed,_⟩ := exists_unit_analytic_jordan_parametrization ha
  let U := S∩β ⁻¹' O
  have hU : IsOpen U := hβ.continuousOn.isOpen_inter_preimage hS hO
  have hDU : closedBall (0:ℂ) 1⊆U := by
    intro z hz
    exact ⟨hDS hz,hHO (hclosed ▸ mem_image_of_mem β hz)⟩
  obtain ⟨δ,hδ,hthick⟩ := (isCompact_closedBall (0:ℂ) 1).exists_cthickening_subset_open hU hDU
  rw [cthickening_closedBall hδ.le zero_le_one] at hthick
  let b := δ+1
  have hb : 1<b := by dsimp [b];linarith
  have hBU : closedBall (0:ℂ) b⊆U := hthick
  let e := holomorphicPlaneChart hU (hβ.mono inter_subset_left) (hi.mono inter_subset_left)
  let K := β '' closedBall 0 b
  have hK : IsCompact K := (isCompact_closedBall (0:ℂ) b).image_of_continuousOn
    (hβ.continuousOn.mono (hBU.trans inter_subset_left))
  have hKO : K⊆O := by rintro _ ⟨z,hz,rfl⟩;exact (hBU hz).2
  refine ⟨β,S,K,hS,hDS,hβ,hi,hK,hKO,hclosed,?_⟩
  intro t ht ht1
  let T := smoothRadialShrinkHomeomorph ht ht1 zero_lt_one hb
  have hfix : ∀z∉closedBall (0:ℂ) b,T z=z := by
    intro z hz
    apply radialShrink_outer zero_lt_one hb
    exact (lt_of_not_ge (by simpa only [mem_closedBall,dist_zero_right] using hz)).le
  let G := compactChartHomeomorph e T (isCompact_closedBall 0 b) hBU hfix
  have hes := holomorphicPlaneChart_smooth hU (hβ.mono inter_subset_left) (hi.mono inter_subset_left)
  have his := holomorphicPlaneChart_inverse_smooth hU (hβ.mono inter_subset_left) (hi.mono inter_subset_left)
  refine ⟨G,?_,?_,?_,?_⟩
  · exact chartConjugate_contDiff e T (isCompact_closedBall 0 b) hBU hfix hes his
      (radialShrink_contDiff t 1 b)
  · exact compactChartHomeomorph_inverse_smooth e T (isCompact_closedBall 0 b) hBU hfix hes his
      (smoothRadialShrinkHomeomorph_inverse_contDiff ht ht1 zero_lt_one hb)
  · intro z hz
    exact chartConjugate_eq_off e T hfix hz
  · rw [←hclosed]
    change G '' (e '' closedBall 0 1)=e '' closedBall 0 t
    rw [compactChartHomeomorph_image e T (isCompact_closedBall 0 b) hBU hfix hDU]
    change e '' (radialShrink t 1 b '' closedBall 0 1)=_
    rw [radialShrink_image_inner ht zero_lt_one hb,mul_one]

end CircleDomainRigidity

end

end OAI
