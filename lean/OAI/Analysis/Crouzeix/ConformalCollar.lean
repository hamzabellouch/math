import Mathlib
import OAI.Analysis.Crouzeix.CollarUnivalence

namespace OAI

/-! Conformal Collar. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

theorem isOpen_image_of_univalent {V : Set ℂ} (hV : IsOpen V) {g : ℂ → ℂ}
    (hga : AnalyticOnNhd ℂ g V) (hgi : InjOn g V) : IsOpen (g '' V) := by
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨z, hz, rfl⟩
  rw [← (hga z hz).hasStrictDerivAt.map_nhds_eq
    (deriv_ne_zero_of_injOn hV hga.differentiableOn hgi hz)]
  exact image_mem_map (hV.mem_nhds hz)

theorem image_closure_eq_closedDisk {U V : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hUV : closure U ⊆ V) {g : ℂ → ℂ}
    (hga : AnalyticOnNhd ℂ g V) (hbij : BijOn g U (ball 0 1))
    (hfront : ∀ p ∈ frontier U, ‖g p‖ = 1) : g '' closure U = closedBall 0 1 := by
  apply Subset.antisymm
  · rintro w ⟨z, hz, rfl⟩
    rw [mem_closedBall_zero_iff]
    by_cases hzu : z ∈ U
    · exact (mem_ball_zero_iff.mp (hbij.mapsTo hzu)).le
    · exact (hfront z ⟨hz, by simpa only [hU.interior_eq] using hzu⟩).le
  · rw [← closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
    apply closure_minimal _ ((hb.isCompact_closure.image_of_continuousOn
      (hga.continuousOn.mono hUV)).isClosed)
    exact hbij.surjOn.trans (image_mono subset_closure)

theorem exists_conformal_collar {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hc : IsSimplyConnected U) {a : ℂ} (ha : a ∈ U)
    (hchart : ∀ p ∈ frontier U, Nonempty (BoundaryChart U p)) :
    ∃ (V : Set ℂ) (ρ : ℝ) (f h : ℂ → ℂ),
      IsOpen V ∧ closure U ⊆ V ∧ 1 < ρ ∧
      AnalyticOnNhd ℂ f V ∧ AnalyticOnNhd ℂ h (ball 0 ρ) ∧
      InjOn f V ∧ InjOn h (ball 0 ρ) ∧
      BijOn f U (ball 0 1) ∧ BijOn h (ball 0 1) U ∧
      BijOn f (closure U) (closedBall 0 1) ∧
      BijOn h (closedBall 0 1) (closure U) ∧
      InvOn h f U (ball 0 1) ∧ f a = 0 ∧ h 0 = a ∧
      (∀ z ∈ frontier U, ‖f z‖ = 1) ∧
      InvOn h f V (f '' V) ∧ ball 0 ρ ⊆ f '' V := by
  obtain ⟨f₀, hf₀, _, hfb₀⟩ := riemann_mapping_bounded hU hb hc ha
  obtain ⟨V, f, hV, hUV, hfa, hfe, hfi, hfront⟩ :=
    exists_univalent_extension hU hb hf₀.holomorphic hfb₀ hchart
  have hfb : BijOn f U (ball 0 1) := hfb₀.congr hfe.symm
  have hBij : BijOn f V (f '' V) := ⟨mapsTo_image _ _, hfi, surjOn_image _ _⟩
  let h := invFunOn f V
  have hinv : InvOn h f V (f '' V) := hBij.invOn_invFunOn
  have hWi := isOpen_image_of_univalent hV hfa hfi
  have hha : AnalyticOnNhd ℂ h (f '' V) := by
    apply DifferentiableOn.analyticOnNhd _ hWi
    intro w hw
    exact (hasStrictDerivAt_invFunOn hV hfa.differentiableOn hBij hw).hasDerivAt.differentiableAt.differentiableWithinAt
  have hfc : BijOn f (closure U) (closedBall 0 1) :=
    ⟨by rw [← image_closure_eq_closedDisk hU hb hUV hfa hfb hfront]; exact mapsTo_image _ _,
      hfi.mono hUV,
      by rw [← image_closure_eq_closedDisk hU hb hUV hfa hfb hfront]; exact surjOn_image _ _⟩
  have hclosed : closedBall 0 1 ⊆ f '' V :=
    hfc.surjOn.trans (image_mono hUV)
  have hUsub : U ⊆ V := subset_closure.trans hUV
  have hdisk : ball 0 1 ⊆ f '' V := ball_subset_closedBall.trans hclosed
  have hiU : InvOn h f U (ball 0 1) := ⟨hinv.1.mono hUsub, hinv.2.mono hdisk⟩
  have hiC : InvOn h f (closure U) (closedBall 0 1) := ⟨hinv.1.mono hUV, hinv.2.mono hclosed⟩
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open hWi hclosed
  rw [thickening_closedBall hδ zero_le_one] at hδsub
  have hfa0 : f a = 0 := (hfe ha).trans hf₀.normalized
  have h0 : h 0 = a := hfa0 ▸ hinv.1 (hUsub ha)
  exact ⟨V, δ + 1, f, h, hV, hUV, by linarith,
    hfa, hha.mono hδsub, hfi, (hBij.symm hinv.symm).injOn.mono hδsub,
    hfb, hfb.symm hiU.symm, hfc, hfc.symm hiC.symm, hiU, hfa0, h0,
    hfront, hinv, hδsub⟩

end CrouzeixHilbert.Conformal

end

end OAI
