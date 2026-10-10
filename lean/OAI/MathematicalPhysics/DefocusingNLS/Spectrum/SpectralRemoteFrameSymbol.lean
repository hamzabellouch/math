import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePhysicalFrame
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteGapSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteInverseJets

namespace OAI

/-! Uniform symbols of the physical leading eigenvector frame and its inverse. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

private theorem part_smooth (h : ℝ) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun c => spectralRemoteInitialFramePart h (c i))
      spectralRemoteRootDomain := by
  have hr (j : ℝ) : ContDiffOn ℝ ∞
      (fun c : Fin 2 → ℝ => homogeneousSpectralLocalizationRemoteRoot h j (c i))
      spectralRemoteRootDomain :=
    (spectralRemote_root_smooth h j).comp (contDiff_apply ℝ ℝ i).contDiffOn
      (fun c hc => hc i)
  exact (((ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) (ℂ × ℂ)
    (ContinuousLinearMap.fst ℂ ℂ ℂ)).restrictScalars ℝ).contDiff.comp_contDiffOn
      (contDiffOn_const.prodMk (hr 1))).add
    (((ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) (ℂ × ℂ)
      (ContinuousLinearMap.snd ℂ ℂ ℂ)).restrictScalars ℝ).contDiff.comp_contDiffOn
        (contDiffOn_const.prodMk (hr (-1))))

private theorem part_continuous (h : ℝ) (i : Fin 2) :
    Continuous (fun c : Fin 2 → ℝ => spectralRemoteInitialFramePart h (c i)) := by
  have hr (j : ℝ) : Continuous
      (fun c : Fin 2 → ℝ => homogeneousSpectralLocalizationRemoteRoot h j (c i)) :=
    (spectralRemote_root_continuous h j).comp (continuous_apply i)
  exact ((ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) (ℂ × ℂ)
    (ContinuousLinearMap.fst ℂ ℂ ℂ)).continuous.comp
      (continuous_const.prodMk (hr 1))).add
    ((ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) (ℂ × ℂ)
      (ContinuousLinearMap.snd ℂ ℂ ℂ)).continuous.comp
        (continuous_const.prodMk (hr (-1))))

theorem spectralRemoteInitialFrame_smooth :
    ContDiffOn ℝ ∞ spectralRemoteInitialFrame spectralRemoteRootDomain :=
  ((ContinuousLinearMap.prodMapL ℂ (ℂ × ℂ) (ℂ × ℂ) (ℂ × ℂ) (ℂ × ℂ)).restrictScalars ℝ).contDiff.comp_contDiffOn
    ((part_smooth 1 0).prodMk (part_smooth (-1) 1))

theorem spectralRemoteInitialFrame_continuous : Continuous spectralRemoteInitialFrame :=
  (ContinuousLinearMap.prodMapL ℂ (ℂ × ℂ) (ℂ × ℂ) (ℂ × ℂ) (ℂ × ℂ)).continuous.comp
    ((part_continuous 1 0).prodMk (part_continuous (-1) 1))

theorem spectralRemote_initial_frame_symbols
    {L : ℕ → ℝ} {c : ℕ → ℝ → Fin 2 → ℝ}
    (hc : HasUniformLogJetBound L 0 c)
    (hsmall : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ i, |c n t i| ≤ 1/32) :
    HasUniformLogJetBound L 0 (fun n t => spectralRemoteInitialFrame (c n t)) ∧
    HasUniformLogJetBound L 0 (fun n t => Ring.inverse (spectralRemoteInitialFrame (c n t))) := by
  let C : Set (Fin 2 → ℝ) := Metric.closedBall 0 (1/32)
  let O : Set (Fin 2 → ℝ) := spectralRemoteRootDomain ∩
    {x | IsUnit (spectralRemoteInitialFrame x)}
  have hO : IsOpen O := spectralRemoteRootDomain_open.inter
    (Units.isOpen.preimage spectralRemoteInitialFrame_continuous)
  have hb (x : Fin 2 → ℝ) (hx : x ∈ C) (i : Fin 2) : |x i| ≤ 1/32 := by
    have hn : ‖x‖ ≤ 1/32 := by simpa only [C,Metric.mem_closedBall,dist_zero_right] using hx
    exact (show |x i| ≤ ‖x‖ from norm_le_pi_norm x i).trans hn
  have hCO : C ⊆ O := fun x hx =>
    ⟨fun i => (le_abs_self _).trans_lt ((hb x hx i).trans_lt (by norm_num)),
      spectralRemoteInitialFrame_unit x (hb x hx)⟩
  have hmem : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), c n t ∈ C := by
    filter_upwards [hsmall] with n hn
    intro t ht
    change dist (c n t) 0 ≤ 1/32
    rw [dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/32)).mpr
      (fun i => by simpa only [Real.norm_eq_abs] using hn t ht i)
  have hp := spectralRemoteInitialFrame_smooth.mono (show O ⊆ spectralRemoteRootDomain from inter_subset_left)
  have hi : ContDiffOn ℝ ∞ (fun x => Ring.inverse (spectralRemoteInitialFrame x)) O := by
    intro x hx
    have hu := hx.2
    obtain ⟨u,he⟩ := hu
    have hii : ContDiffAt ℝ ∞ (Ring.inverse : SpectralRemoteOperator → SpectralRemoteOperator)
        (spectralRemoteInitialFrame x) := by
      rw [← he]
      exact contDiffAt_ringInverse ℝ u
    exact hii.comp_contDiffWithinAt x (hp x hx)
  exact ⟨spectralRemote_uniform_compact_comp hO (isCompact_closedBall _ _) hCO hp hc hmem,
    spectralRemote_uniform_compact_comp
      (g := fun x => Ring.inverse (spectralRemoteInitialFrame x))
      hO (isCompact_closedBall _ _) hCO hi hc hmem⟩

end DefocusingNLS

end OAI
