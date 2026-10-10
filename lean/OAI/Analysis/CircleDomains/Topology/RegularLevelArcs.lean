import OAI.Analysis.CircleDomains.Selection.RegularContours
import OAI.Analysis.CircleDomains.Modulus.FiniteCostChartPaths
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace OAI

/-! Local regular-level arcs with finite weighted path cost, obtained from
actual smooth implicit-function coordinates and Hausdorff length. -/

open Set Function MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_finite_cost_regular_level_arc {f : ℂ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {t : ℝ} {z : ℂ}
    (hz : f z = t) (hregular : fderiv ℝ f z ≠ 0)
    (g : ℂ → ℝ≥0∞)
    (hfinite : (∫⁻w in {w | f w = t}, g w ∂(μH[1] : Measure ℂ)) < ∞) :
    ∃ (γ : RectifiablePath ℂ) (V : Set ℂ), IsOpen V ∧ z ∈ V ∧
      V ∩ {w | f w = t} ⊆ range γ.val ∧ range γ.val ⊆ {w | f w = t} ∧
      Injective γ.val ∧ (∫⁻w, g w ∂pathOccupation γ) < ∞ := by
  obtain ⟨e, hze, he, heSmooth, heInv⟩ := exists_smooth_planar_level_chart hf hregular
  let y0 : ℝ := (e z).2
  let φ : ℝ → ℂ := fun y => e.symm (t, y)
  let ψ : ℂ → ℝ := fun w => (e w).2
  have hez : (t, y0) = e z := Prod.ext ((he z).trans hz).symm rfl
  have htarget : (t, y0) ∈ e.target := hez ▸ e.map_source hze
  have hφz : φ y0 = z := by
    change e.symm (t, y0) = z
    rw [hez, e.left_inv hze]
  have hφsmooth : ContDiffAt ℝ (↑(⊤ : ℕ∞)) φ y0 :=
    (heInv.contDiffAt (e.open_target.mem_nhds htarget)).comp y0
      (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨L0, T, hT, hL0⟩ := (hφsmooth.of_le (by simp)).exists_lipschitzOnWith
  obtain ⟨K, U, hU, hK⟩ :=
    (show ContDiffAt ℝ 1 ψ z from
      (contDiff_snd.comp heSmooth).contDiffAt.of_le (by simp)).exists_lipschitzOnWith
  have hφU : φ ⁻¹' U ∈ 𝓝 y0 := by
    apply hφsmooth.continuousAt.preimage_mem_nhds
    rwa [hφz]
  have htargetN : (fun y : ℝ => (t, y)) ⁻¹' e.target ∈ 𝓝 y0 :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds htarget)
  obtain ⟨δ, hδ, hδR⟩ := Metric.mem_nhds_iff.mp (inter_mem (inter_mem hT hφU) htargetN)
  let a : ℝ := y0 - δ / 2
  let b : ℝ := y0 + δ / 2
  have hab : a < b := by dsimp [a, b]; linarith
  have hI : Icc a b ⊆ ball y0 δ := by
    intro y hy
    rw [mem_ball, Real.dist_eq, abs_lt]
    dsimp [a, b] at hy
    constructor <;> linarith [hy.1, hy.2]
  have hφLip : LipschitzOnWith (L0 + 1) φ (Icc a b) :=
    (hL0.mono (fun y hy => (hδR (hI hy)).1.1)).weaken (le_add_of_nonneg_right zero_le_one)
  have hφU' : MapsTo φ (Icc a b) U := fun y hy => (hδR (hI hy)).1.2
  have hφtarget : ∀ y ∈ Icc a b, (t, y) ∈ e.target := fun y hy => (hδR (hI hy)).2
  have hinv : ∀ y ∈ Icc a b, ψ (φ y) = y := by
    intro y hy
    exact congrArg Prod.snd (e.right_inv (hφtarget y hy))
  have hlevel : φ '' Icc a b ⊆ {w | f w = t} := by
    rintro w ⟨y, hy, rfl⟩
    change f (e.symm (t, y)) = t
    rw [← he, e.right_inv (hφtarget y hy)]
  let γ := intervalChartPath φ hab.le hφLip
  let V := e.source ∩ ψ ⁻¹' Ioo a b
  have hV : IsOpen V := e.open_source.inter (isOpen_Ioo.preimage (continuous_snd.comp heSmooth.continuous))
  have hzV : z ∈ V := by
    refine ⟨hze, ?_⟩
    change a < y0 ∧ y0 < b
    dsimp [a, b]
    constructor <;> linarith
  have hrange : range γ.val = φ '' Icc a b := intervalChartPath_range φ hab hφLip
  refine ⟨γ, V, hV, hzV, ?_, hrange ▸ hlevel, ?_, ?_⟩
  · intro w hw
    rw [hrange]
    refine ⟨ψ w, ⟨hw.1.2.1.le, hw.1.2.2.le⟩, ?_⟩
    change e.symm (t, (e w).2) = w
    have hwcoord : (t, (e w).2) = e w := Prod.ext ((he w).trans hw.2).symm rfl
    rw [hwcoord, e.left_inv hw.1.1]
  · exact (intervalChartPath_antilipschitz φ ψ hab hφLip hK hφU' hinv).injective
  · exact intervalChartPath_cost_lt_top φ ψ hab hφLip (by positivity) hK hφU' hinv hlevel g hfinite

end CircleDomainRigidity

end

end OAI
