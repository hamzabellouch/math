import OAI.MeasureTheory.Falconer.Geometry.InactiveBinGeometry
import OAI.MeasureTheory.Falconer.Angular.RotatedScaleNonstationary

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem inactive_bin_integral_bound {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) {a b : ℝ} (hab : a ≤ b) (hsw : tsupport w ⊆ Icc a b)
    (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ δ, 0 < δ → δ ≤ 1 → ∀ (e : UnitCircle) (φ : ℝ),
    |φ| ≤ Real.pi → dist (sourceUnitDirection φ) e ≤ δ →
    (∀ θ ∈ tsupport w, 0 ≤ Real.cos (θ-φ)) →
    ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f → ∀ {C D Λ : ℝ}, 0 ≤ C → 0 ≤ D → 0 < Λ →
    (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖∫ x : ℝ, cosineOscillator Λ (x-φ) *
      (w x * selectedBinAmplitude δ (inactiveAngularLabels (angularBinCount δ) e (3*δ)) f x)‖ ≤
      A*C*(max D δ⁻¹/(Λ*δ))^n := by
  obtain ⟨B,hB,hbin⟩ := selectedBinAmplitude_derivatives n
  obtain ⟨W,hW,hweight⟩ := compact_multiplier_uniform_derivatives hw isCompact_Icc hsw n
  obtain ⟨A,hA,hnon⟩ := angular_nonstationary_rotated_scale hab n
  refine ⟨A*(W*B), by positivity, ?_⟩
  intro δ hδ hcap e φ hφ hmove hcone f hf C D Λ hC hD hΛ hb
  let S := inactiveAngularLabels (angularBinCount δ) e (3*δ)
  have hg := selectedBinAmplitude_contDiff δ S hf
  have hδπ : δ ≤ 2*Real.pi := hcap.trans (by have := Real.one_le_pi_div_two; linarith)
  have hbin' := hbin δ hδ hδπ S hf hC hD hb
  have hd : 1 ≤ max D δ⁻¹ := ((one_le_inv₀ hδ).mpr hcap).trans (le_max_right _ _)
  have hh := hweight hg (mul_nonneg hB hC) hd hbin'
  have hs : tsupport (fun y => w y * selectedBinAmplitude δ S f y) ⊆ Icc a b :=
    tsupport_mul_subset_left.trans hsw
  have hi := hnon δ hδ hcap φ hφ (hw.mul hg) hs
    (fun θ hθ => inactive_bin_sine_separation hδ e hmove hcone hθ)
    (mul_nonneg hW (mul_nonneg hB hC)) (le_max_right _ _) hΛ hh
  apply hi.trans_eq
  ring

end PlanarFalconer

end OAI
