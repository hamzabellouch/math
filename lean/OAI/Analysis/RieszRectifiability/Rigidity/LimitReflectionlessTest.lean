import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.LimitRieszInteriorOscillation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem limit_rieszScalarPairing_zero_of_oscillation {d : ℕ} (p : ℕ) (C D : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, SFinite (μ j)] [SFinite ν]
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j)) (hgν : GlobalUpperGrowth (p + 1) D ν)
    (hweak : CompactTestConvergence μ ν)
    (a : Ambient d) (ha : a ∈ ν.support) (A v : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hv : Tendsto v atTop (𝓝 0))
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) a (A j) (v j))
    (e : Ambient d) (he : ‖e‖ ≤ 1)
    (φ η : Ambient d → ℝ) (Lφ Lη Bφ Bη : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hη : LipschitzWith Lη η)
    (hcφ : HasCompactSupport φ) (hcη : HasCompactSupport η)
    (hBφ : ∀ x, |φ x| ≤ (Bφ : ℝ)) (hBη : ∀ x, |η x| ≤ (Bη : ℝ))
    (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hsφ : ∀ x, φ x ≠ 0 → dist x a ≤ H) (hsη : ∀ x, η x ≠ 0 → dist x a ≤ H)
    (hmean : (∫ x, φ x ∂ν) = 0) (hbump : (∫ x, η x ∂ν) ≠ 0) :
    rieszScalarPairing (p + 1) ν a R e φ = 0 := by
  let K₁ := compactRieszTailConstant (p + 1) C e H (Bφ + Bη)
  let K₂ := compactRieszTailConstant (p + 1) D e H Bφ
  let K := K₁ + K₂
  have hK₁ : 0 ≤ K₁ := compactRieszTailConstant_nonneg (p + 1) C e H (Bφ + Bη) (hg 0).1 hH
  have hK₂ : 0 ≤ K₂ := compactRieszTailConstant_nonneg (p + 1) D e H Bφ hgν.1 hH
  have hK : 0 ≤ K := add_nonneg hK₁ hK₂
  let P := rieszScalarPairing (p + 1) ν a R e φ
  by_contra hn
  have hP : 0 < |P| := abs_pos.mpr hn
  let T₀ := max (2 * H) ((K + 1) / |P|)
  obtain ⟨T, hTinterval, hboundary⟩ := exists_null_frontier_thickening ν {a}
    (show T₀ < T₀ + 1 by linarith)
  simp only [thickening_singleton] at hboundary
  have hHT : 2 * H ≤ T := (le_max_left _ _).trans hTinterval.1.le
  have hTlarge : (K + 1) / |P| < T := (le_max_right _ _).trans_lt hTinterval.1
  have hT : 0 < T := (div_pos (by positivity : 0 < K + 1) hP).trans hTlarge
  have hmass : ν (ball a T) ≠ 0 :=
    ((ν.mem_support_iff_forall a).mp ha (ball a T) (ball_mem_nhds a hT)).ne'
  have hinner := limit_rieszInterior_bound_of_oscillation p C D μ ν hg hgν hweak a A v hA hv hosc
    e he φ η Lφ Lη Bφ Bη hφ hη hcφ hcη hBφ hBη H T hH hT hHT hsφ hsη hmean hbump
    hboundary hmass
  have htail := rieszScalarPairing_interior_tail_bound (p + 1) D ν hgν a H T hH hT hHT
    e φ Lφ Bφ hφ hBφ hsφ
  have heq := rieszScalarPairing_localization_independent p D ν hgν e φ Lφ hφ
    a a H H R T hH hH hR hT hHR hHT hsφ hsφ hmean
  let I := (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e φ q
    ∂(ν.restrict (ball a T)).prod (ν.restrict (ball a T)))
  have hb : |P| ≤ K / T := by
    change |rieszScalarPairing (p + 1) ν a R e φ| ≤ _
    rw [heq]
    calc
      _ ≤ |rieszScalarPairing (p + 1) ν a T e φ - I| + |I| := by
        simpa only [sub_add_cancel] using! abs_add_le
          (rieszScalarPairing (p + 1) ν a T e φ - I) I
      _ ≤ K₂ / T + K₁ / T := add_le_add htail hinner
      _ = _ := by dsimp only [K]; ring
  have hstrict : K / T < |P| := by
    apply (div_lt_iff₀ hT).mpr
    have h := (div_lt_iff₀ hP).mp hTlarge
    nlinarith
  exact (not_lt_of_ge hb) hstrict

end

end RieszRectifiability

end OAI
