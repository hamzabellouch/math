import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLowCompact

namespace OAI

/-! # Compact low-energy multiplication for every coefficient in Y

Density of physical Schwartz functions in the actual Y norm and the proved
bilinear product bound extend the compact observation result to every fixed
Y coefficient. This applies to the polynomial coefficients of the actual
odd-power linearization.
-/

open Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

theorem tendsto_homogeneousLowEnergy_product (a k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (V : HomogeneousY a k) (u : ℕ → HomogeneousY a k) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => homogeneousLowEnergy a k ha1 hk
      (homogeneousYProduct a k ha ha1 hk V (u n))) atTop (𝓝 0) := by
  let B := homogeneousYProduct a k ha ha1 hk
  let L := homogeneousLowEnergy a k ha1 hk
  let C := ‖B‖
  have hC : 0 ≤ C := norm_nonneg B
  have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (hu 0)
  have hnorm : Tendsto (fun n => ‖L (B V (u n))‖) atTop (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro r hr
      exact Filter.Eventually.of_forall (fun n => hr.trans_le (norm_nonneg _))
    · intro ε hε
      let δ := ε / (2 * (C * M + 1))
      have hδ : 0 < δ := div_pos hε (by positivity)
      obtain ⟨φ, hφ⟩ := (homogeneousSchwartzEmbedding_dense a k ha ha1 hk).exists_dist_lt V hδ
      let Vφ := homogeneousSchwartzEmbedding a k ha ha1 hk φ
      have hdiff : ‖V - Vφ‖ < δ := by simpa only [dist_eq_norm] using hφ
      have hs := tendsto_homogeneousLowEnergy_schwartzCoefficient a k M ha ha1 hk φ u hu hweak
      have hs' : Tendsto (fun n => ‖L (B Vφ (u n))‖) atTop (𝓝 0) := by
        have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
        change Tendsto (fun n => Real.sqrt (‖L (B Vφ (u n))‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at h
        simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h
      have he := hs'.eventually (gt_mem_nhds (half_pos hε))
      have hδbound : C * δ * M ≤ ε / 2 := by
        have hid : δ * (2 * (C * M + 1)) = ε := div_mul_cancel₀ _ (by positivity)
        nlinarith [hδ.le]
      filter_upwards [he] with n hn
      have herror : ‖L (B (V - Vφ) (u n))‖ ≤ ε / 2 := calc
        _ ≤ ‖B (V - Vφ) (u n)‖ := homogeneousLowEnergy_norm_le a k ha1 hk _
        _ ≤ C * ‖V - Vφ‖ * ‖u n‖ := B.le_opNorm₂ _ _
        _ ≤ C * ‖V - Vφ‖ * M := mul_le_mul_of_nonneg_left (hu n)
          (mul_nonneg hC (norm_nonneg _))
        _ ≤ C * δ * M := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdiff.le hC) hM
        _ ≤ ε / 2 := hδbound
      have hsum : L (B V (u n)) = L (B Vφ (u n)) + L (B (V - Vφ) (u n)) := by
        simp only [map_sub, sub_apply]
        abel
      calc
        ‖L (B V (u n))‖ = ‖L (B Vφ (u n)) + L (B (V - Vφ) (u n))‖ := congrArg norm hsum
        _ ≤ ‖L (B Vφ (u n))‖ + ‖L (B (V - Vφ) (u n))‖ := norm_add_le _ _
        _ < ε := by linarith
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using hnorm

end DefocusingNLS

end OAI
