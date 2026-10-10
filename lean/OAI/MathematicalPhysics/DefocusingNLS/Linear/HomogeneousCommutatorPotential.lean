import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCommutatorCompletion

namespace OAI

/-! # Compact commutator for every actual Y coefficient

The coefficient approximation is in the faithful physical algebra norm.
In particular the theorem applies to the coefficients of the constructed
profile, without assuming extra rapid decay for that profile.
-/

open Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

theorem tendsto_homogeneousTopCommutator (a M : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (j : Fin (N + 1) → Fin 12) (V : HomogeneousY a ((N + 1 : ℕ) : ℝ))
    (u : ℕ → HomogeneousY a ((N + 1 : ℕ) : ℝ)) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a ((N + 1 : ℕ) : ℝ) →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => homogeneousTopCommutator a (N + 1) ha ha1 hk j V (u n))
      atTop (𝓝 0) := by
  let T := homogeneousTopCommutator a (N + 1) ha ha1 hk j
  let C := ‖T‖
  have hC : 0 ≤ C := norm_nonneg T
  have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (hu 0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_order.2
  constructor
  · intro r hr
    exact Eventually.of_forall (fun n => hr.trans_le (norm_nonneg _))
  · intro ε hε
    let δ := ε / (2 * (C * M + 1))
    have hδ : 0 < δ := div_pos hε (by positivity)
    obtain ⟨φ, hφ⟩ := (homogeneousSchwartzEmbedding_dense a ((N + 1 : ℕ) : ℝ) ha ha1 hk).exists_dist_lt V hδ
    let Vφ := homogeneousSchwartzEmbedding a ((N + 1 : ℕ) : ℝ) ha ha1 hk φ
    have hdiff : ‖V - Vφ‖ < δ := by simpa only [dist_eq_norm] using hφ
    have hs := tendsto_homogeneousTopCommutator_Schwartz_coefficient a M N ha ha1 hk j φ u hu hweak
    have he := hs.norm.eventually (gt_mem_nhds (show ‖(0 : MeasureTheory.Lp ℂ 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 12))))‖ < ε / 2 by
        simpa only [norm_zero] using half_pos hε))
    have hδbound : C * δ * M ≤ ε / 2 := by
      have hid : δ * (2 * (C * M + 1)) = ε := div_mul_cancel₀ _ (by positivity)
      nlinarith [hδ.le]
    filter_upwards [he] with n hn
    have herror : ‖T (V - Vφ) (u n)‖ ≤ ε / 2 := calc
      _ ≤ C * ‖V - Vφ‖ * ‖u n‖ := T.le_opNorm₂ _ _
      _ ≤ C * ‖V - Vφ‖ * M := mul_le_mul_of_nonneg_left (hu n)
        (mul_nonneg hC (norm_nonneg _))
      _ ≤ C * δ * M := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdiff.le hC) hM
      _ ≤ ε / 2 := hδbound
    have hsum : T V (u n) = T Vφ (u n) + T (V - Vφ) (u n) := by
      simp only [map_sub, sub_apply]
      abel
    change ‖T V (u n)‖ < ε
    calc
      _ = ‖T Vφ (u n) + T (V - Vφ) (u n)‖ := congrArg norm hsum
      _ ≤ ‖T Vφ (u n)‖ + ‖T (V - Vφ) (u n)‖ := norm_add_le _ _
      _ < ε := by linarith

end DefocusingNLS

end OAI
