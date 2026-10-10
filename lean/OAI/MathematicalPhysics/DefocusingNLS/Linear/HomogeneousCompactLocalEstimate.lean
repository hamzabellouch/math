import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousWeakSubsequence
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousObservationSeparates
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLocalL2Energy

namespace OAI

/-! # The local physical observation form of a compact Y error

A failure of the estimate produces unit vectors with vanishing observation
on expanding balls. Their weak subsequential limit is zero by faithfulness
of the physical realization, contradicting the proved compact-error bound.
-/

open MeasureTheory Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousCompactOperator_local_estimate
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (T : HomogeneousY a k →L[ℝ] F)
    (hcompact : ∀ (M : ℝ) (u : ℕ → HomogeneousY a k), (∀ n, ‖u n‖ ≤ M) →
      (∀ ℓ : HomogeneousY a k →L[ℝ] ℂ, Tendsto (fun n => ℓ (u n)) atTop (𝓝 0)) →
      Tendsto (fun n => T (u n)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ u : HomogeneousY a k,
      ‖T u‖ ≤ ε * ‖u‖ + C * ‖homogeneousLocalL2Observation a k R ha ha1 hk u‖ := by
  by_contra! h
  have hex (n : ℕ) : ∃ u : HomogeneousY a k,
      ε * ‖u‖ + ((n : ℝ) + 1) *
        ‖homogeneousLocalL2Observation a k ((n : ℝ) + 1) ha ha1 hk u‖ < ‖T u‖ :=
    h ((n : ℝ) + 1) (by positivity) ((n : ℝ) + 1) (by positivity)
  choose u hu using hex
  have hup (n : ℕ) : 0 < ‖u n‖ := by
    by_contra hn
    have hz : u n = 0 := norm_eq_zero.mp (le_antisymm (le_of_not_gt hn) (norm_nonneg _))
    simpa only [hz, map_zero, norm_zero, mul_zero, add_zero, lt_self_iff_false] using hu n
  let w : ℕ → HomogeneousY a k := fun n => (‖u n‖)⁻¹ • u n
  have hwn (n : ℕ) : ‖w n‖ = 1 := by
    dsimp only [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hup n)),
      inv_mul_cancel₀ (hup n).ne']
  have hTn (n : ℕ) : ‖T (w n)‖ = ‖T (u n)‖ / ‖u n‖ := by
    dsimp only [w]
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hup n))]
    exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm
  have hJn (n : ℕ) :
      ‖homogeneousLocalL2Observation a k ((n : ℝ) + 1) ha ha1 hk (w n)‖ =
        ‖homogeneousLocalL2Observation a k ((n : ℝ) + 1) ha ha1 hk (u n)‖ / ‖u n‖ := by
    dsimp only [w]
    rw [ContinuousLinearMap.map_smul_of_tower, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (hup n))]
    exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm
  have hstep (n : ℕ) : ε + ((n : ℝ) + 1) *
      ‖homogeneousLocalL2Observation a k ((n : ℝ) + 1) ha ha1 hk (w n)‖ < ‖T (w n)‖ := by
    rw [hTn, hJn]
    calc
      _ = (ε * ‖u n‖ + ((n : ℝ) + 1) *
          ‖homogeneousLocalL2Observation a k ((n : ℝ) + 1) ha ha1 hk (u n)‖) / ‖u n‖ := by
        field_simp [(hup n).ne']
      _ < _ := div_lt_div_of_pos_right (hu n) (hup n)
  have hJbound (n : ℕ) :
      ‖homogeneousLocalL2Observation a k ((n : ℝ) + 1) ha ha1 hk (w n)‖ ≤
        ‖T‖ / ((n : ℝ) + 1) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have ht := T.le_opNorm (w n)
    rw [hwn, mul_one] at ht
    nlinarith [hstep n]
  have hJzero (R : ℝ) :
      Tendsto (fun n => homogeneousLocalL2Observation a k R ha ha1 hk (w n)) atTop (𝓝 0) := by
    obtain ⟨N, hRN⟩ := exists_nat_gt R
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _))
      (g := fun n : ℕ => ‖T‖ / ((n : ℝ) + 1))
    · filter_upwards [eventually_ge_atTop N] with n hn
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
      exact (homogeneousLocalL2Observation_norm_mono a k R ((n : ℝ) + 1)
        ha ha1 hk (by linarith) (w n)).trans (hJbound n)
    · simpa only [div_eq_mul_inv, one_mul, mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ‖T‖
  obtain ⟨v, _hv, φ, hφ, hw⟩ := homogeneousY_weak_subsequence a k 1 ha1 hk w
    (fun n => (hwn n).le)
  have hv0 : v = 0 := by
    apply homogeneousLocalL2_observations_separate a k ha ha1 hk v
    intro R _hR
    let J := homogeneousLocalL2Observation a k R ha ha1 hk
    let ℓ : HomogeneousY a k →L[ℝ] ℂ := ((innerSL ℂ (J v)).comp J).restrictScalars ℝ
    have h₁ := hw ℓ
    have h₂ := (innerSL ℂ (J v)).continuous.continuousAt.tendsto.comp
      ((hJzero R).comp hφ.tendsto_atTop)
    have he := tendsto_nhds_unique h₁ h₂
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    simpa only [ℓ, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_zero_right] using he
  have hTzero := hcompact 1 (fun n => w (φ n)) (fun n => (hwn (φ n)).le)
    (fun ℓ => by simpa only [hv0, map_zero] using hw ℓ)
  have he := hTzero.norm.eventually (gt_mem_nhds (show ‖(0 : F)‖ < ε by simpa using hε))
  obtain ⟨n, hn⟩ := he.exists
  have hn' := hstep (φ n)
  have hnonneg : 0 ≤ ((φ n : ℝ) + 1) *
      ‖homogeneousLocalL2Observation a k ((φ n : ℝ) + 1) ha ha1 hk (w (φ n))‖ := by positivity
  linarith

end DefocusingNLS

end OAI
