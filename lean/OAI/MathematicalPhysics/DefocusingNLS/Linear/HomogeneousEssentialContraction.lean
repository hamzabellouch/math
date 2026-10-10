import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEnergyObservation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousTimeObservation

namespace OAI

/-! # The actual time-step contraction on weakly null data

The integrated local term tends to zero by the already proved compact
physical observation. This is the whole-space time-step estimate used
before the finite-rank spectral decomposition.
-/

open MeasureTheory Set Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousLinearized_weakNull_contraction (a b : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (m : ℕ) (q : HomogeneousY a ((N + 1 : ℕ) : ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x : E, ‖homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q x‖ ^
      (2 * (m + 1)) ≤ M)
    (hgap : 0 < ((N + 1 : ℕ) : ℝ) + 2 * a - 6 -
      2 * ((2 * ((m + 1 : ℕ) : ℝ) + 1) * M)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (T : ℝ) (hT : 0 ≤ T) (A : ℝ)
      (u : ℕ → HomogeneousY a ((N + 1 : ℕ) : ℝ)), (∀ n, ‖u n‖ ≤ A) →
      (∀ ℓ : HomogeneousY a ((N + 1 : ℕ) : ℝ) →L[ℝ] ℂ,
        Tendsto (fun n => ℓ (u n)) atTop (𝓝 0)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ‖homogeneousLinearizedPropagator a b ((N + 1 : ℕ) : ℝ) T ha ha1 hk hT
          (m + 1) q (u n) ⟨T, hT, le_rfl⟩‖ ^ 2 < Real.exp (-c * T) * A ^ 2 + ε := by
  obtain ⟨c, hc, R, _hR, C, _hC, hobs⟩ :=
    homogeneousLinearized_integrated_observation a b N ha ha1 hk m q M hM hQB hgap
  refine ⟨c, hc, fun T hT A u hu hw ε hε => ?_⟩
  have htime := tendsto_homogeneousLinearized_timeObservation a b ((N + 1 : ℕ) : ℝ)
    T R A c ha ha1 hk hT (m + 1) q u hu hw
  have hsmall := (htime.const_mul C).eventually
    (gt_mem_nhds (show C * 0 < ε by simpa only [mul_zero] using hε))
  filter_upwards [hsmall] with n hn
  have he := hobs T hT (u n) ⟨T,hT,le_rfl⟩
  dsimp only at he
  have hA : ‖u n‖ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hu n) 2
  have hb := mul_le_mul_of_nonneg_left hA (Real.exp_nonneg (-c * T))
  change _ < Real.exp (-c * T) * A ^ 2 + ε
  simpa only [homogeneousLinearizedPropagator_apply] using he.trans_lt (add_lt_add_of_le_of_lt hb hn)

end DefocusingNLS

end OAI
