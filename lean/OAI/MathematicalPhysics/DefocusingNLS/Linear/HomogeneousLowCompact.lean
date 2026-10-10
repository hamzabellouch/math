import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSchwartzObservation

namespace OAI

/-! # Compact low-order action of a fixed physical coefficient

The frequency interpolation inequality extends from Schwartz functions to
the faithful completion, using the actual weighted physical L² observation.
Consequently the low Sobolev part of multiplication by a fixed Schwartz
coefficient vanishes on every bounded weakly null sequence.
-/

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousLowEnergy_coefficient_interpolation (a k ε : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hε : 0 < ε) (V : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : HomogeneousY a k,
      ‖homogeneousLowEnergy a k ha1 hk
        (homogeneousYProduct a k ha ha1 hk
          (homogeneousSchwartzEmbedding a k ha ha1 hk V) f)‖ ^ 2 ≤
      ε * ‖homogeneousYProduct a k ha ha1 hk
        (homogeneousSchwartzEmbedding a k ha ha1 hk V) f‖ ^ 2 +
      C * ‖homogeneousWeightedObservation a k ha ha1 hk V (V.memLp 2) f‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := homogeneousLowEnergy_schwartz_interpolation a k ε ha ha1 hk hε V
  refine ⟨C, hC, fun f => ?_⟩
  let B := homogeneousYProduct a k ha ha1 hk (homogeneousSchwartzEmbedding a k ha ha1 hk V)
  let L := homogeneousLowEnergy a k ha1 hk
  let W := homogeneousWeightedObservation a k ha ha1 hk V (V.memLp 2)
  refine (homogeneousSchwartzEmbedding_dense a k ha ha1 hk).induction_on
    (p := fun f : HomogeneousY a k => ‖L (B f)‖ ^ 2 ≤ ε * ‖B f‖ ^ 2 + C * ‖W f‖ ^ 2) f ?_ ?_
  · apply isClosed_le <;> fun_prop
  · exact hc

theorem tendsto_homogeneousLowEnergy_schwartzCoefficient (a k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (V : 𝓢(E, ℂ)) (u : ℕ → HomogeneousY a k) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖homogeneousLowEnergy a k ha1 hk
      (homogeneousYProduct a k ha ha1 hk
        (homogeneousSchwartzEmbedding a k ha ha1 hk V) (u n))‖ ^ 2) atTop (𝓝 0) := by
  let B := homogeneousYProduct a k ha ha1 hk (homogeneousSchwartzEmbedding a k ha ha1 hk V)
  let D := ‖B‖ * M
  have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (hu 0)
  have hD : 0 ≤ D := mul_nonneg (norm_nonneg _) hM
  have hn (n : ℕ) : ‖B (u n)‖ ≤ D :=
    (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hu n) (norm_nonneg _))
  have hobs : Tendsto (fun n => ‖homogeneousWeightedObservation a k ha ha1 hk
      V (V.memLp 2) (u n)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [homogeneousWeightedObservation_norm_sq] using
      tendsto_homogeneousPhysical_weighted_L2_of_weakNull a k M ha ha1 hk V (V.memLp 2) u hu hweak
  apply tendsto_order.2
  constructor
  · intro r hr
    exact Filter.Eventually.of_forall (fun n => hr.trans_le (sq_nonneg _))
  · intro ε hε
    let δ := ε / (2 * (D ^ 2 + 1))
    have hδ : 0 < δ := div_pos hε (by positivity)
    obtain ⟨C, _hC, hc⟩ := homogeneousLowEnergy_coefficient_interpolation a k δ ha ha1 hk hδ V
    have hs := (hobs.const_mul C).eventually
      (gt_mem_nhds (show C * 0 < ε / 2 by simpa only [mul_zero] using half_pos hε))
    have hδD : δ * D ^ 2 ≤ ε / 2 := by
      have he : δ * (2 * (D ^ 2 + 1)) = ε := div_mul_cancel₀ _ (by positivity)
      nlinarith [hδ.le]
    filter_upwards [hs] with n hsmall
    have hi := hc (u n)
    have hb := (sq_le_sq₀ (norm_nonneg _) hD).mpr (hn n)
    have hm := mul_le_mul_of_nonneg_left hb hδ.le
    change ‖homogeneousLowEnergy a k ha1 hk (B (u n))‖ ^ 2 < ε
    linarith

end DefocusingNLS

end OAI
