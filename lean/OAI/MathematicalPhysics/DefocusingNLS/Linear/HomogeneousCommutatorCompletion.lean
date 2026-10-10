import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousTopCommutator
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSchwartzCommutator

namespace OAI

/-! # Completing the compact commutator in the input variable

Approximation in the actual Y norm transfers the Schwartz result to every
bounded weakly null sequence, without an additional compactness hypothesis.
-/

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem schwartzLp2_norm_sq (f : 𝓢(E, ℂ)) :
    ‖f.toLp 2 volume‖ ^ 2 = ∫ x : E, ‖f x‖ ^ 2 := by
  have h := real_inner_self_eq_norm_sq (f.toLp 2 volume)
  rw [L2.inner_def] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [SchwartzMap.coeFn_toLp f 2 volume] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem tendsto_homogeneousTopCommutator_Schwartz_input (a M : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (j : Fin (N + 1) → Fin 12) (V : 𝓢(E, ℂ)) (f : ℕ → 𝓢(E, ℂ))
    (hf : ∀ n, ‖homogeneousSchwartzEmbedding a ((N + 1 : ℕ) : ℝ) ha ha1 hk (f n)‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a ((N + 1 : ℕ) : ℝ) →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (homogeneousSchwartzEmbedding a ((N + 1 : ℕ) : ℝ) ha ha1 hk (f n)))
        atTop (𝓝 0)) :
    Tendsto (fun n => homogeneousTopCommutator a (N + 1) ha ha1 hk j
      (homogeneousSchwartzEmbedding a ((N + 1 : ℕ) : ℝ) ha ha1 hk V)
      (homogeneousSchwartzEmbedding a ((N + 1 : ℕ) : ℝ) ha ha1 hk (f n))) atTop (𝓝 0) := by
  have ht := tendsto_homogeneousSchwartzCommutator_physicalL2 a M N ha ha1 hk j V f hf hweak
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, homogeneousTopCommutator_Schwartz, ← schwartzLp2_norm_sq,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs

theorem tendsto_homogeneousTopCommutator_Schwartz_coefficient (a M : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (j : Fin (N + 1) → Fin 12) (V : 𝓢(E, ℂ))
    (u : ℕ → HomogeneousY a ((N + 1 : ℕ) : ℝ)) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a ((N + 1 : ℕ) : ℝ) →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => homogeneousTopCommutator a (N + 1) ha ha1 hk j
      (homogeneousSchwartzEmbedding a ((N + 1 : ℕ) : ℝ) ha ha1 hk V) (u n)) atTop (𝓝 0) := by
  let S := homogeneousSchwartzEmbedding a ((N + 1 : ℕ) : ℝ) ha ha1 hk
  have hd := homogeneousSchwartzEmbedding_dense a ((N + 1 : ℕ) : ℝ) ha ha1 hk
  have hchoose (n : ℕ) : ∃ f : 𝓢(E, ℂ), dist (u n) (S f) < 1 / ((n : ℝ) + 1) :=
    hd.exists_dist_lt (u n) (by positivity)
  choose f hf using hchoose
  have herrBound (n : ℕ) : ‖S (f n) - u n‖ ≤ 1 / ((n : ℝ) + 1) := by
    simpa only [dist_eq_norm, norm_sub_rev] using (hf n).le
  have herr : Tendsto (fun n => S (f n) - u n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) herrBound
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hfb (n : ℕ) : ‖S (f n)‖ ≤ M + 1 := by
    have hδ : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    calc
      _ ≤ ‖S (f n) - u n‖ + ‖u n‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + M := add_le_add ((herrBound n).trans hδ) (hu n)
      _ = _ := add_comm _ _
  have hfw (ℓ : HomogeneousY a ((N + 1 : ℕ) : ℝ) →L[ℝ] ℂ) :
      Tendsto (fun n => ℓ (S (f n))) atTop (𝓝 0) := by
    have h := (ℓ.continuous.continuousAt.tendsto.comp herr).add (hweak ℓ)
    simpa only [Function.comp_apply, map_sub, map_zero, sub_add_cancel, add_zero] using h
  let T := homogeneousTopCommutator a (N + 1) ha ha1 hk j (S V)
  have hs := tendsto_homogeneousTopCommutator_Schwartz_input a (M + 1) N ha ha1 hk j V f hfb hfw
  have he := T.continuous.continuousAt.tendsto.comp herr
  have h := hs.sub he
  simpa only [T, S, Function.comp_apply, map_sub, map_zero, sub_sub_cancel, sub_zero] using h

end DefocusingNLS

end OAI
