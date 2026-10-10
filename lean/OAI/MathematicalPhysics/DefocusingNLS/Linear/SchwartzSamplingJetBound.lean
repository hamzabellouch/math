import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSamplingBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSymbolBound

namespace OAI

/-! # Finite physical jet control of expanding-torus sampling

A fixed finite set of physical Schwartz derivatives controls every sampled
vector, uniformly for all periods `L ≥ 1`.  The test function may vary with L.
-/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private noncomputable def samplingDecaySeminorm : Seminorm ℝ 𝓢(E, ℂ) :=
  (Finset.Iic (12, 0)).sup (schwartzSeminormFamily ℝ E ℂ)

private theorem samplingDecaySeminorm_continuous : Continuous samplingDecaySeminorm :=
  Seminorm.continuous_finsetSup fun p _ =>
    (schwartz_withSeminorms ℝ E ℂ).continuous_seminorm p

private theorem decay_le_samplingDecaySeminorm (K : 𝓢(E, ℂ)) (x : E) :
    (1 + ‖x‖) ^ (12 : ℕ) * ‖K x‖ ≤ 2 ^ (12 : ℕ) * samplingDecaySeminorm K := by
  simpa only [samplingDecaySeminorm, schwartzSeminormFamily, norm_iteratedFDeriv_zero]
    using! SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (12, 0)) (k := 12) (n := 0) (by decide) (by decide) K x

theorem exists_schwartzTorusSample_physicalJet_bound (a k : ℝ)
    (ha1 : a < 1) (hk : 8 < k) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (ψ : 𝓢(E, ℂ)) (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ x : E, (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n ψ x‖ ≤ D) →
      ∀ (L : ℝ) (hL : 1 ≤ L),
        ‖schwartzTorusSample a k L ha1 hk hL (radianFourierKernel ψ)‖ ≤ C * D := by
  let W (s : ℝ) : 𝓢(E, ℂ) →L[ℝ] 𝓢(E, ℂ) :=
    SchwartzMap.smulLeftCLM ℂ (fun x : E => (1 + ‖x‖ ^ 2) ^ (s / 2))
  let T₀ := (W (6 - a)).comp (radianFourierCLM.restrictScalars ℝ)
  let T₁ := (W k).comp (radianFourierCLM.restrictScalars ℝ)
  let q : Seminorm ℝ 𝓢(E, ℂ) :=
    samplingDecaySeminorm.comp T₀.toLinearMap + samplingDecaySeminorm.comp T₁.toLinearMap
  have hq : Continuous q :=
    (samplingDecaySeminorm_continuous.comp T₀.continuous).add
      (samplingDecaySeminorm_continuous.comp T₁.continuous)
  obtain ⟨S, C, _, hC⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ E ℂ) q hq
  let N := S.sup (fun p : ℕ × ℕ => max p.1 p.2)
  let B := Real.sqrt (2 * ((2 * Real.pi) ^ (12 : ℕ))⁻¹ *
    (1 + 2 * Real.pi) ^ (12 : ℕ))
  refine ⟨N, B * 2 ^ (12 : ℕ) * C, by dsimp [B]; positivity, ?_⟩
  intro ψ D hD hjet L hL
  have hsemi : ∀ p ∈ S, schwartzSeminormFamily ℝ E ℂ p ψ ≤ D := by
    intro p hp
    have hpN : max p.1 p.2 ≤ N :=
      Finset.le_sup (f := fun p : ℕ × ℕ => max p.1 p.2) hp
    have hi : p.1 ≤ N := (le_max_left _ _).trans hpN
    have hn : p.2 ≤ N := (le_max_right _ _).trans hpN
    apply SchwartzMap.seminorm_le_bound ℝ p.1 p.2 ψ hD
    intro x
    have hweight : ‖x‖ ^ p.1 ≤ (1 + ‖x‖) ^ N := by
      calc
        _ ≤ (1 + ‖x‖) ^ p.1 := pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
        _ ≤ _ := pow_le_pow_right₀ (by linarith [norm_nonneg x]) hi
    exact (mul_le_mul_of_nonneg_right hweight (norm_nonneg _)).trans (hjet p.2 hn x)
  have hsup : S.sup (schwartzSeminormFamily ℝ E ℂ) ψ ≤ D :=
    Seminorm.finset_sup_apply_le hD hsemi
  have hqD : q ψ ≤ C * D :=
    (hC ψ).trans (mul_le_mul_of_nonneg_left hsup C.coe_nonneg)
  have hb : ∀ s ∈ ({6 - a, k} : Set ℝ), ∀ x : E,
      (1 + ‖x‖) ^ (12 : ℕ) *
        ‖weightedSchwartzKernel s (radianFourierKernel ψ) x‖ ≤
          2 ^ (12 : ℕ) * ((C : ℝ) * D) := by
    intro s hs x
    have hsbound : samplingDecaySeminorm
        (weightedSchwartzKernel s (radianFourierKernel ψ)) ≤ q ψ := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · change samplingDecaySeminorm (T₀ ψ) ≤
          samplingDecaySeminorm (T₀ ψ) + samplingDecaySeminorm (T₁ ψ)
        exact le_add_of_nonneg_right (apply_nonneg _ _)
      · change samplingDecaySeminorm (T₁ ψ) ≤
          samplingDecaySeminorm (T₀ ψ) + samplingDecaySeminorm (T₁ ψ)
        exact le_add_of_nonneg_left (apply_nonneg _ _)
    exact (decay_le_samplingDecaySeminorm _ x).trans
      (mul_le_mul_of_nonneg_left (hsbound.trans hqD) (by positivity))
  have h := schwartzTorusSample_norm_le_of_weighted_decay a k ha1 hk
    (radianFourierKernel ψ) (2 ^ (12 : ℕ) * ((C : ℝ) * D)) (by positivity) hb L hL
  dsimp only [B] at ⊢
  convert h using 1; ring

end DefocusingNLS

end OAI
