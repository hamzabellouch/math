import OAI.Analysis.CircleDomains.Probability.FatouSelection
import OAI.Analysis.CircleDomains.Transfer.ReciprocalGridSelection

namespace OAI

/-!
# Fixing grid shifts before the staircase width

The wedge costs depend on a sequence of widths, whereas the terminal
cost depends only on the grid shifts. Fatou selection provides one
compatible choice of shifts with small terminal cost and arbitrarily
late small wedge costs. Thus subsequent collar conditions may impose
any finite lower bound on the width-sequence index.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace CircleDomainRigidity.FiniteTransfer

/-- The real-valued version of the Fatou selection estimate, with the
two costs normalized by their actual thresholds. -/
theorem exists_compatible_frequently_small_real_pair
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (W : ℕ → X → ℝ) (J : X → ℝ) {P : X → Prop} {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B)
    (hWi : ∀ k, Integrable (W k) μ) (hJi : Integrable J μ)
    (hW0 : ∀ k, ∀ᵐ x ∂μ, 0 ≤ W k x) (hJ0 : ∀ᵐ x ∂μ, 0 ≤ J x)
    (hP : ∀ᵐ x ∂μ, P x)
    (hWmean : ∀ k, (∫ x, W k x ∂μ) < A / 4)
    (hJmean : (∫ x, J x ∂μ) < B / 4) :
    ∃ x, P x ∧ J x < B ∧ ∃ᶠ k in atTop, W k x < A := by
  let U : ℕ → X → ℝ≥0∞ := fun k x => ENNReal.ofReal (W k x / A)
  let V : X → ℝ≥0∞ := fun x => ENNReal.ofReal (J x / B)
  have hU k : AEMeasurable (U k) μ :=
    ((hWi k).div_const A).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hV : AEMeasurable V μ :=
    (hJi.div_const B).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hmean k : (∫⁻ x, U k x + V x ∂μ) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [lintegral_add_left' (hU k)]
    have hWu : (∫⁻ x, U k x ∂μ) = ENNReal.ofReal ((∫ x, W k x ∂μ) / A) := by
      dsimp [U]
      rw [← ofReal_integral_eq_lintegral_ofReal ((hWi k).div_const A)
        ((hW0 k).mono (fun _ hx => div_nonneg hx hA.le)), integral_div]
    have hJv : (∫⁻ x, V x ∂μ) = ENNReal.ofReal ((∫ x, J x ∂μ) / B) := by
      dsimp [V]
      rw [← ofReal_integral_eq_lintegral_ofReal (hJi.div_const B)
        (hJ0.mono (fun _ hx => div_nonneg hx hB.le)), integral_div]
    rw [hWu, hJv, ← ENNReal.ofReal_add
      (div_nonneg (integral_nonneg_of_ae (hW0 k)) hA.le)
      (div_nonneg (integral_nonneg_of_ae hJ0) hB.le)]
    apply ENNReal.ofReal_le_ofReal
    have hWlt : (∫ x, W k x ∂μ) / A < 1 / 4 :=
      (div_lt_iff₀ hA).mpr (by linarith [hWmean k])
    have hJlt : (∫ x, J x ∂μ) / B < 1 / 4 :=
      (div_lt_iff₀ hB).mpr (by linarith [hJmean])
    linarith
  obtain ⟨x, hxP, hxJ, hxW⟩ := exists_compatible_frequently_small_pair U V hU hV hP
    (ENNReal.ofReal_lt_one.mpr (by norm_num : (1 / 2 : ℝ) < 1)) hmean
  refine ⟨x, hxP, ?_, ?_⟩
  · exact (div_lt_one hB).mp (ENNReal.ofReal_lt_one.mp hxJ)
  · exact hxW.mono (fun k hk => (div_lt_one hA).mp (ENNReal.ofReal_lt_one.mp hk))

/-- Simultaneous choice of reciprocal grid spacing and fixed shifts,
retaining any conull compatibility event and arbitrarily late good
width indices. The terminal cost includes all compulsory indices. -/
theorem exists_reciprocal_grid_with_frequently_small_widths {n : ℕ}
    (W : ℕ → ℕ → (Fin n → ℝ) → ℝ) (J : ℕ → (Fin n → ℝ) → ℝ)
    (P : ℕ → (Fin n → ℝ) → Prop) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hWi : ∀ N k, Integrable (W N k) (reciprocalGridLaw n N))
    (hJi : ∀ N, Integrable (J N) (reciprocalGridLaw n N))
    (hW0 : ∀ N k, ∀ᵐ θ ∂reciprocalGridLaw n N, 0 ≤ W N k θ)
    (hJ0 : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, 0 ≤ J N θ)
    (hP : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, P N θ)
    (hWmean : ∀ᶠ N in atTop, ∀ k,
      (∫ θ, W N k θ ∂reciprocalGridLaw n N) < η / 4)
    (hJmean : Tendsto
      (fun N => reciprocalGridStep N ^ 2 * (∫ θ, J N θ ∂reciprocalGridLaw n N))
      atTop (𝓝 0)) :
    ∃ (N : ℕ) (θ : Fin n → ℝ), reciprocalGridStep N < δ ∧ P N θ ∧
      reciprocalGridStep N * Real.sqrt (J N θ) < η ∧
      ∃ᶠ k in atTop, W N k θ < η := by
  have hsmall : ∀ᶠ N in atTop,
      reciprocalGridStep N < δ ∧
      (∀ k, (∫ θ, W N k θ ∂reciprocalGridLaw n N) < η / 4) ∧
      reciprocalGridStep N ^ 2 * (∫ θ, J N θ ∂reciprocalGridLaw n N) < η ^ 2 / 4 := by
    filter_upwards [reciprocalGridStep_tendsto_zero.eventually_lt_const hδ, hWmean,
      hJmean.eventually_lt_const (by positivity : 0 < η ^ 2 / 4)] with N hN hW hJ
    exact ⟨hN, hW, hJ⟩
  obtain ⟨N, hN, hW, hJ⟩ := hsmall.exists
  let := reciprocalGridLaw_isProbabilityMeasure n N
  let C : (Fin n → ℝ) → ℝ := fun θ => reciprocalGridStep N ^ 2 * J N θ
  have hCi : Integrable C (reciprocalGridLaw n N) := (hJi N).const_mul _
  have hC0 : ∀ᵐ θ ∂reciprocalGridLaw n N, 0 ≤ C θ :=
    (hJ0 N).mono (fun _ hx => mul_nonneg (sq_nonneg _) hx)
  have hCmean : (∫ θ, C θ ∂reciprocalGridLaw n N) < η ^ 2 / 4 := by
    simpa only [C, integral_const_mul] using hJ
  obtain ⟨θ, hθ, hθC, hθW⟩ := exists_compatible_frequently_small_real_pair
    (W N) C hη (sq_pos_of_pos hη) (hWi N) hCi (hW0 N) hC0
    ((hP N).and (hJ0 N)) hW hCmean
  refine ⟨N, θ, hN, hθ.1, ?_, hθW⟩
  have hsquare : (reciprocalGridStep N * Real.sqrt (J N θ)) ^ 2 < η ^ 2 := by
    rwa [mul_pow, Real.sq_sqrt hθ.2]
  exact (sq_lt_sq₀
    (mul_nonneg (reciprocalGridStep_pos N).le (Real.sqrt_nonneg _)) hη.le).mp hsquare

end CircleDomainRigidity.FiniteTransfer

end OAI
