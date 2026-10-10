import OAI.NumberTheory.JointDickman.Amplification.TailViolationSum

namespace OAI

/-! # Vanishing mass discarded by the coefficient regularity cutoff -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def regularityRemainder (B L : ℕ) : ℝ :=
  (2 * (L : ℝ) * B + (B : ℝ)^2) / (B : ℝ)^10

theorem regularityRemainder_nonneg (B L : ℕ) : 0 ≤ regularityRemainder B L := by
  unfold regularityRemainder
  positivity

theorem regularityRemainder_tendsto (L : ℕ) :
    Tendsto (fun B => regularityRemainder B L) atTop (𝓝 0) := by
  have h₉ : Tendsto (fun B : ℕ => (2 * (L : ℝ)) / (B : ℝ)^9) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by norm_num : (9 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop)
  have h₈ : Tendsto (fun B : ℕ => (1 : ℝ) / (B : ℝ)^8) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by norm_num : (8 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun B : ℕ => (2 * (L : ℝ)) / (B : ℝ)^9 + (1 : ℝ) / (B : ℝ)^8) atTop (𝓝 0) := by
    simpa using h₉.add h₈
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with B hB
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
  unfold regularityRemainder
  field_simp [hB0]

open Classical in
noncomputable def discardedCoefficientWeight (B L j b d : ℕ) (τ C : ℝ) : ℝ :=
  if ∀ k : Fin 3, RegularPrimeSet B L τ C (coefficientPrimeSet B (coefficientForm k j b d))
  then 0 else tripleCoefficientWeight B j b d

theorem discardedCoefficientWeight_le (B L j b d : ℕ) (τ C : ℝ)
    (hC : 0 ≤ C) (hlog : 1 ≤ Real.log (auxiliaryCutoff B)) :
    discardedCoefficientWeight B L j b d τ C ≤ ∑ k : Fin 3,
      (prefixViolationMass B L τ (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d) +
        tailViolationMass B C (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d)) := by
  classical
  have hw := tripleCoefficientWeight_nonneg B j b d
  have hn (k : Fin 3) := add_nonneg
    (prefixViolationMass_nonneg B L τ (coefficientPrimeSet B (coefficientForm k j b d)) hw)
    (tailViolationMass_nonneg B C (coefficientPrimeSet B (coefficientForm k j b d)) hw)
  unfold discardedCoefficientWeight
  split_ifs with h
  · exact sum_nonneg (fun k _ => hn k)
  · obtain ⟨k, hk⟩ := not_forall.mp h
    exact (regularity_failure_union_bound _ hC hlog hw hk).trans
      (single_le_sum (fun i _ => hn i) (mem_univ k))

/-- The positive-slope rectangle form of manuscript (9). Its error sequence
is independent of the tail cutoff, slope, and rectangle location. -/
theorem coefficient_regularity_loss
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {δ : ℝ} (hδ : 0 < δ) (hδ32 : δ ≤ 32) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (j l₁ r₁ l₂ r₂ : ℕ),
          0 ≤ C → j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
          Real.exp (δ * B) ≤ (r₁ : ℝ) - l₁ → Real.exp (δ * B) ≤ (r₂ : ℝ) - l₂ →
          (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, discardedCoefficientWeight B L j b d τ C) ≤
            K * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j *
              (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  classical
  obtain ⟨Cp, hCp, hp⟩ := coefficient_prefix_sum_bound hFord hM hδ
  obtain ⟨Ct, hCt, ht⟩ := coefficient_tail_sum_bound hFord hM hδ
  obtain ⟨D, hD, htail⟩ := actual_tail_chernoff_sum hM (by linarith : 0 < δ / 8)
    (by linarith : δ / 8 ≤ 4)
  let K₀ := Cp + Ct * D + 1
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  refine ⟨3 * K₀, by positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨s, hs, hs1, he, hen, hprefix⟩ := prefixGridError_tendsto hM hτ
  let ε := fun B => prefixGridError B L (δ / 8) τ s + regularityRemainder B L
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (hprefix L (δ / 8) hL (by linarith) (by linarith)).add
      (regularityRemainder_tendsto L)
  refine ⟨ε, fun B => add_nonneg (prefixGridError_nonneg ..) (regularityRemainder_nonneg ..), hε, ?_⟩
  have hloglarge : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [sieveCutoff_eventually (by linarith : 0 < δ / 8), htail,
    auxiliaryLogLength_between, coefficient_rectangle_remainder_power hδ,
    hloglarge, eventually_gt_atTop 1] with B hcut htailB hℓ hrem hlog hB
  intro C j l₁ r₁ l₂ r₂ hC hj hI hJ hlen₁ hlen₂
  let A := ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j
  let E := coefficientRectangleRemainder B (sieveCutoff (δ / 8) B) l₁ r₁ l₂ r₂
  have hlen₁0 : 0 ≤ (r₁ : ℝ) - l₁ := (Real.exp_pos _).le.trans hlen₁
  have hlen₂0 : 0 ≤ (r₂ : ℝ) - l₂ := (Real.exp_pos _).le.trans hlen₂
  have hsig := singularFactor_one_le (by norm_num : (0 : ℝ) ≤ 24) j
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hlen₁0 hlen₂0) (by linarith)
  have hCpA : 0 ≤ Cp * A := mul_nonneg hCp.le hA
  have hCtA : 0 ≤ Ct * A := mul_nonneg hCt.le hA
  have hremE : (2 * (L : ℝ) * B + (B : ℝ)^2) * E ≤ A * regularityRemainder B L := by
    have hE : E ≤ (((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂)) / (B : ℝ)^10 := hrem _ _ hlen₁ hlen₂
    have hprod : ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) ≤ A :=
      le_mul_of_one_le_right (mul_nonneg hlen₁0 hlen₂0) hsig
    have hdiv := div_le_div_of_nonneg_right hprod (by positivity : (0 : ℝ) ≤ (B : ℝ)^10)
    have hh := mul_le_mul_of_nonneg_left (hE.trans hdiv)
      (by positivity : (0 : ℝ) ≤ 2 * (L : ℝ) * B + (B : ℝ)^2)
    simpa only [regularityRemainder, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  have htail' := htailB (activeTailIndices B) C (fun i hi => (mem_filter.mp hi).2.le)
  have hsingle (k : Fin 3) :
      (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂,
        (prefixViolationMass B L τ (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d) +
        tailViolationMass B C (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d))) ≤
      K₀ * A * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
    have hpb := hp B j l₁ r₁ l₂ r₂ hB hcut.1 hcut.2.1
      (by linarith only [hcut.2.2.1]) hj hI hJ k L τ s hL hτ.le hs
        (by linarith only [hs1]) he hen hℓ.1 hℓ.2
    have htb := ht B j l₁ r₁ l₂ r₂ hB hcut.1 hcut.2.1
      (by linarith only [hcut.2.2.1]) hj hI hJ hlog k C hC
    have hsum := add_le_add hpb htb
    simp_rw [← sum_add_distrib] at hsum
    have htb' := mul_le_mul_of_nonneg_left htail' hCtA
    have hmain :
        Cp * A * prefixGridError B L (δ / 8) τ s +
        Ct * A * (∑ i ∈ activeTailIndices B, tailChernoffFactor B i (δ / 8) C) +
        (2 * (L : ℝ) * B + (B : ℝ)^2) * E ≤
        Cp * A * prefixGridError B L (δ / 8) τ s +
        (Ct * D) * A * Real.exp (-(1 / 10 : ℝ) * C) + A * regularityRemainder B L := by
      nlinarith only [htb', hremE]
    have hCpK : Cp ≤ K₀ := by dsimp [K₀]; linarith only [mul_pos hCt hD]
    have hCtK : Ct * D ≤ K₀ := by dsimp [K₀]; linarith only [hCp]
    have h1K : 1 ≤ K₀ := by dsimp [K₀]; linarith only [hCp, mul_pos hCt hD]
    have h₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCpK hA)
      (prefixGridError_nonneg B L (δ / 8) τ s)
    have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCtK hA)
      (Real.exp_pos (-(1 / 10 : ℝ) * C)).le
    have h₃ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1K hA)
      (regularityRemainder_nonneg B L)
    have hfinal := add_le_add (add_le_add h₁ h₂) h₃
    calc
      _ ≤ Cp * A * prefixGridError B L (δ / 8) τ s +
          Ct * A * (∑ i ∈ activeTailIndices B, tailChernoffFactor B i (δ / 8) C) +
          (2 * (L : ℝ) * B + (B : ℝ)^2) * E := by
        convert hsum using 1
        dsimp [A, E]
        ring
      _ ≤ _ := hmain
      _ ≤ K₀ * A * prefixGridError B L (δ / 8) τ s +
          K₀ * A * Real.exp (-(1 / 10 : ℝ) * C) + K₀ * A * regularityRemainder B L := by
        simpa only [one_mul] using hfinal
      _ = K₀ * A * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by dsimp only [ε]; ring
  calc
    _ ≤ ∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, ∑ k : Fin 3,
        (prefixViolationMass B L τ (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d) +
        tailViolationMass B C (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d)) :=
      sum_le_sum (fun b _ => sum_le_sum (fun d _ => discardedCoefficientWeight_le B L j b d τ C hC hlog))
    _ = ∑ k : Fin 3, ∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂,
        (prefixViolationMass B L τ (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d) +
        tailViolationMass B C (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d)) := by
      rw [show (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, ∑ k : Fin 3, _) =
        ∑ b ∈ Ico l₁ r₁, ∑ k : Fin 3, ∑ d ∈ Ico l₂ r₂, _ from
          sum_congr rfl (fun _ _ => sum_comm)]
      exact sum_comm
    _ ≤ ∑ _k : Fin 3, K₀ * A * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) :=
      sum_le_sum (fun k _ => hsingle k)
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; dsimp [A]; ring

end JointDickman

end OAI
