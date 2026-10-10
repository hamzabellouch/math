import OAI.NumberTheory.Ostmann.Quadratic.QuadraticProgressionExtraction

namespace OAI

/-! # The rational approximation forced by the actual quadratic witness

The only hypotheses below are the density energy, compact support, the
explicit large-sum event, and numerical scale bounds. The inverse quadratic
estimate and the progression reduction are proved in the imported modules.
-/

namespace Ostmann

open scoped BigOperators SchwartzMap

noncomputable def quadraticVariationBudget (Φ : 𝓢(ℝ, ℂ)) (B : ℝ) : ℝ :=
  1 + SchwartzMap.seminorm ℝ 0 0 (quadraticSchwartzWeight Φ) +
    SchwartzMap.seminorm ℝ 0 1 (quadraticSchwartzWeight Φ) * (B + 1)

theorem quadraticVariationBudget_one_le (Φ : 𝓢(ℝ, ℂ)) (B : ℝ) (hB : 3 ≤ B) :
    1 ≤ quadraticVariationBudget Φ B := by
  unfold quadraticVariationBudget
  have h₀ : 0 ≤ SchwartzMap.seminorm ℝ 0 0 (quadraticSchwartzWeight Φ) := by positivity
  have h₁ : 0 ≤ SchwartzMap.seminorm ℝ 0 1 (quadraticSchwartzWeight Φ) * (B + 1) := by positivity
  linarith

theorem quadratic_witness_large_progression {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0)
    (henergy : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q)
    (a : ZMod q) (h₀ s v : ℕ) (θ R B K : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) (hB : 3 ≤ B)
    (hY : 1 ≤ Real.sqrt (R / ((s : ℝ) * v * q)))
    (hΦ : ∀ x : ℝ, B ^ 2 < x → Φ x = 0)
    (hlarge : Real.sqrt ((2 : ℝ) ^ q.primeFactors.card) * Real.exp (-K) <
      ‖positiveQuadraticSum g a ((h₀ : ℝ) + θ) Φ R v s‖) :
    ∃ r : ℕ, 0 < r ∧ r ≤ q ∧
      let Y := Real.sqrt (R / ((s : ℝ) * v * q))
      let N := (⌊B * q * Y⌋₊ + q - r) / q
      Y ≤ (N : ℝ) ∧ (N : ℝ) ≤ (B + 1) * Y ∧
      Y * Real.exp (-K) / 2 < ‖∑ j ∈ Finset.range N,
        Φ ((((j : ℝ) + (r : ℝ) / q) / Y) ^ 2) *
          realQuadraticPhase (((s * v * q : ℕ) : ℝ) * θ) (2 * θ * s * v * r) j‖ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hYpos : 0 < Real.sqrt (R / ((s : ℝ) * v * q)) := by linarith
  apply positiveQuadraticSum_large_progression g hg henergy a h₀ s v θ R B
    (Real.sqrt (R / ((s : ℝ) * v * q)) * Real.exp (-K) / 2) Φ
    hs hv hR hB hY (by positivity) hΦ
  rw [quadratic_normalizer_progression_scale q s v R (NeZero.pos q) hs hv hR]
  have hpow : Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1)) ≤
      2 * Real.sqrt ((2 : ℝ) ^ q.primeFactors.card) := by
    rw [pow_succ, Real.sqrt_mul (by positivity)]
    have htwo : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    nlinarith [Real.sqrt_nonneg ((2 : ℝ) ^ q.primeFactors.card)]
  calc
    _ ≤ (q * Real.sqrt (R / ((s : ℝ) * v * q))) *
        (Real.sqrt ((2 : ℝ) ^ q.primeFactors.card) * Real.exp (-K)) := by
      have hh := mul_le_mul_of_nonneg_right hpow
        (show 0 ≤ (q : ℝ) * Real.sqrt (R / ((s : ℝ) * v * q)) * Real.exp (-K) / 2 by positivity)
      nlinarith
    _ < _ := mul_lt_mul_of_pos_left hlarge (mul_pos hqR hYpos)

theorem positiveQuadraticSum_phase_witness {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0)
    (henergy : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q)
    (a : ZMod q) (h₀ s v Amax : ℕ) (θ R B K : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) (hB : 3 ≤ B) (hK : 0 ≤ K)
    (hY : 1 ≤ Real.sqrt (R / ((s : ℝ) * v * q)))
    (hΦ : ∀ x : ℝ, B ^ 2 < x → Φ x = 0)
    (hlarge : Real.sqrt ((2 : ℝ) ^ q.primeFactors.card) * Real.exp (-K) <
      ‖positiveQuadraticSum g a ((h₀ : ℝ) + θ) Φ R v s‖)
    (hscale : let Y := Real.sqrt (R / ((s : ℝ) * v * q))
      let δ := Real.exp (-K) / (4 * quadraticVariationBudget Φ B * (B + 1))
      512 * (1 + 2 * Real.log ((B + 1) * Y)) ≤ δ ^ 3 * Y)
    (hA : 1024 * ((s * v * q : ℕ) : ℝ) /
      (Real.exp (-K) / (4 * quadraticVariationBudget Φ B * (B + 1))) ^ 2 ≤ Amax) :
    ∃ c ∈ Finset.Icc 1 Amax, ∃ b : ℤ,
      |(c : ℝ) * θ - b| ≤
        1024 * (1 + 2 * Real.log ((B + 1) * Real.sqrt (R / ((s : ℝ) * v * q)))) /
          ((Real.exp (-K) / (4 * quadraticVariationBudget Φ B * (B + 1))) ^ 4 *
            (Real.sqrt (R / ((s : ℝ) * v * q))) ^ 2) := by
  let Y := Real.sqrt (R / ((s : ℝ) * v * q))
  let D := quadraticVariationBudget Φ B
  let δ := Real.exp (-K) / (4 * D * (B + 1))
  have hD : 1 ≤ D := quadraticVariationBudget_one_le Φ B hB
  have hDpos : 0 < D := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    have he : Real.exp (-K) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    dsimp [δ]
    apply (div_le_one (by positivity)).mpr
    nlinarith
  have hYpos : 0 < Y := by dsimp [Y]; linarith
  obtain ⟨r, hr, hrq, hNlo, hNhi, hsum⟩ := quadratic_witness_large_progression
    g hg henergy a h₀ s v θ R B K Φ hs hv hR hB hY hΦ hlarge
  let N := (⌊B * q * Y⌋₊ + q - r) / q
  let w := fun j : ℕ => Φ ((((j : ℝ) + (r : ℝ) / q) / Y) ^ 2)
  have hNpos : (0 : ℝ) < N := hYpos.trans_le hNlo
  have hN : 0 < N := by exact_mod_cast hNpos
  have hlog : Real.log (N : ℝ) ≤ Real.log ((B + 1) * Y) :=
    Real.log_le_log hNpos hNhi
  have hscaleN : 512 * (1 + 2 * Real.log (N : ℝ)) ≤ δ ^ 3 * N := by
    have hh := mul_le_mul_of_nonneg_left hNlo (show 0 ≤ δ ^ 3 by positivity)
    dsimp only at hscale
    change 512 * (1 + 2 * Real.log ((B + 1) * Y)) ≤ δ ^ 3 * Y at hscale
    linarith
  have hvar : discreteVariation w N ≤ D := by
    apply (quadratic_progression_weight_variation q s v r N R (B + 1) Φ
      (NeZero.pos q) hs hv hR hNhi).trans
    dsimp [D, quadraticVariationBudget]
    linarith
  have hweighted : discreteVariation w N * (δ * N) <
      ‖∑ j ∈ Finset.range N, w j *
        realQuadraticPhase (((s * v * q : ℕ) : ℝ) * θ) (2 * θ * s * v * r) j‖ := by
    have heq : D * (δ * ((B + 1) * Y)) = Y * Real.exp (-K) / 4 := by
      dsimp [δ]
      field_simp
    have hh := mul_le_mul_of_nonneg_left hNhi (show 0 ≤ D * δ by positivity)
    have hvv := mul_le_mul_of_nonneg_right hvar (show 0 ≤ δ * (N : ℝ) by positivity)
    change Y * Real.exp (-K) / 2 < _ at hsum
    calc
      _ ≤ D * (δ * ((B + 1) * Y)) := by nlinarith
      _ = Y * Real.exp (-K) / 4 := heq
      _ < Y * Real.exp (-K) / 2 := by nlinarith [mul_pos hYpos (Real.exp_pos (-K))]
      _ < _ := hsum
  obtain ⟨c, hc, b, hab⟩ := weighted_quadratic_phase_witness w (2 * θ * s * v * r) δ
    N (s * v * q) Amax θ hN (Nat.mul_pos (Nat.mul_pos hs hv) (NeZero.pos q))
    hδ hδ1 hscaleN hweighted hA
  refine ⟨c, hc, b, hab.trans ?_⟩
  have hnum : 0 ≤ 1024 * (1 + 2 * Real.log ((B + 1) * Y)) := by
    have hlog0 : 0 ≤ Real.log ((B + 1) * Y) := Real.log_nonneg (by nlinarith [hY])
    positivity
  calc
    _ ≤ 1024 * (1 + 2 * Real.log ((B + 1) * Y)) / (δ ^ 4 * (N : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left hnum (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hYpos.le hNlo 2) (by positivity))

end Ostmann

end OAI
