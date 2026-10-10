import OAI.NumberTheory.Ostmann.Characters.PolynomialWeightPair
import OAI.NumberTheory.Ostmann.Construction.OneSidedCauchy

namespace OAI

/-! # The one-sided estimate for the actual polynomial amplitude family -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem polynomial_one_sided_bound (Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (χ : ∀ q : Q, DirichletCharacter ℂ (q : ℕ)) (hnonprincipal : ∀ q, χ q ≠ 1)
    (a M K : ℕ) (ha : 0 < a) (hM : ∀ q : Q, M.Coprime (q : ℕ))
    {n t : ℕ} (F : Q → Fin n → ClippedPolynomialFactor)
    (H : Q → Fin t → Polynomial ℝ) (keep : Q → (Fin t → Bool) → Bool)
    (B : ℝ) (R Bq : ℕ) (hB : 0 ≤ B)
    (hbudget : ∀ q, smoothPolynomialBudget (F q) ≤ B)
    (hcomplexity : ∀ q, polynomialWeightComplexity (F q) (H q) ≤ R)
    (hBq : ∀ q : Q, (q : ℕ) ≤ Bq)
    (μ : Fin (K * M) → ℝ) (ν : Q → ℝ) (U : Fin (K * M) → ℂ) (V : Q → ℂ)
    (C α : ℝ) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hμ : ∀ j, 0 ≤ μ j) (hmassμ : ∑ j, μ j ≤ 1)
    (hdom : ∀ j, μ j ≤ C * ((a + j.val : ℕ) : ℝ)⁻¹)
    (hν : ∀ q, 0 ≤ ν q) (hmassν : ∑ q, ν q ≤ 1) (hatom : ∀ q, ν q ≤ α)
    (hU : ∀ j, ‖U j‖ ≤ 1) (hV : ∀ q, ‖V q‖ ≤ 1) :
    ‖∑ j, (μ j : ℂ) * (U j * ∑ q : Q, (ν q : ℂ) * V q *
      (χ q ((a + j.val : ℕ) : ZMod (q : ℕ)) *
        polynomialAmplitude (F q) (H q) (keep q) ((a + j.val : ℕ) : ℝ)))‖ ^ 2 ≤
      C * (α * (((K * M : ℕ) : ℝ) / a * B ^ 2) +
        (M : ℝ) * ((3 ^ (2 * R) : ℕ) * (2 * (a : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2) := by
  let η : Fin (K * M) → ℝ := fun j => ((a + j.val : ℕ) : ℝ)⁻¹
  let G : Q → Fin (K * M) → ℂ := fun q j =>
    χ q ((a + j.val : ℕ) : ZMod (q : ℕ)) *
      polynomialAmplitude (F q) (H q) (keep q) ((a + j.val : ℕ) : ℝ)
  have hη (j : Fin (K * M)) : 0 ≤ η j := by dsimp [η]; positivity
  have hηatom (j : Fin (K * M)) : η j ≤ (a : ℝ)⁻¹ := by
    apply inv_anti₀ (by exact_mod_cast ha)
    exact_mod_cast Nat.le_add_right a j.val
  have hηmass : ∑ j, η j ≤ ((K * M : ℕ) : ℝ) / a := by
    calc
      _ ≤ ∑ _j : Fin (K * M), (a : ℝ)⁻¹ := Finset.sum_le_sum (fun j _ => hηatom j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]
  have hG (q : Q) (j : Fin (K * M)) : ‖G q j‖ ≤ B := by
    change ‖χ q _ * polynomialAmplitude (F q) (H q) (keep q) _‖ ≤ B
    rw [norm_mul]
    exact (mul_le_mul ((χ q).norm_le_one _) ((polynomialAmplitude_norm (F q) (H q) (keep q) _).trans
      (hbudget q)) (norm_nonneg _) (by norm_num)).trans_eq (one_mul B)
  apply one_sided_cauchy_of_offdiagonal μ η ν U V G C α (((K * M : ℕ) : ℝ) / a) B
    ((M : ℝ) * ((3 ^ (2 * R) : ℕ) * (2 * (a : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2)
    hC hα (by positivity) (by positivity) hμ hmassμ hdom hη hηmass hν hmassν hatom hU hV hG
  intro q r hqr
  have : NeZero (q : ℕ) := ⟨(hprime q q.property).ne_zero⟩
  have : NeZero (r : ℕ) := ⟨(hprime r r.property).ne_zero⟩
  have hcop : (q : ℕ).Coprime (r : ℕ) :=
    (Nat.coprime_primes (hprime q q.property) (hprime r r.property)).mpr
      (fun he => hqr (Subtype.ext he))
  let FP := pairedPolynomialFactors (F q) (F r)
  let HP := Fin.append (H q) (H r)
  let kP := pairedPolynomialKeep (keep q) (keep r)
  have he (j : Fin (K * M)) : (η j : ℂ) * (G q j * conj (G r j)) =
      supportedPolynomialWeight FP HP kP ((a + j.val : ℕ) : ℝ) *
        (χ q ((a + j.val : ℕ) : ZMod (q : ℕ)) *
          conj (χ r ((a + j.val : ℕ) : ZMod (r : ℕ)))) := by
    have hp := pairedPolynomialAmplitude (F q) (F r) (H q) (H r) (keep q) (keep r)
      ((a + j.val : ℕ) : ℝ)
    change polynomialAmplitude FP HP kP _ = _ at hp
    have hs : supportedPolynomialWeight FP HP kP ((a + j.val : ℕ) : ℝ) =
        (η j : ℂ) * polynomialAmplitude FP HP kP ((a + j.val : ℕ) : ℝ) := by
      unfold supportedPolynomialWeight polynomialAmplitude η
      ring
    rw [hs, hp]
    simp only [G, map_mul]
    ring
  have hb := supported_polynomial_integer_character_sum hcop (χ q) (χ r) (hnonprincipal q)
    a M K ha ((hM q).mul_right (hM r)) FP HP kP
  simp_rw [he]
  apply hb.trans
  have hc : polynomialWeightComplexity FP HP ≤ 2 * R := by
    change polynomialWeightComplexity (pairedPolynomialFactors (F q) (F r))
      (Fin.append (H q) (H r)) ≤ _
    rw [polynomialWeightComplexity_pair]
    have hq := hcomplexity q
    have hr := hcomplexity r
    omega
  have hpow : ((3 ^ polynomialWeightComplexity FP HP : ℕ) : ℝ) ≤ (3 ^ (2 * R) : ℕ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (3 : ℕ)) hc
  have hbud : smoothPolynomialBudget FP ≤ B ^ 2 := by
    change smoothPolynomialBudget (pairedPolynomialFactors (F q) (F r)) ≤ _
    rw [pairedPolynomialFactors_budget, pow_two]
    exact mul_le_mul (hbudget q) (hbudget r) (smoothPolynomialBudget_nonneg _) hB
  have hqrB : (q : ℝ) * (r : ℝ) ≤ (Bq : ℝ) ^ 2 := by
    have hq : (q : ℝ) ≤ Bq := by exact_mod_cast hBq q
    have hr : (r : ℝ) ≤ Bq := by exact_mod_cast hBq r
    simpa only [pow_two] using mul_le_mul hq hr (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hFP0 := smoothPolynomialBudget_nonneg FP
  change (M : ℝ) * (((3 ^ polynomialWeightComplexity FP HP : ℕ) : ℝ) *
      (2 * (a : ℝ)⁻¹ * smoothPolynomialBudget FP) * ((q : ℝ) * (r : ℝ))) ≤ _
  calc
    _ ≤ (M : ℝ) * (((3 ^ (2 * R) : ℕ) : ℝ) * (2 * (a : ℝ)⁻¹ * B ^ 2) * (Bq : ℝ) ^ 2) := by
      gcongr
    _ = _ := by ring

end Ostmann

end OAI
