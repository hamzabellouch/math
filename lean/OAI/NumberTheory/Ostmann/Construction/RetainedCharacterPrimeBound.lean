import OAI.NumberTheory.Ostmann.ZeroDensity.HadamardPrimeBound
import OAI.NumberTheory.Ostmann.ZeroDensity.PageSelection

namespace OAI

/-! # Signed prime mass for a retained primitive real character -/

namespace Ostmann

open scoped BigOperators Classical

/-- Equality on natural arguments compares characters even when their
moduli occur with different dependent types. -/
def samePrimitiveRealCharacter (e : PrimitiveRealZero) (χ : PrimitiveRealCharacter) : Prop :=
  e.modulus = χ.modulus ∧ ∀ n : ℕ, e.character n = χ.character n

noncomputable def zeroComparisonConstant (P : PublishedProgressionInput) : ℝ :=
  max 5 (1 + P.kappa⁻¹)

/-- The only possible loss beyond the zero-free bound is a Siegel term for
the one retained Page character. The Euler and prime-power steps are proved. -/
theorem retained_character_prime_lower (P : PublishedProgressionInput)
    (H : PublishedRealZeroInput P) (hSiegel : PublishedSiegelBound)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A K : ℝ, 0 < A ∧ 0 < K ∧
      ∀ (χ : PrimitiveRealCharacter) (Q : ℕ) (R s : ℝ),
        2 ≤ Q → χ.modulus ≤ Q → 0 ≤ R →
        2 * (A + H.errorConstant) ≤ Real.log (4 * (Q : ℝ)) →
        1 < s → s ≤ 1 + 1 / Real.log (4 * (Q : ℝ)) →
        (∀ e : PrimitiveRealZero, selectedPageZero P Q = some e →
          samePrimitiveRealCharacter e χ → (e.modulus : ℝ) ≤ R) →
        -2 * zeroComparisonConstant P * Real.log (4 * (Q : ℝ)) -
            K * R ^ ε - H.errorConstant - A ≤ ∑' n, realPrimeTerm χ.character s n := by
  obtain ⟨Ad, hAd, hderiv⟩ := exists_dirichlet_logDerivative_bound
  obtain ⟨Ap, hAp, hprime⟩ := exists_signed_prime_lower_of_zero_sum
  obtain ⟨K, hK, hEbound⟩ := exceptional_zero_sum_bound hSiegel ε hε
  let A := Ad + Ap + 1
  refine ⟨A, K, by dsimp [A]; positivity, hK, ?_⟩
  intro χ Q R s hQ hχQ hR hsize hs hss hretain
  let L := Real.log (4 * (Q : ℝ))
  let s₀ := 1 + 1 / L
  let Z := H.expansion χ
  let Cz := zeroComparisonConstant P
  have hL1 : 1 ≤ L := by
    change 2 * (A + H.errorConstant) ≤ L at hsize
    dsimp [A] at hsize
    linarith [H.errorConstant_nonneg]
  have hL : 0 < L := by linarith
  have hs₀ : 1 < s₀ := by
    have hp : 0 < 1 / L := by positivity
    dsimp [s₀]
    linarith
  have hs₀2 : s₀ ≤ 2 := by
    have hdiv : 1 / L ≤ (1 : ℝ) := (div_le_one hL).mpr hL1
    dsimp [s₀]
    linarith
  have hss₀ : s ≤ s₀ := hss
  have hlog : Real.log (χ.modulus : ℝ) ≤ L := by
    apply Real.log_le_log (by exact_mod_cast χ.positive)
    have hmod : (χ.modulus : ℝ) ≤ Q := by exact_mod_cast hχQ
    linarith [show (0 : ℝ) ≤ Q from Nat.cast_nonneg Q]
  have hpole : 1 / (s₀ - 1) = L := by
    dsimp [s₀]
    field_simp
    ring
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hd := hderiv χ.modulus χ.complexCharacter s₀ hs₀ hs₀2
  change ‖deriv χ.L (s₀ : ℂ) / χ.L (s₀ : ℂ)‖ ≤ _ at hd
  rw [hpole] at hd
  have hdl : χ.logDerivative s₀ ≤ L + Ad := (Complex.re_le_norm _).trans hd
  have hanchor : (∑' i, realZeroKernel (s₀ - (Z.zeros i).re) (Z.zeros i).im) ≤ 2 * L := by
    apply realCharacterZeroExpansion_anchor Z s₀ L Ad hs₀ hs₀2 hlog hdl
    change 2 * (A + H.errorConstant) ≤ L at hsize
    dsimp [A] at hsize
    linarith
  obtain ⟨E, hcard, hEin, hEout⟩ := H.region χ Q hQ hχQ
  have hexception : (∑ i ∈ E, (s - (Z.zeros i).re)⁻¹) ≤ K * R ^ ε := by
    by_cases hnon : E.Nonempty
    · obtain ⟨i, hi⟩ := hnon
      let e := Z.realZero i (hEin i hi).1
      have hsel : selectedPageZero P Q = some e :=
        selectedPageZero_eq P Q hQ e hχQ (hEin i hi).2
      have hechar : samePrimitiveRealCharacter e χ := ⟨rfl, fun _ => rfl⟩
      have hqR : (χ.modulus : ℝ) ≤ R := hretain e hsel hechar
      have he := hEbound χ H.errorConstant Z E s hcard hs (fun i hi => (hEin i hi).1)
      exact he.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hqR hε.le) hK.le)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hnon, Finset.sum_empty]
      positivity
  have hCz5 : 5 ≤ Cz := le_max_left _ _
  have hCzc : 1 + P.kappa⁻¹ ≤ Cz := le_max_right _ _
  have hCz : 0 ≤ Cz := by linarith
  have hcompare := (realZeroKernel_sum_bound Z.zeros E s s₀ P.kappa (1 / L) Cz
    (fun i => ⟨(Z.in_strip i).1.le, (Z.in_strip i).2⟩) hs hss₀ hs₀2 P.kappa_pos
    hCz5 hCzc (by dsimp [s₀]; linarith) (by
      intro i hi him
      have hz := hEout i hi him
      change (Z.zeros i).re ≤ 1 - P.kappa / L at hz
      have hh : P.kappa / L ≤ s - (Z.zeros i).re := by linarith
      simpa only [div_eq_mul_inv, one_mul] using hh)
    (Z.summable s₀ hs₀ hs₀2)).2
  have hzbound : (∑' i, realZeroKernel (s - (Z.zeros i).re) (Z.zeros i).im) ≤
      2 * Cz * L + K * R ^ ε := by
    have h := add_le_add (mul_le_mul_of_nonneg_left hanchor hCz) hexception
    nlinarith
  have hp := hprime χ H.errorConstant Z s (2 * Cz * L + K * R ^ ε) hs
    (hss₀.trans hs₀2) hzbound
  change -2 * Cz * L - K * R ^ ε - H.errorConstant - A ≤ _
  dsimp [A]
  linarith

end Ostmann

end OAI
