import OAI.NumberTheory.TwoPoint.Walks.CanonicalBinSummation

namespace OAI

/-! Real bin endpoints introduce factors floor(T)/T of norm at most one.
The per-bin spectral bounds remain valid with these factors. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_canonical_weighted_bin_sum_uniform
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (_hh : 0 < h) (_hl : 0 < l) (E : Finset ℕ)
        (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
        (_hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ (bins : Finset ℤ) (eligible : ℤ → ℕ → ℕ → Prop),
        (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
      ∀ (b : ℕ) (N : ℤ → ℕ) (v : ℤ → ℂ),
        (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
        (∀ j ∈ bins, ‖v j‖ ≤ 1) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let R := Real.exp 1 * (2 * (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      ‖∑ j ∈ bins, v j * canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j)‖ /
        totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η ≤
        (6 * bins.card * (l : ℝ) ^ 2 / L) * (R / W ^ J) +
          6 * bins.card * Real.exp (-L) := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_actual_retained_bin_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h l hh hl E hE hEl W hW
  filter_upwards [hb h l hh hl E hE hEl W hW,
    hprime.eventually_canonical_retained_mass E W hW] with L hb hm
  intro hL η hη hηone bins eligible he b N v hN hv
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let S := paddingTiltNormalizer (paddingPrimeSupply E L)
  let V := ∏ j, primeHarmonicMass (P j)
  let R := Real.exp 1 * (2 * (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J))
  have hmass := hm hL η hη
  have hbound (j : ℤ) (hj : j ∈ bins) :
      ‖v j * canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j)‖ ≤
        3 * (l : ℝ) ^ 2 * S * R / L + 3 * Real.exp (-L) := by
    rw [norm_mul]
    calc
      _ ≤ 1 * ‖canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j)‖ :=
        mul_le_mul_of_nonneg_right (hv j hj) (norm_nonneg _)
      _ = ‖canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j)‖ := one_mul _
      _ ≤ _ := hb hL η hη hηone (eligible j) (he j hj) b (N j) (hN j hj)
  exact retained_bin_sum_mass_lower bins
    (fun j => v j * canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j))
    S V (totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η)
    L l R (Real.exp (-L)) W J (paddingTiltNormalizer_one_le _) hW hmass.1
    (by linarith) hmass.2 (by positivity) (Real.exp_pos _).le hbound

end TwoPointCorrelations

end OAI
