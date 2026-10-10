import OAI.NumberTheory.Ostmann.Construction.SupportedPrimePrior

namespace OAI

/-! # Numerical bounds for the selected internal and external harmonic laws -/

namespace Ostmann
open scoped Classical BigOperators

/-- The fixed positive cell-mass constant changes the starting threshold,
not the coefficient of L in the normalizer. -/
theorem selected_cell_normalizer (c K L mass : ℝ) (hc : 0 < c)
    (hL : max 1 (-Real.log c) ≤ L)
    (hmass : c / Real.exp (K * L) ≤ mass) :
    0 < mass ∧ mass⁻¹ ≤ Real.exp ((K + 1) * L) := by
  have hm : 0 < mass := lt_of_lt_of_le (div_pos hc (Real.exp_pos _)) hmass
  have hsmall : Real.exp (-L) ≤ c := by
    calc
      _ ≤ Real.exp (Real.log c) :=
        Real.exp_le_exp.mpr (by linarith only [(le_max_right 1 (-Real.log c)).trans hL])
      _ = _ := Real.exp_log hc
  have hci : c⁻¹ ≤ Real.exp L := by
    have hh := inv_anti₀ (Real.exp_pos (-L)) hsmall
    simpa only [Real.exp_neg, inv_inv] using hh
  refine ⟨hm, (inv_anti₀ (div_pos hc (Real.exp_pos _)) hmass).trans ?_⟩
  calc
    (c / Real.exp (K * L))⁻¹ = Real.exp (K * L) * c⁻¹ := by rw [inv_div, div_eq_mul_inv]
    _ ≤ Real.exp (K * L) * Real.exp L :=
      mul_le_mul_of_nonneg_left hci (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Rich selected cells supply all the probability and atom bounds used in
both original-prime comparisons. Only their actual reciprocal masses and
prime ranges are needed. -/
theorem selected_harmonic_family_bounds (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) :
    let C := K + 1
    1 ≤ C ∧ ∀ (L : ℝ), max 1 (-Real.log c) ≤ L → ∀ (P : Finset ℕ) (B : Type)
      (Qμ : ℕ → Finset ℕ) (Qν : B → Finset ℕ),
      (∀ j, Qμ j ⊆ P) → (∀ j, Qν j ⊆ P) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      let μ := fun j => primeSubsetPrior P (Qμ j)
      let ν := fun j => primeSubsetPrior P (Qν j)
      (∀ j q, 0 ≤ μ j q) ∧ (∀ j q, 0 ≤ ν j q) ∧
      (∀ j, ∑ q, μ j q = 1) ∧ (∀ j, ∑ q, ν j q = 1) ∧
      (∀ j (q : P), (q : ℝ) * μ j q ≤ Real.exp (C * L)) ∧
      (∀ j q, μ j q ≤ Real.exp (C * L - Real.exp ((39 / 10000 : ℝ) * L))) ∧
      (∀ j q, ν j q ≤ Real.exp (C * L - Real.exp ((39 / 10000 : ℝ) * L))) ∧
      (∀ j q, μ j q ≤ Real.exp (C * L - Real.exp ((1 / 100 : ℝ) * L))) ∧
      (∀ j q, μ j q ≠ 0 → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) := by
  dsimp only
  have hC : 1 ≤ K + 1 := by linarith only [hK]
  refine ⟨hC, ?_⟩
  intro L hL P B Qμ Qν hμP hνP hμmass hνmass hμrange hνrange
  have hm (j) := selected_cell_normalizer c K L (∑ q ∈ Qμ j, (q : ℝ)⁻¹) hc hL (hμmass j)
  have hn (j) := selected_cell_normalizer c K L (∑ q ∈ Qν j, (q : ℝ)⁻¹) hc hL (hνmass j)
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hlow : Real.exp ((39 / 10000 : ℝ) * L) ≤ Real.exp ((1 / 100 : ℝ) * L) :=
    Real.exp_le_exp.mpr (by linarith only [hL1])
  refine ⟨(fun j q => primeSubsetPrior_nonneg P (Qμ j) q),
    (fun j q => primeSubsetPrior_nonneg P (Qν j) q), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact primeSubsetPrior_mass P (Qμ j) (hμP j) (ne_of_gt (hm j).1)
  · intro j
    exact primeSubsetPrior_mass P (Qν j) (hνP j) (ne_of_gt (hn j).1)
  · intro j q
    exact (prime_mul_primeSubsetPrior_le P (Qμ j) q).trans (hm j).2
  · intro j q
    exact primeSubsetPrior_le_exp_of_support P (Qμ j) _ _ (hm j).2
      (fun q hq => (Real.exp_le_exp.mpr hlow).trans (hμrange j q hq)) q
  · intro j q
    exact primeSubsetPrior_le_exp_of_support P (Qν j) _ _ (hn j).2 (hνrange j) q
  · intro j q
    exact primeSubsetPrior_le_exp_of_support P (Qμ j) _ _ (hm j).2 (hμrange j) q
  · intro j q hq
    exact hμrange j q (primeSubsetPrior_support P (Qμ j) q hq)

/-- A finite ambient prime set requires tier separation only for the
internal tiers which the depth-n sample actually uses. -/
theorem selected_harmonic_family_tiers (P : Finset ℕ) (B : Type) (n : ℕ)
    (Qμ : ℕ → Finset ℕ) (Qν : B → Finset ℕ) (tier : P → ℕ) (tierB : B → ℕ)
    (hμ : ∀ j, j < n → ∀ q : P, (q : ℕ) ∈ Qμ j → tier q = j)
    (hν : ∀ j (q : P), (q : ℕ) ∈ Qν j → tier q = tierB j) :
    (∀ j, j < n → ∀ q, primeSubsetPrior P (Qμ j) q ≠ 0 → tier q = j) ∧
    (∀ j q, primeSubsetPrior P (Qν j) q ≠ 0 → tier q = tierB j) := by
  exact ⟨fun j hj q hq => hμ j hj q (primeSubsetPrior_support P (Qμ j) q hq),
    fun j q hq => hν j q (primeSubsetPrior_support P (Qν j) q hq)⟩

end Ostmann

end OAI
