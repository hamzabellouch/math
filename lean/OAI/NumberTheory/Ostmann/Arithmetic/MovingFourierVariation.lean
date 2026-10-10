import OAI.NumberTheory.Ostmann.Arithmetic.MovingFourierPolynomials

namespace OAI

/-! # Constructed variation bounds for the actual moving Fourier factors -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem MovingSlotData.leafFrequencies_bound {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) (V : ℝ) (h : T.Frequencies (fun s => |(s : ℝ)| ≤ V))
    (i : TreeLeafIndex n) : |(T.leafFrequencies i : ℝ)| ≤ V := by
  induction T with
  | leaf s regular => exact h
  | node s CL CR u left right ihL ihR =>
    cases i with
    | inl i => exact ihL h.2.1 i
    | inr i => exact ihR h.2.2 i

noncomputable def movingFourierVariationBudget (ψ : 𝓢(ℝ, ℂ))
    (V lo hi : ℝ) (n : ℕ) : ℝ :=
  (2 * SchwartzMap.seminorm ℝ 0 0 ψ +
    (SchwartzMap.seminorm ℝ 0 0 ψ + SchwartzMap.seminorm ℝ 0 1 ψ * V) * (hi - lo)) ^ (2 ^ n)

theorem movingFourierPolynomialFactors_budget {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V)) :
    smoothPolynomialBudget (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi) ≤
      movingFourierVariationBudget ψ V lo hi n := by
  unfold smoothPolynomialBudget movingFourierVariationBudget
  calc
    _ ≤ ∏ _j : Fin (2 ^ n),
        (2 * SchwartzMap.seminorm ℝ 0 0 ψ +
          (SchwartzMap.seminorm ℝ 0 0 ψ + SchwartzMap.seminorm ℝ 0 1 ψ * V) * (hi - lo)) := by
      apply Finset.prod_le_prod₀
      · intro j _
        let f := movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi j
        exact add_nonneg (mul_nonneg (by norm_num) f.bound_nonneg)
          (mul_nonneg f.lip_nonneg (sub_nonneg.mpr f.lo_le_hi))
      · intro j _
        have hv := T.leafFrequencies_bound V hV ((movingLeafIndexEquiv n).symm j)
        have hd := mul_le_mul_of_nonneg_left hv (schwartz_profile_lip_nonneg ψ)
        have he := mul_le_mul_of_nonneg_right (add_le_add (le_rfl : SchwartzMap.seminorm ℝ 0 0 ψ ≤ SchwartzMap.seminorm ℝ 0 0 ψ) hd)
          (sub_nonneg.mpr hhi)
        dsimp only [movingFourierPolynomialFactors]
        split_ifs <;> exact add_le_add le_rfl he
    _ = _ := by simp

/-- At most one derivative root per terminal quadratic is needed. Both the
root cut set and the variation bound are built from the actual history. -/
theorem movingFourierPolynomialFactors_variation {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hL : L.natDegree ≤ 1) (hR : R.natDegree ≤ 1)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V)) :
    ∃ S : Finset ℝ, S.card ≤ 2 ^ n ∧
      ∀ (u : ℕ → ℝ), Monotone u → ∀ N : ℕ,
        rootCellCode S (u 0) = rootCellCode S (u (N - 1)) →
        discreteVariation (fun j => smoothPolynomialWeight
          (movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi) (u j)) N ≤
            movingFourierVariationBudget ψ V lo hi n := by
  let F := movingFourierPolynomialFactors value T L R ψ X lo hi hlo hhi
  let S := polynomialRootCuts (fun i => (F i).polynomial.derivative)
  have hdeg (i : Fin (2 ^ n)) : (F i).polynomial.derivative.natDegree ≤ 1 := by
    have h := movingFourierPolynomialFactors_degree value T L R ψ X lo hi hlo hhi hL hR i
    change (F i).polynomial.natDegree ≤ 2 at h
    exact (Polynomial.natDegree_derivative_le _).trans (by omega)
  refine ⟨S, ?_, ?_⟩
  · apply (polynomialRootCuts_card _).trans
    calc
      _ ≤ ∑ _i : Fin (2 ^ n), 1 := Finset.sum_le_sum (fun i _ => hdeg i)
      _ = 2 ^ n := by simp
  · intro u hu N hcode
    apply (smoothPolynomialWeight_variation F S _ u hu N hcode).trans
      (movingFourierPolynomialFactors_budget value T L R ψ X lo hi V hlo hhi hV)
    intro i r hr
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Multiset.mem_toFinset.mpr hr⟩

end Ostmann

end OAI
