import OAI.Combinatorics.ContingencyTables.Dense.DenseTrialWeights

namespace OAI

/-! # Acceptance probability of the actual ideal dense trial -/

namespace ContingencyTables.GridBoundary

open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def denseAcceptanceMass (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) : ℝ :=
  ∑ t : DenseTrial R P d q, if TrialAccepted R P d e t then denseTrialMass R P d e t else 0

omit [DecidableEq I] [DecidableEq J] in
theorem goodBin_trialAccepted (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) (t : DenseTrial R P d q) (ht : goodBin R P d e t.1) :
    TrialAccepted R P d e t :=
  (trialReal_feasible_iff R P d hd hR hP e t).mp
    (ht (trialReal R P d e t) (trialReal_closed R P d hd hR hP e t))

theorem denseAcceptanceMass_le_one (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (e : I × J ≃ Fin q) : denseAcceptanceMass R P d e ≤ 1 := by
  rw [← denseTrialMass_sum R P d hd hR hP e]
  apply Finset.sum_le_sum
  intro t _
  split_ifs
  · exact le_rfl
  · exact (denseTrialMass_pos R P d hd hR hP e t).le

/-- Wholly feasible bins accept every integral offset, so their proved
stationary mass is a lower bound on the actual trial acceptance mass. -/
theorem denseAcceptanceMass_lower (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hdimR : Fintype.card (Option I) ≤ d) (hdimP : Fintype.card (Option J) ≤ d)
    (hfree : Fintype.card (I × J) ≤ d) (htotal : ∑ i, R i = ∑ j, P j)
    (e : I × J ≃ Fin q) : (1 / 32 : ℝ) ≤ denseAcceptanceMass R P d e := by
  let : Nonempty (Offset (integerWidth R P d)) :=
    ⟨fun p => ⟨0, integerWidth_pos R P d hd hR hP p⟩⟩
  have hO : (Fintype.card (Offset (integerWidth R P d)) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Fintype.card_pos (α := Offset (integerWidth R P d)))
  have hgood := dense_good_bin_probability R P d hd hR hP hRmax hPmax
    hdimR hdimP hfree htotal e
  have hle :
      (∑ t : DenseTrial R P d q,
        if goodBin R P d e t.1 then denseTrialMass R P d e t else 0) ≤
      denseAcceptanceMass R P d e := by
    apply Finset.sum_le_sum
    intro t _
    by_cases hg : goodBin R P d e t.1
    · rw [ite_eq_left hg, ite_eq_left (goodBin_trialAccepted R P d hd hR hP e t hg)]
    · rw [ite_eq_right hg]
      split_ifs
      · exact (denseTrialMass_pos R P d hd hR hP e t).le
      · exact le_rfl
  apply hgood.trans
  convert hle using 1
  rw [Fintype.sum_prod_type]
  change _ = ∑ a : Grid (I := Fin q) (4 * d ^ 8),
    ∑ _o : Offset (integerWidth R P d), if goodBin R P d e a then
      (denseBinWeight R P d e a /
        (∑ b : Grid (I := Fin q) (4 * d ^ 8), denseBinWeight R P d e b)) /
          (Fintype.card (Offset (integerWidth R P d)) : ℝ) else 0
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_ite, mul_zero]
  simp_rw [mul_div_cancel₀ _ hO]
  rw [goodBins, Finset.sum_filter, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

end

end ContingencyTables.GridBoundary

end OAI
