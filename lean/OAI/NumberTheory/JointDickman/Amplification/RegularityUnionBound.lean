import OAI.NumberTheory.JointDickman.Amplification.MarkovRemainders

namespace OAI

/-! # A finite union bound for every failure of the regularity cutoff -/

namespace JointDickman

open Finset

open Classical in
noncomputable def prefixViolationMass (B L : ℕ) (τ : ℝ) (S : Finset ℕ) (w : ℝ) : ℝ :=
  ∑ i ∈ Icc 1 L,
    ((if ((primePrefix B ((i : ℝ) / L) S).card : ℝ) <
        (((i : ℝ) / L) / 2 - τ) * auxiliaryLogLength B then w else 0) +
    (if (((i : ℝ) / L) / 2 + τ) * auxiliaryLogLength B <
        ((primePrefix B ((i : ℝ) / L) S).card : ℝ) then w else 0))

open Classical in
noncomputable def tailViolationMass (B : ℕ) (C : ℝ) (S : Finset ℕ) (w : ℝ) : ℝ :=
  ∑ i ∈ range B,
    if ((S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
      (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C then w else 0

theorem prefixViolationMass_nonneg (B L : ℕ) (τ : ℝ) (S : Finset ℕ) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ prefixViolationMass B L τ S w := by
  classical
  apply sum_nonneg
  intro i _
  split_ifs <;> linarith

theorem tailViolationMass_nonneg (B : ℕ) (C : ℝ) (S : Finset ℕ) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ tailViolationMass B C S w := by
  classical
  apply sum_nonneg
  intro i _
  split_ifs <;> linarith

theorem regularity_failure_union_bound {B L : ℕ} {τ C w : ℝ} (S : Finset ℕ)
    (hC : 0 ≤ C) (hlog : 1 ≤ Real.log (auxiliaryCutoff B)) (hw : 0 ≤ w)
    (hbad : ¬RegularPrimeSet B L τ C S) :
    w ≤ prefixViolationMass B L τ S w + tailViolationMass B C S w := by
  classical
  have hpnon := prefixViolationMass_nonneg B L τ S hw
  have htnon := tailViolationMass_nonneg B C S hw
  unfold RegularPrimeSet at hbad
  rcases not_and_or.mp hbad with hprefix | htail
  · obtain ⟨i, hi⟩ := not_forall.mp hprefix
    obtain ⟨hi, hbad_i⟩ := not_imp.mp hi
    have hsingle :
        (if ((primePrefix B ((i : ℝ) / L) S).card : ℝ) <
            (((i : ℝ) / L) / 2 - τ) * auxiliaryLogLength B then w else 0) +
        (if (((i : ℝ) / L) / 2 + τ) * auxiliaryLogLength B <
            ((primePrefix B ((i : ℝ) / L) S).card : ℝ) then w else 0) ≤ prefixViolationMass B L τ S w := by
      apply single_le_sum (fun j _ => ?_) hi
      split_ifs <;> linarith
    rcases not_and_or.mp hbad_i with hlo | hhi
    · rw [ite_eq_left (lt_of_not_ge hlo)] at hsingle
      split_ifs at hsingle <;> linarith
    · rw [ite_eq_left (lt_of_not_ge hhi)] at hsingle
      split_ifs at hsingle <;> linarith
  · obtain ⟨i, hi⟩ := not_forall.mp htail
    have hfail := lt_of_not_ge hi
    have hY : 0 < primeTailEndpoint B i := by
      unfold primeTailEndpoint
      positivity
    have hcount : (0 : ℝ) ≤ (S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card :=
      Nat.cast_nonneg _
    have hYi : primeTailEndpoint B i < B := by
      by_contra h
      have hBY : (B : ℝ) ≤ primeTailEndpoint B i := le_of_not_gt h
      have hdiv : (B : ℝ) / primeTailEndpoint B i ≤ 1 := (div_le_one hY).mpr hBY
      have hlog' := Real.log_nonpos (div_nonneg (Nat.cast_nonneg B) hY.le) hdiv
      linarith
    have hiB : i ∈ range B := mem_range.mpr (tail_endpoint_index_lt hlog hYi)
    have hsingle :
        (if ((S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
            (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C then w else 0) ≤
          tailViolationMass B C S w := by
      apply single_le_sum (fun j _ => ?_) hiB
      split_ifs <;> linarith
    rw [ite_eq_left hfail] at hsingle
    linarith

end JointDickman

end OAI
