import OAI.Combinatorics.Ryser.Incidence.PopularScalars
import OAI.Combinatorics.Ryser.Incidence.ScalarCoverExpressions
import OAI.Combinatorics.Ryser.Incidence.RatioSet
import OAI.Combinatorics.Ryser.Incidence.ScalarCollisions
import OAI.Combinatorics.Ryser.Incidence.NoApproximateSubfieldNumerics
import Mathlib.SetTheory.Cardinal.Finite

namespace OAI

namespace RyserCoveringCounterexample.Incidence

noncomputable section
open scoped Pointwise

variable {F : Type*} [Field F] [DecidableEq F]

theorem scalarExpression_of_mem_ratioSet {E : Finset F} {c : F}
    (hc : c ∈ ratioSet E) : ScalarExpression E c 4 := by
  obtain ⟨x, hx, x', hx', y, hy, y', hy', hyy', hquot⟩ := mem_ratioSet.mp hc
  rw [← hquot]
  exact scalarExpression_ratio hx hx' hy hy' hyy'

theorem no_approximate_subfield_finite [Fintype F]
    (S : Finset F) (K : ℝ) (hzero : (0 : F) ∉ S) (hK : 2 ≤ K)
    (hsub : ((S - S).card : ℝ) ≤ K * (S.card : ℝ))
    (hdiv : ((S / S).card : ℝ) ≤ K * (S.card : ℝ))
    (properSubfields : ∀ L : Subfield F, L ≠ ⊤ →
      (Nat.card L : ℝ) ^ 3 ≤ (Fintype.card F : ℝ))
    (hlarge : 4 * K ^ 127942 < (S.card : ℝ)) :
    (S.card : ℝ) ^ 3 ≤ 8 * K ^ 3 * (Fintype.card F : ℝ) ∨
      (Fintype.card F : ℝ) < 2 * K ^ 527 * (S.card : ℝ) := by
  classical
  by_cases hfirst : (S.card : ℝ) ^ 3 ≤ 8 * K ^ 3 * (Fintype.card F : ℝ)
  · exact Or.inl hfirst
  apply Or.inr
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hspos : 0 < (S.card : ℝ) :=
    lt_trans (mul_pos (by norm_num) (pow_pos hKpos _)) hlarge
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hspos)
  obtain ⟨B, E, hEB, hBcard, hpopular, hD, hCost⟩ :=
    exists_popular_scalars S K hS hzero hK hsub hdiv
  have hB : B.Nonempty := by
    apply Finset.card_pos.mp
    rw [hBcard]
    exact hS.card_pos
  have hnum := noapprox_threshold_numerics K (S.card : ℝ) (E.card : ℝ)
    hK hpopular hlarge
  have hE : 2 ≤ E.card := by exact_mod_cast hnum.2.1.le
  have hC4 : scalarCoverExponent 4 + 3 = 527 := by decide
  have hC9 : scalarCoverExponent 9 + 3 = 127940 := by decide
  have hratio (r : F) (hr : r ∈ ratioSet E) : ScalarExpression E r 4 :=
    scalarExpression_of_mem_ratioSet hr
  have hsmall (c : F) (hc : ScalarExpression E c 9) :
      (dilateSum E c).card < E.card ^ 2 := by
    have hgrowth := ScalarExpression.card_add_subset_of_le hB hK hD hCost hEB
      hc (show 9 ≤ 9 from le_rfl)
    have hbound : ((dilateSum E c).card : ℝ) ≤ K ^ 127940 * (S.card : ℝ) := by
      rw [dilateSum_eq_add_smul]
      simpa only [hC9, hBcard] using hgrowth
    exact_mod_cast hbound.trans_lt hnum.2.2.1
  have hadd : ∀ r ∈ ratioSet E, ∀ r' ∈ ratioSet E,
      (dilateSum E (r + r')).card < E.card ^ 2 := by
    intro r hr r' hr'
    exact hsmall (r + r') (ScalarExpression.add (hratio r hr) (hratio r' hr'))
  have hmul : ∀ r ∈ ratioSet E, ∀ r' ∈ ratioSet E,
      (dilateSum E (r * r')).card < E.card ^ 2 := by
    intro r hr r' hr'
    exact hsmall (r * r') (ScalarExpression.mul (hratio r hr) (hratio r' hr'))
  let L : Subfield F := ratioSubfield E hE hadd hmul
  have hLcard : Nat.card L = (ratioSet E).card := by
    change Nat.card (ratioSet E) = (ratioSet E).card
    exact Nat.card_eq_finsetCard _
  have hEcard : (E.card : ℝ) ≤ (Nat.card L : ℝ) := by
    rw [hLcard]
    exact_mod_cast card_le_card_ratioSet hE
  have hfieldlt : (Fintype.card F : ℝ) < (E.card : ℝ) ^ 3 :=
    cube_lt_of_popular_lower K (S.card : ℝ) (E.card : ℝ) (Fintype.card F : ℝ)
      hKpos hspos.le hpopular (lt_of_not_ge hfirst)
  have hLtop : L = ⊤ := by
    by_contra hproper
    have hcube : (E.card : ℝ) ^ 3 ≤ (Nat.card L : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hEcard 3
    exact (not_lt_of_ge (hcube.trans (properSubfields L hproper))) hfieldlt
  have hallratio (c : F) : c ∈ ratioSet E := by
    have hc : c ∈ L := by rw [hLtop]; exact Subfield.mem_top _
    exact hc
  have hallgrowth (c : F) :
      ((dilateSum E c).card : ℝ) ≤ K ^ 527 * (S.card : ℝ) := by
    have hgrowth := ScalarExpression.card_add_subset_of_le hB hK hD hCost hEB
      (hratio c (hallratio c)) (show 4 ≤ 4 from le_rfl)
    rw [dilateSum_eq_add_smul]
    simpa only [hC4, hBcard] using hgrowth
  have hcollision := card_field_lt_twice_of_dilateSum_card_le_real E
    (K ^ 527 * (S.card : ℝ))
    (mul_nonneg (pow_nonneg hKpos.le _) (Nat.cast_nonneg _))
    hallgrowth hnum.2.2.2
  simpa only [mul_assoc] using hcollision

theorem no_approximate_subfield_finite_of_nat [Fintype F]
    (S : Finset F) (K : ℝ) (hzero : (0 : F) ∉ S) (hK : 2 ≤ K)
    (hsub : ((S - S).card : ℝ) ≤ K * (S.card : ℝ))
    (hdiv : ((S / S).card : ℝ) ≤ K * (S.card : ℝ))
    (properSubfields : ∀ L : Subfield F, L ≠ ⊤ →
      Nat.card L ^ 3 ≤ Fintype.card F)
    (hlarge : 4 * K ^ 127942 < (S.card : ℝ)) :
    (S.card : ℝ) ^ 3 ≤ 8 * K ^ 3 * (Fintype.card F : ℝ) ∨
      (Fintype.card F : ℝ) < 2 * K ^ 527 * (S.card : ℝ) := by
  exact no_approximate_subfield_finite S K hzero hK hsub hdiv
    (fun L hL => by exact_mod_cast properSubfields L hL) hlarge

end
end RyserCoveringCounterexample.Incidence

end OAI
