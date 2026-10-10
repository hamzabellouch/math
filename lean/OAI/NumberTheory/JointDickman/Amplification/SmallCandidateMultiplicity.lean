import OAI.NumberTheory.JointDickman.Amplification.SmallAdditionCount
import OAI.NumberTheory.JointDickman.Amplification.CandidateMultiplicity
import OAI.NumberTheory.JointDickman.Amplification.MarkovRemainders

namespace OAI

/-! # Pairs of representations with only small added primes -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def smallCandidateAlternatives (B L T H : ℕ) (τ C : ℝ)
    {M : ℕ} (i k : Fin M) (A D U V : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (candidatePairRepresentations B L T H τ C i k (A ∪ U) (D ∪ V)).filter
    (fun ab => ab.1 \ A ⊆ primePrefix B ((3 : ℝ)/L) (ab.1 \ A) ∧
      ab.2 \ D ⊆ primePrefix B ((3 : ℝ)/L) (ab.2 \ D))

theorem smallCandidateAlternatives_subset (B L T H : ℕ) (τ C : ℝ)
    {M : ℕ} (i k : Fin M) (A D U V : Finset ℕ) :
    smallCandidateAlternatives B L T H τ C i k A D U V ⊆
      (regularSmallAlternatives B L 3 τ C A U).product
        (regularSmallAlternatives B L 3 τ C D V) := by
  intro ab hab
  obtain ⟨hab,hadd⟩ := mem_filter.mp hab
  have hm := mem_product.mp (mem_filter.mp hab).1
  have ha := mem_endpointSplits.mp hm.1
  have hd := mem_endpointSplits.mp hm.2
  exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr ha.1,ha.2.1,hadd.1⟩,
    mem_filter.mpr ⟨mem_powerset.mpr hd.1,hd.2.1,hadd.2⟩⟩

noncomputable def smallMultiplicityExponent (L : ℕ) (τ : ℝ) : ℝ :=
  ((6 : ℝ)/L+4*τ)*Real.log 2+2*highOmissionExponent τ

theorem smallCandidateAlternatives_exp_bound {B L T H : ℕ} {τ C : ℝ}
    {M : ℕ} (i k : Fin M) (A D U V : Finset ℕ) (hL : 3 ≤ L)
    (hτ : 0 < τ) (hτsmall : τ ≤ 1/100) (hℓ : 0 ≤ auxiliaryLogLength B)
    (hA : RegularPrimeSet B L τ C A) (hD : RegularPrimeSet B L τ C D)
    (hU : RegularPrimeSet B L τ C U) (hV : RegularPrimeSet B L τ C V) :
    ((smallCandidateAlternatives B L T H τ C i k A D U V).card : ℝ) ≤
      Real.exp (smallMultiplicityExponent L τ*auxiliaryLogLength B) := by
  have ha := regularSmallAlternatives_exp_bound (k := 3) A U (by omega) (by simp; omega) hτ hτsmall hℓ hA hU
  have hd := regularSmallAlternatives_exp_bound (k := 3) D V (by omega) (by simp; omega) hτ hτsmall hℓ hD hV
  have hc : ((smallCandidateAlternatives B L T H τ C i k A D U V).card : ℝ) ≤
      (regularSmallAlternatives B L 3 τ C A U).card*
        (regularSmallAlternatives B L 3 τ C D V).card := by
    exact_mod_cast (card_le_card (smallCandidateAlternatives_subset B L T H τ C i k A D U V)).trans_eq
      (by rw [Finset.product_eq_sprod,card_product])
  refine hc.trans ((mul_le_mul ha hd (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq ?_)
  rw [← Real.exp_add]
  congr 1
  unfold smallMultiplicityExponent
  ring

theorem smallMultiplicityExponent_nonneg {L : ℕ} {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ 1/100) : 0 ≤ smallMultiplicityExponent L τ := by
  unfold smallMultiplicityExponent
  exact add_nonneg (mul_nonneg (add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _))
    (mul_nonneg (by norm_num) hτ)) (Real.log_nonneg (by norm_num)))
    (mul_nonneg (by norm_num) (highOmissionExponent_nonneg hτ hτsmall))

/-- The deterministic small-addition count has the same bound under every
probability law on the two remainders. -/
theorem smallCandidateAlternatives_rpow_bound {L : ℕ} (hL : 3 ≤ L)
    {τ : ℝ} (hτ : 0 < τ) (hτsmall : τ ≤ 1/100) :
    ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C : ℝ) (i k : Fin M) (A D U V : Finset ℕ),
      RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D →
      RegularPrimeSet B L τ C U → RegularPrimeSet B L τ C V →
      ((smallCandidateAlternatives B L T H τ C i k A D U V).card : ℝ) ≤
        (B : ℝ)^(smallMultiplicityExponent L τ) := by
  filter_upwards [auxiliaryLogLength_between, eventually_gt_atTop 0] with B hℓ hB
  intro T H M C i k A D U V hA hD hU hV
  have h := smallCandidateAlternatives_exp_bound (T := T) (H := H) i k A D U V hL hτ hτsmall hℓ.1 hA hD hU hV
  refine h.trans ?_
  rw [Real.rpow_def_of_pos (by exact_mod_cast hB : (0 : ℝ) < B)]
  exact Real.exp_le_exp.mpr (by
    nlinarith [mul_le_mul_of_nonneg_left hℓ.2 (smallMultiplicityExponent_nonneg hτ.le hτsmall (L := L))])

end JointDickman

end OAI
