import OAI.Combinatorics.Progressions.Estimates.ModularDesignatedCoefficientMarkov

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

noncomputable def coefficientPolynomialRankFailureProbability {E I : Type*}
    [Fintype I] [DecidableEq I] (N n : ℕ) [NeZero N]
    (P : (E → ZMod N) → MvPolynomial I (ZMod N)) (c : E → ZMod N) : ℝ :=
  𝔼 u : Fin n → I → ZMod N,
    if polynomialLinearRow (polynomialIterDifference n (P c) u) = 0 then 1 else 0

theorem coefficientPolynomialRankFailureProbability_nonneg {E I : Type*}
    [Fintype I] [DecidableEq I] (N n : ℕ) [NeZero N]
    (P : (E → ZMod N) → MvPolynomial I (ZMod N)) (c : E → ZMod N) :
    0 ≤ coefficientPolynomialRankFailureProbability N n P c :=
  Finset.expect_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem coefficientPolynomialRankFailureProbability_expect_le
    {E A I : Type*} [Fintype E] [Fintype A] [Fintype I]
    [DecidableEq E] [DecidableEq A] [DecidableEq I]
    {p a n : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a)
    (slot : A → E) (hinj : Function.Injective slot)
    (S : A → Finset I) (hcard : ∀ b, (S b).card = n + 1)
    (hdisjoint : Pairwise (fun b c => Disjoint (S b) (S c)))
    (P Q : (E → ZMod (p ^ a)) → MvPolynomial I (ZMod (p ^ a)))
    (unit : A → (ZMod (p ^ a))ˣ)
    (hP : ∀ c d, P (Function.extend slot d c) = Q c +
      ∑ b, ((unit b : ZMod (p ^ a)) * d b) • ∏ i ∈ S b, X i) :
    (𝔼 c : E → ZMod (p ^ a), coefficientPolynomialRankFailureProbability (p ^ a) n P c) ≤
      (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ Fintype.card A := by
  have hconditional (c : E → ZMod (p ^ a)) :
      (𝔼 d : A → ZMod (p ^ a), coefficientPolynomialRankFailureProbability (p ^ a) n P
        (Function.extend slot d c)) ≤
        (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ Fintype.card A := by
    unfold coefficientPolynomialRankFailureProbability
    simp_rw [hP c]
    exact designatedPolynomial_expected_rank_failure_le hp ha S hcard hdisjoint (Q c) unit
  rw [← expect_coordinate_resampling slot hinj
    (coefficientPolynomialRankFailureProbability (p ^ a) n P)]
  calc
    _ ≤ 𝔼 _c : E → ZMod (p ^ a),
        (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ Fintype.card A :=
      Finset.expect_le_expect (fun c _ => hconditional c)
    _ = _ := Fintype.expect_const _

theorem coefficientPolynomialRankFailureProbability_mean_le
    {E A I : Type*} [Fintype E] [Fintype A] [Fintype I]
    [DecidableEq E] [DecidableEq A] [DecidableEq I]
    {p a n s : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a) (hns : n + 1 ≤ s)
    (slot : A → E) (hinj : Function.Injective slot)
    (S : A → Finset I) (hcard : ∀ b, (S b).card = n + 1)
    (hdisjoint : Pairwise (fun b c => Disjoint (S b) (S c)))
    (P Q : (E → ZMod (p ^ a)) → MvPolynomial I (ZMod (p ^ a)))
    (unit : A → (ZMod (p ^ a))ˣ)
    (hP : ∀ c d, P (Function.extend slot d c) = Q c +
      ∑ b, ((unit b : ZMod (p ^ a)) * d b) • ∏ i ∈ S b, X i) :
    (FiniteProbabilityWeights.uniform (E → ZMod (p ^ a))).mean
      (coefficientPolynomialRankFailureProbability (p ^ a) n P) ≤
      ((s : ℝ) * ((p : ℝ) ^ a) ^ (-modularRankSmallBallExponent s)) ^ Fintype.card A := by
  rw [FiniteProbabilityWeights.uniform_mean]
  apply (coefficientPolynomialRankFailureProbability_expect_le hp ha slot hinj S
    hcard hdisjoint P Q unit hP).trans
  apply pow_le_pow_left₀ (by positivity)
  exact modularRank_tag_cost_le hns (by exact_mod_cast hp.one_lt.le)

theorem coefficientPolynomialRankFailureProbability_markov
    {E A I : Type*} [Fintype E] [Fintype A] [Fintype I]
    [DecidableEq E] [DecidableEq A] [DecidableEq I]
    {p a n s : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a) (hns : n + 1 ≤ s)
    (slot : A → E) (hinj : Function.Injective slot)
    (S : A → Finset I) (hcard : ∀ b, (S b).card = n + 1)
    (hdisjoint : Pairwise (fun b c => Disjoint (S b) (S c)))
    (P Q : (E → ZMod (p ^ a)) → MvPolynomial I (ZMod (p ^ a)))
    (unit : A → (ZMod (p ^ a))ˣ)
    (hP : ∀ c d, P (Function.extend slot d c) = Q c +
      ∑ b, ((unit b : ZMod (p ^ a)) * d b) • ∏ i ∈ S b, X i) (C : ℝ) :
    (FiniteProbabilityWeights.uniform (E → ZMod (p ^ a))).eventProbability
      (fun c => ((p : ℝ) ^ a) ^ (-C) < coefficientPolynomialRankFailureProbability
        (p ^ a) n P c) ≤
      ((p : ℝ) ^ a) ^ C *
        ((s : ℝ) * ((p : ℝ) ^ a) ^ (-modularRankSmallBallExponent s)) ^ Fintype.card A := by
  have hq : 0 < (p : ℝ) ^ a := pow_pos (by exact_mod_cast hp.pos) _
  have h := finiteProbability_rank_markov
    (FiniteProbabilityWeights.uniform (E → ZMod (p ^ a)))
    (coefficientPolynomialRankFailureProbability (p ^ a) n P)
    (coefficientPolynomialRankFailureProbability_nonneg (p ^ a) n P) (C := C) hq
  exact h.trans (mul_le_mul_of_nonneg_left
    (coefficientPolynomialRankFailureProbability_mean_le hp ha hns slot hinj S hcard hdisjoint
      P Q unit hP) (Real.rpow_nonneg hq.le _))

end Erdos3

end

end OAI
