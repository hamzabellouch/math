import OAI.Combinatorics.ContingencyTables.Counting.CompanionWarmStart

namespace OAI

/-! # Binary-size minimum mass of the actual companion transversal law

The factorial denominator cancels against the two complementary
factorials. The surviving binomial coefficient is bounded by 2^b,
giving the p+K exponent used in the paper's restart schedule.
-/

namespace ContingencyTables.InitialTransversals

open scoped BigOperators Classical
open Nat InitialLocalChoices CommonBasesFPRAS LabelledFactorial TwoLiftStates

lemma localWeight_lower (b : ℕ) (S : Finset (Fin b)) :
    (1/2:ℝ)^b ≤ localWeight b 0 0 S := by
  have hk : S.card ≤ b := by
    simpa using S.card_le_univ
  have hD : (0:ℝ) < b.factorial := by exact_mod_cast Nat.factorial_pos b
  have hF : (b.choose S.card:ℝ)*(S.card.factorial:ℝ)*((b-S.card).factorial:ℝ)=
      (b.factorial:ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hprod : (b.choose S.card:ℝ)*localWeight b 0 0 S=1 := by
    unfold localWeight
    simp only [Nat.sub_zero,Nat.add_zero]
    rw [← mul_div_assoc,← mul_assoc,hF,div_self hD.ne']
  have hlocal : 0 ≤ localWeight b 0 0 S := by
    unfold localWeight
    positivity
  have hchoose : (b.choose S.card:ℝ) ≤ (2:ℝ)^b := by
    exact_mod_cast Nat.choose_le_two_pow b S.card
  have hm := mul_le_mul_of_nonneg_right hchoose hlocal
  have hpow : (0:ℝ) < (2:ℝ)^b := by positivity
  rw [hprod] at hm
  rw [div_pow,one_pow,div_le_iff₀ hpow]
  nlinarith

variable {C : Type*} [Fintype C]

/-- On every actual paired transversal, the constant-count factorial
display is at least M times 2 to the negative number of copy labels. -/
theorem firstLift_plain_lower (b : C → ℕ) (M : ℝ) (hM : 0 ≤ M)
    (S : Set (Copy b×Bool)) (hS : PlainState pairs S) :
    M*(1/2:ℝ)^(∑ c,b c) ≤
      firstLift (group (cell b)) (fun _ => M) (denominator b) S := by
  let T := plainEquivChoices b ⟨S,hS⟩
  have he : encode b T=S := congrArg Subtype.val ((plainEquivChoices b).symm_apply_apply ⟨S,hS⟩)
  rw [← he,firstLift_encode]
  apply mul_le_mul_of_nonneg_left _ hM
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀
  · intro c _
    positivity
  · intro c _
    exact localWeight_lower (b c) (T c)

end ContingencyTables.InitialTransversals

namespace ContingencyTables.CompanionMinMass

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication CompanionAnnealing CompanionInitialization
open CompanionWarmStart TwoLiftStates LabelledFactorial

variable {I J : Type*} [Fintype I] [Fintype J]

lemma label_card (A : Instance I J) :
    Fintype.card (Labels A)=∑ s : SmallCell A,A.b s.val.1 s.val.2 := by
  simp [Labels,Fintype.card_sigma]

lemma initial_weight_lower (A : Instance I J) (S : Set (Labels A×Bool))
    (hS : PlainState pairs S) :
    freeTotal A*(1/2:ℝ)^Fintype.card (Labels A) ≤ weight A 0 S := by
  have hM : (0:ℝ) ≤ freeTotal A :=
    (Finset.prod_pos (fun _ _ => Nat.cast_pos.mpr (Nat.succ_pos _))).le
  have hh := InitialTransversals.firstLift_plain_lower
    (fun s : SmallCell A => A.b s.val.1 s.val.2) (freeTotal A) hM S hS
  rw [← label_card] at hh
  unfold weight f firstLift
  simp only [Nat.cast_zero,zero_div]
  rw [denominator_eq]
  rw [h_zero]
  convert hh using 1
  congr 1

/-- If the finite small-profile domain has at most 2^K points, every
actual phase-j transversal has mass at least 2^(-(j+p+K)). -/
theorem law_lower (A : Instance I J) (K j : ℕ)
    (hB : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1)) ≤ (2:ℝ)^K)
    (S : Set (Labels A×Bool)) (hS : PlainState pairs S) :
    (1/2:ℝ)^(j+Fintype.card (Labels A)+K) ≤ law A j S := by
  have hM : (0:ℝ) < freeTotal A :=
    Finset.prod_pos (fun _ _ => Nat.cast_pos.mpr (Nat.succ_pos _))
  have hT := (total_bounds_zero A j).2
  have hT0 : total A 0=freeTotal A*∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1) := by
    unfold total weight
    simpa only [Nat.cast_zero,zero_div] using total_zero A
  rw [hT0] at hT
  have hupper : total A j ≤ freeTotal A*(2:ℝ)^K :=
    hT.trans (mul_le_mul_of_nonneg_left hB hM.le)
  have hw := (weight_bounds_zero A j S).1
  have hi := initial_weight_lower A S hS
  have hlower : freeTotal A*(1/2:ℝ)^(j+Fintype.card (Labels A)) ≤ weight A j S := by
    rw [pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hi (show (0:ℝ) ≤ (1/2:ℝ)^j by positivity)]
  have hpos := total_positive A j
  unfold law
  rw [le_div_iff₀ hpos,pow_add]
  have hm := mul_le_mul_of_nonneg_left hupper
    (show (0:ℝ) ≤ (1/2:ℝ)^(j+Fintype.card (Labels A))*(1/2:ℝ)^K by positivity)
  have hcancel : (1/2:ℝ)^K*(2:ℝ)^K=1 := by
    rw [← mul_pow]
    norm_num
  have he : ((1/2:ℝ)^(j+Fintype.card (Labels A))*(1/2:ℝ)^K)*
      (freeTotal A*(2:ℝ)^K)=freeTotal A*(1/2:ℝ)^(j+Fintype.card (Labels A)) := by
    calc
      _ = freeTotal A*(1/2:ℝ)^(j+Fintype.card (Labels A))*
          ((1/2:ℝ)^K*(2:ℝ)^K) := by ring
      _ = _ := by rw [hcancel,mul_one]
  rw [he] at hm
  exact hm.trans hlower

end ContingencyTables.CompanionMinMass

end OAI
