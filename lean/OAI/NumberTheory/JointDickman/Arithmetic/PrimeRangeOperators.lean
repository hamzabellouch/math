import OAI.NumberTheory.JointDickman.Amplification.HighLowThinning

namespace OAI

/-! # The high-prime restrictions as finite averaging operators -/

namespace JointDickman

open Finset

noncomputable def subsetAverage (P : Finset ℕ) (q : ℕ → ℝ) (F : Finset ℕ → ℝ) : ℝ :=
  ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * F S

open Classical in
noncomputable def keptHighAverage (P Q : Finset ℕ) (F : Finset ℕ → ℝ) : ℝ :=
  ∑ S ∈ (P ∪ Q).powerset, bernoulliSubsetMass (P ∪ Q) (fun _ => (1 / 2 : ℝ)) S *
    (if S ∩ Q = Q then F (S ∩ P) else 0)

open Classical in
noncomputable def noHighAdditionAverage (P Q : Finset ℕ) (q : ℕ → ℝ)
    (k : ℝ) (F : Finset ℕ → ℝ) : ℝ :=
  ∑ S ∈ (P ∪ Q).powerset, ∑ T ∈ (P ∪ Q).powerset,
    jointRetentionMass (P ∪ Q) q S T *
      (if k ≤ ((S ∩ Q).card : ℝ) ∧ T ∩ Q = ∅ then F (T ∩ P) else 0)

theorem keptHighAverage_eq (P Q : Finset ℕ) (hd : Disjoint P Q) (F : Finset ℕ → ℝ) :
    keptHighAverage P Q F = (1 / 2 : ℝ)^Q.card * subsetAverage P (fun _ => 1 / 2) F :=
  fixed_high_retention_factor P Q hd F

theorem noHighAdditionAverage_eq (P Q : Finset ℕ) (hd : Disjoint P Q)
    (q : ℕ → ℝ) (k : ℝ) (F : Finset ℕ → ℝ) :
    noHighAdditionAverage P Q q k F = highNoAdditionMass Q q k *
      subsetAverage P (fun p => q p / 2) F := high_low_thinning_factor P Q hd q k F

theorem subsetAverage_const_mul (P : Finset ℕ) (q : ℕ → ℝ) (c : ℝ) (F : Finset ℕ → ℝ) :
    subsetAverage P q (fun S => c * F S) = c * subsetAverage P q F := by
  unfold subsetAverage
  rw [mul_sum]
  apply sum_congr rfl
  intro S _
  ring

theorem subsetAverage_le_const (P : Finset ℕ) (q : ℕ → ℝ)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) (F : Finset ℕ → ℝ) (K : ℝ)
    (hF : ∀ S ⊆ P, F S ≤ K) : subsetAverage P q F ≤ K := by
  calc
    _ ≤ ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * K :=
      sum_le_sum (fun S hS => mul_le_mul_of_nonneg_left (hF S (mem_powerset.mp hS))
        (bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq))
    _ = K := by rw [← sum_mul, bernoulliSubsetMass_sum, one_mul]

theorem highNoAdditionMass_nonneg (Q : Finset ℕ) (q : ℕ → ℝ) (k : ℝ)
    (hq : ∀ p ∈ Q, 0 ≤ q p ∧ q p ≤ 1) : 0 ≤ highNoAdditionMass Q q k := by
  unfold highNoAdditionMass
  apply sum_nonneg
  intro S hS
  split_ifs
  · unfold jointRetentionMass subsetRetentionMass
    simp only [empty_subset, ite_true]
    exact mul_nonneg (bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq) (by positivity)
  · exact le_rfl

/-- Keeping both coefficients' high parts is averaged only after a uniform
bound for the two low coefficient choices has been established. -/
theorem keptHighAverage_pair_bound (P Q R S : Finset ℕ) (hPQ : Disjoint P Q)
    (hRS : Disjoint R S) (F : Finset ℕ → Finset ℕ → ℝ) (K : ℝ)
    (hF : ∀ A ⊆ P, ∀ D ⊆ R, F A D ≤ K) :
    keptHighAverage P Q (fun A => keptHighAverage R S (F A)) ≤
      (1 / 2 : ℝ)^Q.card * (1 / 2 : ℝ)^S.card * K := by
  rw [keptHighAverage_eq P Q hPQ]
  have hi (A : Finset ℕ) (hA : A ⊆ P) : keptHighAverage R S (F A) ≤ (1 / 2 : ℝ)^S.card * K := by
    rw [keptHighAverage_eq R S hRS]
    exact mul_le_mul_of_nonneg_left
      (subsetAverage_le_const R (fun _ => 1 / 2) (by intros; norm_num) (F A) K (hF A hA)) (by positivity)
  have hh := mul_le_mul_of_nonneg_left
    (subsetAverage_le_const P (fun _ => 1 / 2) (by intros; norm_num) _ _ hi)
    (show (0 : ℝ) ≤ (1 / 2 : ℝ)^Q.card by positivity)
  convert hh using 1; ring

/-- The two remaining processes factor into the high no-change mass and
exactly their two independent low addition laws. -/
theorem noHighAdditionAverage_pair_eq (P Q : Finset ℕ) (hd : Disjoint P Q)
    (q r : ℕ → ℝ) (k : ℝ) (F : Finset ℕ → Finset ℕ → ℝ) :
    noHighAdditionAverage P Q r k (fun V => noHighAdditionAverage P Q q k (fun U => F U V)) =
      highNoAdditionMass Q r k * highNoAdditionMass Q q k *
        subsetAverage P (fun p => r p / 2) (fun V => subsetAverage P (fun p => q p / 2) (fun U => F U V)) := by
  rw [noHighAdditionAverage_eq P Q hd]
  simp_rw [noHighAdditionAverage_eq P Q hd]
  rw [subsetAverage_const_mul]
  ring

end JointDickman

end OAI
