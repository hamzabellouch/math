import OAI.NumberTheory.JointDickman.Amplification.ThinningRanges

namespace OAI

/-! # Averaging high second coins after the low addition product -/

namespace JointDickman

open Finset

theorem partition_union_inter_left {α : Type*} [DecidableEq α]
    {P Q A D : Finset α} (hd : Disjoint P Q) (hA : A ⊆ P) (hD : D ⊆ Q) :
    (A ∪ D) ∩ P = A := by
  ext p
  have ha := @hA p
  have hn : p ∈ D → p ∉ P := fun hp hpp => disjoint_left.mp hd hpp (hD hp)
  simp only [mem_inter, mem_union]
  tauto

theorem partition_union_inter_right {α : Type*} [DecidableEq α]
    {P Q A D : Finset α} (hd : Disjoint P Q) (hA : A ⊆ P) (hD : D ⊆ Q) :
    (A ∪ D) ∩ Q = D := by
  rw [union_comm]
  exact partition_union_inter_left hd.symm hD hA

open Classical in
noncomputable def highNoAdditionMass {α : Type*} [DecidableEq α]
    (Q : Finset α) (q : α → ℝ) (k : ℝ) : ℝ :=
  ∑ R ∈ Q.powerset, if k ≤ (R.card : ℝ) then jointRetentionMass Q q R ∅ else 0

open Classical in
/-- The high tail restriction and no high additions leave the low addition
law unchanged. In particular, this identity does not condition high second
coins on the low-ratio event. -/
theorem high_low_thinning_factor {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hd : Disjoint P Q) (q : α → ℝ) (k : ℝ) (F : Finset α → ℝ) :
    (∑ S ∈ (P ∪ Q).powerset, ∑ T ∈ (P ∪ Q).powerset,
      jointRetentionMass (P ∪ Q) q S T *
        (if k ≤ ((S ∩ Q).card : ℝ) ∧ T ∩ Q = ∅ then F (T ∩ P) else 0)) =
      highNoAdditionMass Q q k *
        (∑ U ∈ P.powerset, bernoulliSubsetMass P (fun p => q p / 2) U * F U) := by
  classical
  rw [jointRetentionMass_partition P Q hd]
  have hinner (S R U : Finset α) (hS : S ⊆ P) (hR : R ⊆ Q) (hU : U ⊆ P) :
      (∑ V ∈ Q.powerset, jointRetentionMass P q S U * jointRetentionMass Q q R V *
        (if k ≤ (((S ∪ R) ∩ Q).card : ℝ) ∧ (U ∪ V) ∩ Q = ∅ then F ((U ∪ V) ∩ P) else 0)) =
      jointRetentionMass P q S U * (if k ≤ (R.card : ℝ) then jointRetentionMass Q q R ∅ else 0) * F U := by
    have heq (V : Finset α) (hV : V ∈ Q.powerset) :
        jointRetentionMass P q S U * jointRetentionMass Q q R V *
          (if k ≤ (((S ∪ R) ∩ Q).card : ℝ) ∧ (U ∪ V) ∩ Q = ∅ then F ((U ∪ V) ∩ P) else 0) =
        if V = ∅ then
          jointRetentionMass P q S U * (if k ≤ (R.card : ℝ) then jointRetentionMass Q q R ∅ else 0) * F U
        else 0 := by
      rw [partition_union_inter_right hd hS hR,
        partition_union_inter_right hd hU (mem_powerset.mp hV),
        partition_union_inter_left hd hU (mem_powerset.mp hV)]
      by_cases hv : V = ∅ <;> by_cases hk : k ≤ (R.card : ℝ) <;> simp [hv, hk]
    rw [sum_congr rfl heq]
    simp only [sum_ite_eq', empty_mem_powerset, ite_true]
  calc
    _ = ∑ S ∈ P.powerset, ∑ R ∈ Q.powerset, ∑ U ∈ P.powerset,
        jointRetentionMass P q S U * (if k ≤ (R.card : ℝ) then jointRetentionMass Q q R ∅ else 0) * F U := by
      apply sum_congr rfl
      intro S hS
      apply sum_congr rfl
      intro R hR
      apply sum_congr rfl
      intro U hU
      exact hinner S R U (mem_powerset.mp hS) (mem_powerset.mp hR) (mem_powerset.mp hU)
    _ = highNoAdditionMass Q q k *
        (∑ S ∈ P.powerset, ∑ U ∈ P.powerset, jointRetentionMass P q S U * F U) := by
      unfold highNoAdditionMass
      rw [sum_comm]
      rw [sum_mul]
      apply sum_congr rfl
      intro R _
      simp only [mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro U _
      ring
    _ = _ := by
      congr 1
      simpa only [jointRetentionMass, ← mul_sum, mul_assoc] using subsetRetentionMass_expectation P q F


open Classical in
/-- The coefficient's high primes are all kept. Low coefficient coins
retain their original independent fair law. -/
theorem fixed_high_retention_factor {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hd : Disjoint P Q) (F : Finset α → ℝ) :
    (∑ S ∈ (P ∪ Q).powerset, bernoulliSubsetMass (P ∪ Q) (fun _ => (1 / 2 : ℝ)) S *
      (if S ∩ Q = Q then F (S ∩ P) else 0)) =
      (1 / 2 : ℝ)^Q.card * (∑ A ∈ P.powerset, bernoulliSubsetMass P (fun _ => (1 / 2 : ℝ)) A * F A) := by
  classical
  rw [bernoulliSubsetMass_partition_sum P Q hd]
  have hi (A : Finset α) (hA : A ⊆ P) :
      (∑ D ∈ Q.powerset,
        bernoulliSubsetMass P (fun _ => (1 / 2 : ℝ)) A *
          bernoulliSubsetMass Q (fun _ => (1 / 2 : ℝ)) D *
            (if (A ∪ D) ∩ Q = Q then F ((A ∪ D) ∩ P) else 0)) =
      (1 / 2 : ℝ)^Q.card * (bernoulliSubsetMass P (fun _ => (1 / 2 : ℝ)) A * F A) := by
    have he (D : Finset α) (hD : D ∈ Q.powerset) :
        bernoulliSubsetMass P (fun _ => (1 / 2 : ℝ)) A *
          bernoulliSubsetMass Q (fun _ => (1 / 2 : ℝ)) D *
            (if (A ∪ D) ∩ Q = Q then F ((A ∪ D) ∩ P) else 0) =
        if D = Q then bernoulliSubsetMass P (fun _ => (1 / 2 : ℝ)) A *
          bernoulliSubsetMass Q (fun _ => (1 / 2 : ℝ)) Q * F A else 0 := by
      rw [partition_union_inter_right hd hA (mem_powerset.mp hD),
        partition_union_inter_left hd hA (mem_powerset.mp hD)]
      split_ifs with h
      · rw [h]
      · exact mul_zero _
    rw [sum_congr rfl he]
    simp only [sum_ite_eq', mem_powerset.mpr (Subset.refl Q), ite_true,
      bernoulliSubsetMass_half (Subset.refl Q)]
    ring
  rw [sum_congr rfl (fun A hA => hi A (mem_powerset.mp hA)), mul_sum]

open Classical in
/-- A bounded low-addition test costs its own bound times the high no-change
factor, with no conditioning on the rare low event. -/
theorem high_low_thinning_bound {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hd : Disjoint P Q) (q : α → ℝ) (k K : ℝ) (hK : 0 ≤ K)
    (hq : ∀ p ∈ P ∪ Q, 0 ≤ q p ∧ q p ≤ 1) (F : Finset α → ℝ)
    (hF : (∑ U ∈ P.powerset, bernoulliSubsetMass P (fun p => q p / 2) U * F U) ≤ K) :
    (∑ S ∈ (P ∪ Q).powerset, ∑ T ∈ (P ∪ Q).powerset,
      jointRetentionMass (P ∪ Q) q S T *
        (if k ≤ ((S ∩ Q).card : ℝ) ∧ T ∩ Q = ∅ then F (T ∩ P) else 0)) ≤
      (1 / 2 : ℝ)^k * K := by
  rw [high_low_thinning_factor P Q hd]
  have hnonneg : 0 ≤ highNoAdditionMass Q q k := by
    unfold highNoAdditionMass
    apply sum_nonneg
    intro R hR
    split_ifs
    · unfold jointRetentionMass subsetRetentionMass
      simp only [empty_subset, ite_true]
      exact mul_nonneg (bernoulliSubsetMass_nonneg (mem_powerset.mp hR)
        (fun p hp => hq p (mem_union_right P hp))) (by positivity)
    · exact le_rfl
  exact (mul_le_mul_of_nonneg_left hF hnonneg).trans
    (mul_le_mul_of_nonneg_right (remaining_high_no_addition_bound Q q k
      (fun p hp => hq p (mem_union_right P hp))) hK)

end JointDickman

end OAI
