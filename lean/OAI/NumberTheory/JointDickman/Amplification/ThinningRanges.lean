import OAI.NumberTheory.JointDickman.Amplification.SubsetThinning

namespace OAI

/-! # Factoring the remaining-set and second-coin law by prime range -/

namespace JointDickman

open Finset

theorem sum_powerset_partition {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hd : Disjoint P Q) (F : Finset α → ℝ) :
    (∑ S ∈ (P ∪ Q).powerset, F S) = ∑ A ∈ P.powerset, ∑ D ∈ Q.powerset, F (A ∪ D) := by
  classical
  have he := (subsetPartitionEquiv P Q hd).symm.sum_comp (fun S : (P ∪ Q).powerset => F S.val)
  rw [Fintype.sum_prod_type] at he
  calc
    _ = ∑ S : (P ∪ Q).powerset, F S.val := (sum_coe_sort _ _).symm
    _ = ∑ A : P.powerset, ∑ D : Q.powerset, F (A.val ∪ D.val) := he.symm
    _ = _ := (sum_coe_sort P.powerset (fun A => ∑ D : Q.powerset, F (A ∪ D.val))).trans
      (sum_congr rfl (fun A _ => sum_coe_sort Q.powerset (fun D => F (A ∪ D))))

theorem subsetRetentionMass_union {α : Type*} [DecidableEq α]
    {P Q S R U V : Finset α} (hd : Disjoint P Q)
    (hS : S ⊆ P) (hR : R ⊆ Q) (hU : U ⊆ P) (hV : V ⊆ Q) :
    subsetRetentionMass (S ∪ R) (U ∪ V) = subsetRetentionMass S U * subsetRetentionMass R V := by
  classical
  have hu : U ∪ V ⊆ S ∪ R ↔ U ⊆ S ∧ V ⊆ R := by
    constructor
    · intro h
      constructor
      · intro p hp
        rcases mem_union.mp (h (mem_union_left V hp)) with hs | hr
        · exact hs
        · exact False.elim (disjoint_left.mp hd (hU hp) (hR hr))
      · intro p hp
        rcases mem_union.mp (h (mem_union_right U hp)) with hs | hr
        · exact False.elim (disjoint_left.mp hd (hS hs) (hV hp))
        · exact hr
    · rintro ⟨hu, hv⟩
      exact union_subset_union hu hv
  have hc := card_union_of_disjoint (hd.mono hS hR)
  by_cases hus : U ⊆ S <;> by_cases hvr : V ⊆ R <;>
    simp [subsetRetentionMass, hu, hus, hvr, hc, pow_add]

noncomputable def jointRetentionMass {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (S T : Finset α) : ℝ :=
  bernoulliSubsetMass P q S * subsetRetentionMass S T

theorem jointRetentionMass_union {α : Type*} [DecidableEq α]
    {P Q S R U V : Finset α} (hd : Disjoint P Q)
    (hS : S ⊆ P) (hR : R ⊆ Q) (hU : U ⊆ P) (hV : V ⊆ Q) (q : α → ℝ) :
    jointRetentionMass (P ∪ Q) q (S ∪ R) (U ∪ V) =
      jointRetentionMass P q S U * jointRetentionMass Q q R V := by
  unfold jointRetentionMass
  rw [bernoulliSubsetMass_union hd hS hR, subsetRetentionMass_union hd hS hR hU hV]
  ring

/-- The joint law factors before imposing any event. This keeps the order
of high-prime exposure and low-prime averaging explicit. -/
theorem jointRetentionMass_partition {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hd : Disjoint P Q) (q : α → ℝ) (F : Finset α → Finset α → ℝ) :
    (∑ S ∈ (P ∪ Q).powerset, ∑ T ∈ (P ∪ Q).powerset,
      jointRetentionMass (P ∪ Q) q S T * F S T) =
      ∑ S ∈ P.powerset, ∑ R ∈ Q.powerset, ∑ U ∈ P.powerset, ∑ V ∈ Q.powerset,
        jointRetentionMass P q S U * jointRetentionMass Q q R V * F (S ∪ R) (U ∪ V) := by
  rw [sum_powerset_partition P Q hd]
  apply sum_congr rfl
  intro S hS
  apply sum_congr rfl
  intro R hR
  rw [sum_powerset_partition P Q hd]
  apply sum_congr rfl
  intro U hU
  apply sum_congr rfl
  intro V hV
  rw [jointRetentionMass_union hd (mem_powerset.mp hS) (mem_powerset.mp hR)
    (mem_powerset.mp hU) (mem_powerset.mp hV)]

open Classical in
/-- A lower bound on the number of exposed remaining primes bounds the
chance that none of their fair second coins adds a prime. -/
theorem remaining_high_no_addition_bound {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (k : ℝ)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    (∑ S ∈ P.powerset, if k ≤ (S.card : ℝ) then jointRetentionMass P q S ∅ else 0) ≤
      (1 / 2 : ℝ)^k := by
  have hpow {n : ℕ} (hn : k ≤ (n : ℝ)) : (1 / 2 : ℝ)^n ≤ (1 / 2 : ℝ)^k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hn
  calc
    _ ≤ ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * (1 / 2 : ℝ)^k := by
      apply sum_le_sum
      intro S hS
      have hm := bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq
      split_ifs with hs
      · unfold jointRetentionMass subsetRetentionMass
        simp only [empty_subset, ite_true]
        exact mul_le_mul_of_nonneg_left (hpow hs) hm
      · exact mul_nonneg hm (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by rw [← sum_mul, bernoulliSubsetMass_sum, one_mul]

end JointDickman

end OAI
