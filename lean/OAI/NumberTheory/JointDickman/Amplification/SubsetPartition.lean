import OAI.NumberTheory.JointDickman.Amplification.ProductComparison

namespace OAI

/-! # Exact splitting of independent prime choices into two ranges -/

namespace JointDickman

open Finset

noncomputable def subsetPartitionEquiv {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hd : Disjoint P Q) :
    (P ∪ Q).powerset ≃ P.powerset × Q.powerset where
  toFun S := (⟨S.val ∩ P, mem_powerset.mpr inter_subset_right⟩,
    ⟨S.val ∩ Q, mem_powerset.mpr inter_subset_right⟩)
  invFun AB := ⟨AB.1.val ∪ AB.2.val, mem_powerset.mpr
    (union_subset_union (mem_powerset.mp AB.1.property) (mem_powerset.mp AB.2.property))⟩
  left_inv S := by
    apply Subtype.ext
    ext p
    have hs := mem_powerset.mp S.property
    simp only [mem_union, mem_inter]
    constructor
    · tauto
    · intro hp
      exact (mem_union.mp (hs hp)).elim (fun h => Or.inl ⟨hp, h⟩) (fun h => Or.inr ⟨hp, h⟩)
  right_inv AB := by
    apply Prod.ext <;> apply Subtype.ext <;> ext p
    · have ha := mem_powerset.mp AB.1.property
      have hb := mem_powerset.mp AB.2.property
      simp only [mem_union, mem_inter]
      constructor
      · rintro ⟨hp | hp, hP⟩
        · exact hp
        · exact False.elim (disjoint_left.mp hd hP (hb hp))
      · intro hp
        exact ⟨Or.inl hp, ha hp⟩
    · have ha := mem_powerset.mp AB.1.property
      have hb := mem_powerset.mp AB.2.property
      simp only [mem_union, mem_inter]
      constructor
      · rintro ⟨hp | hp, hQ⟩
        · exact False.elim (disjoint_left.mp hd (ha hp) hQ)
        · exact hp
      · intro hp
        exact ⟨Or.inr hp, hb hp⟩

theorem bernoulliSubsetMass_union {α : Type*} [DecidableEq α]
    {P Q A D : Finset α} (hd : Disjoint P Q) (hA : A ⊆ P) (hD : D ⊆ Q)
    (q : α → ℝ) :
    bernoulliSubsetMass (P ∪ Q) q (A ∪ D) =
      bernoulliSubsetMass P q A * bernoulliSubsetMass Q q D := by
  classical
  have had : Disjoint A D := hd.mono hA hD
  have hdiff : (P ∪ Q) \ (A ∪ D) = (P \ A) ∪ (Q \ D) := by
    ext p
    simp only [mem_sdiff, mem_union]
    have hAP := @hA p
    have hDQ := @hD p
    have hn : ¬(p ∈ P ∧ p ∈ Q) := fun h => disjoint_left.mp hd h.1 h.2
    tauto
  have hdd : Disjoint (P \ A) (Q \ D) := hd.mono sdiff_subset sdiff_subset
  unfold bernoulliSubsetMass
  rw [hdiff, prod_union had, prod_union hdd]
  ring

/-- Arbitrary tests factor exactly after splitting the prime range. -/
theorem bernoulliSubsetMass_partition_sum {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hd : Disjoint P Q) (q : α → ℝ) (F : Finset α → ℝ) :
    (∑ S ∈ (P ∪ Q).powerset, bernoulliSubsetMass (P ∪ Q) q S * F S) =
      ∑ A ∈ P.powerset, ∑ D ∈ Q.powerset,
        bernoulliSubsetMass P q A * bernoulliSubsetMass Q q D * F (A ∪ D) := by
  classical
  have he := (subsetPartitionEquiv P Q hd).symm.sum_comp
    (fun S : (P ∪ Q).powerset => bernoulliSubsetMass (P ∪ Q) q S.val * F S.val)
  rw [Fintype.sum_prod_type] at he
  calc
    _ = ∑ S : (P ∪ Q).powerset, bernoulliSubsetMass (P ∪ Q) q S.val * F S.val :=
      (sum_coe_sort _ _).symm
    _ = ∑ A : P.powerset, ∑ D : Q.powerset,
        bernoulliSubsetMass (P ∪ Q) q (A.val ∪ D.val) * F (A.val ∪ D.val) := he.symm
    _ = ∑ A ∈ P.powerset, ∑ D ∈ Q.powerset,
        bernoulliSubsetMass (P ∪ Q) q (A ∪ D) * F (A ∪ D) := by
      exact (sum_coe_sort P.powerset (fun A => ∑ D : Q.powerset,
        bernoulliSubsetMass (P ∪ Q) q (A ∪ D.val) * F (A ∪ D.val))).trans
        (sum_congr rfl (fun A _ => sum_coe_sort Q.powerset
          (fun D => bernoulliSubsetMass (P ∪ Q) q (A ∪ D) * F (A ∪ D))))
    _ = _ := by
      apply sum_congr rfl
      intro A hA
      apply sum_congr rfl
      intro D hD
      rw [bernoulliSubsetMass_union hd (mem_powerset.mp hA) (mem_powerset.mp hD)]

/-- The selected high-range subset has its own Bernoulli law, independent
of all choices in the complementary range. -/
theorem bernoulliSubsetMass_projection {α : Type*} [DecidableEq α]
    (P Q D : Finset α) (hQ : Q ⊆ P) (hD : D ⊆ Q) (q : α → ℝ) :
    (∑ S ∈ P.powerset, if S ∩ Q = D then bernoulliSubsetMass P q S else 0) =
      bernoulliSubsetMass Q q D := by
  classical
  have hd : Disjoint (P \ Q) Q := disjoint_sdiff_self_left
  have hu : (P \ Q) ∪ Q = P := sdiff_union_of_subset hQ
  have hrewrite : (∑ S ∈ P.powerset, if S ∩ Q = D then bernoulliSubsetMass P q S else 0) =
      ∑ S ∈ ((P \ Q) ∪ Q).powerset,
        bernoulliSubsetMass ((P \ Q) ∪ Q) q S * (if S ∩ Q = D then 1 else 0) := by
    rw [hu]
    apply sum_congr rfl
    intro S _
    split_ifs <;> simp only [mul_one, mul_zero]
  rw [hrewrite, bernoulliSubsetMass_partition_sum _ _ hd]
  have hinter (A E : Finset α) (hA : A ⊆ P \ Q) (hE : E ⊆ Q) : (A ∪ E) ∩ Q = E := by
    ext p
    have han : p ∈ A → p ∉ Q := fun hp => (mem_sdiff.mp (hA hp)).2
    have heq := @hE p
    simp only [mem_inter, mem_union]
    tauto
  calc
    _ = ∑ A ∈ (P \ Q).powerset, bernoulliSubsetMass (P \ Q) q A * bernoulliSubsetMass Q q D := by
      apply sum_congr rfl
      intro A hA
      calc
        _ = ∑ E ∈ Q.powerset, bernoulliSubsetMass (P \ Q) q A *
            bernoulliSubsetMass Q q E * (if E = D then 1 else 0) := by
          apply sum_congr rfl
          intro E hE
          rw [hinter A E (mem_powerset.mp hA) (mem_powerset.mp hE)]
        _ = _ := by simp only [mul_ite, mul_one, mul_zero, sum_ite_eq',
          mem_powerset.mpr hD, ite_true]

    _ = _ := by rw [← sum_mul, bernoulliSubsetMass_sum, one_mul]

end JointDickman

end OAI
