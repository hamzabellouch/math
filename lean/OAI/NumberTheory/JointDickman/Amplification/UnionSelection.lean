import OAI.NumberTheory.JointDickman.Amplification.RootSelection

namespace OAI

/-! # Independent selection of finite forbidden sets -/

namespace JointDickman

open Finset

/-- Independent form choices work equally for finite sets of zeros, such
as lines in a residue plane. Intersections between the sets cause no loss. -/
theorem bernoulli_union_survival {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (F : ι → Finset α) (θ : ι → ℝ) (x : α) :
    (∑ S ∈ I.powerset, bernoulliSubsetMass I (fun i => 1 - θ i) S *
      (if x ∈ S.biUnion F then 0 else 1)) =
      ∏ i ∈ I.filter (fun i => x ∈ F i), θ i := by
  classical
  let E := I.filter (fun i => x ∈ F i)
  have hid (S : Finset ι) (hS : S ⊆ I) :
      avoidsSelected S E = if x ∈ S.biUnion F then 0 else 1 := by
    have hiff : Disjoint S E ↔ x ∉ S.biUnion F := by
      constructor
      · intro h hx
        obtain ⟨i, hiS, hi⟩ := mem_biUnion.mp hx
        exact disjoint_left.mp h hiS (mem_filter.mpr ⟨hS hiS, hi⟩)
      · intro h
        apply disjoint_left.mpr
        intro i hiS hiE
        exact h (mem_biUnion.mpr ⟨i, hiS, (mem_filter.mp hiE).2⟩)
    unfold avoidsSelected
    by_cases hx : x ∈ S.biUnion F
    · have hn : ¬ Disjoint S E := fun h => (hiff.mp h) hx
      simp [hn, hx]
    · simp [hiff.mpr hx, hx]
  have h := bernoulliSubsetMass_avoids I E (filter_subset _ _) θ
  apply Eq.trans _ h
  apply sum_congr rfl
  intro S hS
  rw [hid S (mem_powerset.mp hS)]

/-- The mean density of the surviving residue set is the exact residue
average of all retained form weights. -/
theorem bernoulli_union_density {ι α : Type*} [DecidableEq ι]
    [Fintype α] [DecidableEq α] (hα : 0 < Fintype.card α)
    (I : Finset ι) (F : ι → Finset α) (θ : ι → ℝ) :
    (∑ S ∈ I.powerset, bernoulliSubsetMass I (fun i => 1 - θ i) S *
      (1 - ((S.biUnion F).card : ℝ) / Fintype.card α)) =
      (∑ x : α, ∏ i ∈ I.filter (fun i => x ∈ F i), θ i) / Fintype.card α := by
  simp_rw [← root_survival_mean hα, ← mul_div_assoc]
  rw [← sum_div]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  exact bernoulli_union_survival I F θ x

end JointDickman

end OAI
