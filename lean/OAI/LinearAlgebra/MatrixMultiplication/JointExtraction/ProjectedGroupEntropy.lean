import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CompatibilityRateLimit
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CompatibilityControls
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.GroupedEntropyPartition

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointProjectedGroupEntropy

open MatrixMultiplication.Foundation JointCompatibilityIncidence
open JointCompatibilityScaling JointCompatibilityControls JointCompatibilityRateLimit
open JointGroupedEntropyPartition
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

section FiniteGroups

variable {U K A : Type*} [Fintype U] [Fintype K] [Fintype A]

theorem groupMass_designated_some (p : U → ℝ) (d : U → Prop) (u : U) :
    groupMass p (designatedGroup d) (some u) = if d u then p u else 0 := by
  simp only [groupMass, designatedGroup_eq_some]
  by_cases hd : d u <;> simp [hd]

theorem weighted_groupLaw_designated_some (p : U → ℝ) (d : U → Prop)
    (law : U → A → ℝ) (u : U) :
    groupMass p (designatedGroup d) (some u) *
        finiteEntropy (groupLaw p (designatedGroup d) law (some u)) =
      (if d u then p u else 0) * finiteEntropy (law u) := by
  by_cases hd : d u
  · rw [groupMass_designated_some, ite_eq_left hd]
    by_cases hp : p u = 0
    · simp [hp]
    · have hl : groupLaw p (designatedGroup d) law (some u) = law u := by
        funext a
        simp [groupLaw, groupMass_designated_some, designatedGroup_eq_some, hd, hp]
      rw [hl]
  · rw [groupMass_designated_some, ite_eq_right hd]
    simp

theorem groupedEntropy_counts_eq_total_mul (n : U → ℕ) (group : U → K)
    (law : U → A → ℝ) :
    groupedEntropy (fun u => (n u : ℝ)) group law =
      (∑ u, n u : ℕ) *
        groupedEntropy (fun u => (n u : ℝ) / (∑ v, n v : ℕ)) group law := by
  by_cases hz : (∑ u, n u) = 0
  · have hn (u : U) : n u = 0 := by
      have hle : n u ≤ ∑ v, n v :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
      rw [hz] at hle
      exact Nat.eq_zero_of_le_zero hle
    simp [hn, groupedEntropy, groupMass]
  · have hN : ((∑ u, n u : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hz
    have hf : (fun u => (n u : ℝ)) =
        fun u => ((∑ v, n v : ℕ) : ℝ) * ((n u : ℝ) / (∑ v, n v : ℕ)) := by
      funext u
      exact (mul_div_cancel₀ _ hN).symm
    calc
      _ = groupedEntropy
          (fun u => ((∑ v, n v : ℕ) : ℝ) * ((n u : ℝ) / (∑ v, n v : ℕ)))
          group law := congrArg (fun p => groupedEntropy p group law) hf
      _ = _ := groupedEntropy_mul _ _ _ _

end FiniteGroups

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape A : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

omit [Fintype C] [DecidableEq C] in
theorem baseGroupSize_eq_groupMass (base : ∀ c, Shape c → ℕ)
    (d : ∀ c, Shape c → Prop) (g : Σ c, Option (Shape c)) :
    (baseGroupSize base d g : ℝ) =
      groupMass (fun u => (base g.1 u : ℝ)) (designatedGroup (d g.1)) g.2 := by
  calc
    (baseGroupSize base d g : ℝ) =
        ∑ u ∈ Finset.univ.filter (fun u => designatedGroup (d g.1) u = g.2),
          (base g.1 u : ℝ) := by
      rw [baseGroupSize, Nat.cast_sum]
      exact (Finset.sum_subtype
        (Finset.univ.filter (fun u => designatedGroup (d g.1) u = g.2))
        (by simp) (fun u => (base g.1 u : ℝ))).symm
    _ = ∑ u, if designatedGroup (d g.1) u = g.2 then (base g.1 u : ℝ) else 0 := by
      rw [Finset.sum_filter]
    _ = _ := by
      unfold groupMass
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : designatedGroup (d g.1) u = g.2 <;> simp only [hu, ite_true, ite_false]

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
theorem residualCenter_eq_groupLaw (base : ∀ c, Shape c → ℕ)
    (d : ∀ c, Shape c → Prop) (law : ∀ c, Shape c → A c → ℝ) (c : C) :
    residualCenter base d law c =
      groupLaw (fun u => (base c u : ℝ)) (designatedGroup (d c)) (law c) none := by
  funext a
  simp only [residualCenter, residualBase, Nat.cast_sum, groupLaw, groupMass,
    designatedGroup_eq_none]
  congr 1
  · rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (fun u => ¬ d c u))
      (by simp) (fun u => (base c u : ℝ) * law c u a)).symm
  · rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (fun u => ¬ d c u))
      (by simp) (fun u => (base c u : ℝ))).symm

omit [DecidableEq C] [∀ c, DecidableEq (A c)] in
theorem projectedReferenceEntropy_eq_sum_counts_groupedEntropy
    (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) :
    projectedReferenceEntropy base d (groupCap base d law 0) =
      ∑ c, groupedEntropy (fun u => (base c u : ℝ))
        (designatedGroup (d c)) (law c) := by
  simp only [projectedReferenceEntropy, Fintype.sum_sigma, groupCap, add_zero,
    groupedEntropy]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro k _
  rw [baseGroupSize_eq_groupMass]
  cases k with
  | none =>
      change _ * finiteEntropy (residualCenter base d law c) = _
      rw [residualCenter_eq_groupLaw]
  | some u =>
      change _ * finiteEntropy (law c u) = _
      rw [weighted_groupLaw_designated_some, groupMass_designated_some]

omit [DecidableEq C] [∀ c, DecidableEq (A c)] in
theorem projectedReferenceEntropy_eq_sum_weighted_groupedEntropy
    (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) :
    projectedReferenceEntropy base d (groupCap base d law 0) =
      ∑ c, (baseSize base c : ℝ) *
        groupedEntropy (fun u => (base c u : ℝ) / (baseSize base c : ℝ))
          (designatedGroup (d c)) (law c) := by
  rw [projectedReferenceEntropy_eq_sum_counts_groupedEntropy]
  apply Finset.sum_congr rfl
  intro c _
  exact groupedEntropy_counts_eq_total_mul (base c) _ _

end MatrixMultiplication.JointProjectedGroupEntropy

end

end OAI
