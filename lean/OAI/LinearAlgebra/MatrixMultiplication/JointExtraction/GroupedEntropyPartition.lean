import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.NativeGroupedEntropy

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointGroupedEntropyPartition

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open JointNativeGroupedEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

section FiniteGroups

variable {U K A : Type*} [Fintype U] [Fintype K] [Fintype A]

omit [Fintype K] in
theorem groupMass_mul (s : ℝ) (p : U → ℝ) (group : U → K) (k : K) :
    JointCompatibilityIncidence.groupMass (fun u => s * p u) group k =
      s * JointCompatibilityIncidence.groupMass p group k := by
  unfold JointCompatibilityIncidence.groupMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : group u = k <;> simp [hu]

omit [Fintype K] [Fintype A] in
theorem groupMeasure_mul (s : ℝ) (p : U → ℝ) (group : U → K)
    (q : U → A → ℝ) (k : K) :
    groupMeasure (fun u => s * p u) group q k =
      fun a => s * groupMeasure p group q k a := by
  funext a
  unfold groupMeasure
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : group u = k <;> simp [hu, mul_assoc]

omit [Fintype K] [Fintype A] in
theorem groupLaw_mul_of_ne_zero (s : ℝ) (hs : s ≠ 0) (p : U → ℝ)
    (group : U → K) (q : U → A → ℝ) (k : K) :
    JointCompatibilityIncidence.groupLaw (fun u => s * p u) group q k =
      JointCompatibilityIncidence.groupLaw p group q k := by
  funext a
  change groupMeasure (fun u => s * p u) group q k a /
      JointCompatibilityIncidence.groupMass (fun u => s * p u) group k =
    groupMeasure p group q k a / JointCompatibilityIncidence.groupMass p group k
  rw [groupMeasure_mul, groupMass_mul]
  exact mul_div_mul_left _ _ hs

theorem groupedEntropy_mul (s : ℝ) (p : U → ℝ) (group : U → K)
    (q : U → A → ℝ) :
    JointCompatibilityIncidence.groupedEntropy (fun u => s * p u) group q =
      s * JointCompatibilityIncidence.groupedEntropy p group q := by
  by_cases hs : s = 0
  · simp [hs, JointCompatibilityIncidence.groupedEntropy,
      JointCompatibilityIncidence.groupMass]
  · unfold JointCompatibilityIncidence.groupedEntropy
    simp only [groupMass_mul, groupLaw_mul_of_ne_zero s hs, mul_assoc, Finset.mul_sum]

omit [Fintype A] in
theorem groupMeasure_designated_some (p : U → ℝ) (d : U → Prop)
    (q : U → A → ℝ) (u : U) :
    groupMeasure p (JointCompatibilityIncidence.designatedGroup d) q (some u) =
      fun a => if d u then p u * q u a else 0 := by
  funext a
  simp only [groupMeasure, JointCompatibilityIncidence.designatedGroup_eq_some]
  by_cases hu : d u <;> simp [hu]

omit [Fintype A] in
theorem groupMeasure_designated_none (p : U → ℝ) (d : U → Prop)
    (q : U → A → ℝ) :
    groupMeasure p (JointCompatibilityIncidence.designatedGroup d) q none =
      fun a => ∑ u, if ¬ d u then p u * q u a else 0 := by
  funext a
  simp only [groupMeasure, JointCompatibilityIncidence.designatedGroup_eq_none]

theorem groupedEntropy_designated (p : U → ℝ) (d : U → Prop)
    (q : U → A → ℝ) (hp : ∀ u, 0 ≤ p u) (hq : ∀ u, ∑ a, q u a = 1) :
    JointCompatibilityIncidence.groupedEntropy p
        (JointCompatibilityIncidence.designatedGroup d) q =
      (∑ u, if d u then p u * homogeneousEntropy (q u) else 0) +
      homogeneousEntropy (fun a => ∑ u, if ¬ d u then p u * q u a else 0) := by
  rw [groupedEntropy_eq_sum_homogeneous p _ q hp hq, Fintype.sum_option,
    groupMeasure_designated_none, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [groupMeasure_designated_some]
  by_cases hu : d u
  · simp only [hu, ite_true]
    exact homogeneousEntropy_mul_normalized (p u) (q u) (hq u)
  · simp only [hu, ite_false, homogeneousEntropy_zero]

theorem groupedEntropy_partition (p : U → ℝ) (d : U → Prop) (weight : U → K)
    (q : U → A → ℝ) (hp : ∀ u, 0 ≤ p u) (hq : ∀ u, ∑ a, q u a = 1) :
    JointCompatibilityIncidence.groupedEntropy p (singletonResidualGroup d weight) q =
      ∑ k, JointCompatibilityIncidence.groupedEntropy
        (fun u => if weight u = k then p u else 0)
        (JointCompatibilityIncidence.designatedGroup d) q := by
  have hclass (k : K) := groupedEntropy_designated
    (fun u => if weight u = k then p u else 0) d q
    (fun u => by split_ifs; exact hp u; exact le_rfl) hq
  rw [groupedEntropy_singletons_residuals p d weight q hp hq]
  simp_rw [hclass]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro u _
    by_cases hu : d u <;> simp [hu, ite_mul]
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    funext a
    apply Finset.sum_congr rfl
    intro u _
    by_cases hd : d u <;> by_cases hw : weight u = k <;> simp [hd, hw]

theorem groupedEntropy_conditional_partition (p : FiniteLaw U) (d : U → Prop)
    (weight : U → K) (q : U → A → ℝ) (hq : ∀ u, ∑ a, q u a = 1) :
    JointCompatibilityIncidence.groupedEntropy p.mass (singletonResidualGroup d weight) q =
      ∑ k, (p.map weight).mass k *
        JointCompatibilityIncidence.groupedEntropy (p.conditional weight k).mass
          (JointCompatibilityIncidence.designatedGroup d) q := by
  rw [groupedEntropy_partition p.mass d weight q p.nonneg hq]
  apply Finset.sum_congr rfl
  intro k _
  have hm : (fun u => if weight u = k then p.mass u else 0) =
      fun u => (p.map weight).mass k * (p.conditional weight k).mass u := by
    funext u
    exact (p.map_mass_mul_conditional weight k u).symm
  rw [hm, groupedEntropy_mul]

end FiniteGroups

section NativeSupport

variable {A : Type*} [Fintype A]

theorem native_groupedEntropy_eq_sum_masked (support : List Shape) (p : Shape → ℝ)
    (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ)
    (hbound : ∀ i : SupportIndex support, support[i.val] (priority position) < 17)
    (hp : ∀ i : SupportIndex support, 0 ≤ p support[i.val])
    (hq : ∀ i : SupportIndex support, ∑ a, q support[i.val] a = 1) :
    AllFieldNativeCapacity.groupedEntropy support p priority position q =
      ∑ k : Fin 17, JointCompatibilityIncidence.groupedEntropy
        (fun i : SupportIndex support =>
          if ownWeight support priority position hbound i = k then p support[i.val] else 0)
        (JointCompatibilityIncidence.designatedGroup
          (fun i => AllFieldNativeCapacity.designated priority position support[i.val]))
        (fun i => q support[i.val]) := by
  have hpart := groupedEntropy_partition (fun i : SupportIndex support => p support[i.val])
      (fun i => AllFieldNativeCapacity.designated priority position support[i.val])
      (ownWeight support priority position hbound) (fun i => q support[i.val]) hp hq
  refine (groupedEntropy_eq_native support p priority position q hbound hp hq).symm.trans
    (hpart.trans ?_)
  apply Finset.sum_congr rfl
  intro k _
  apply congrArg (fun weights : SupportIndex support → ℝ =>
    JointCompatibilityIncidence.groupedEntropy weights
      (JointCompatibilityIncidence.designatedGroup
        (fun i => AllFieldNativeCapacity.designated priority position support[i.val]))
      (fun i => q support[i.val]))
  funext i
  by_cases hi : ownWeight support priority position hbound i = k <;> simp only [hi, ite_true, ite_false]

theorem native_groupedEntropy_eq_sum_conditional (support : List Shape) (p : Shape → ℝ)
    (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ)
    (hbound : ∀ i : SupportIndex support, support[i.val] (priority position) < 17)
    (law : FiniteLaw (SupportIndex support))
    (hlaw : ∀ i : SupportIndex support, law.mass i = p support[i.val])
    (hq : ∀ i : SupportIndex support, ∑ a, q support[i.val] a = 1) :
    AllFieldNativeCapacity.groupedEntropy support p priority position q =
      ∑ k : Fin 17, (law.map (ownWeight support priority position hbound)).mass k *
        JointCompatibilityIncidence.groupedEntropy
          (law.conditional (ownWeight support priority position hbound) k).mass
          (JointCompatibilityIncidence.designatedGroup
            (fun i => AllFieldNativeCapacity.designated priority position support[i.val]))
          (fun i => q support[i.val]) := by
  have hp (i : SupportIndex support) : 0 ≤ p support[i.val] := by
    rw [← hlaw i]
    exact law.nonneg i
  have hm : law.mass = fun i : SupportIndex support => p support[i.val] := funext hlaw
  have hn : JointCompatibilityIncidence.groupedEntropy law.mass
      (nativeGroup support priority position hbound) (fun i => q support[i.val]) =
      AllFieldNativeCapacity.groupedEntropy support p priority position q := by
    rw [hm]
    exact groupedEntropy_eq_native support p priority position q hbound hp hq
  exact hn.symm.trans (groupedEntropy_conditional_partition law _ _ _ hq)

end NativeSupport

end MatrixMultiplication.JointGroupedEntropyPartition

end

end OAI
