import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.GroupBranchDesignation
import OAI.LinearAlgebra.MatrixFields.Entropy.GroupCountRate
import OAI.LinearAlgebra.MatrixFields.Entropy.GroupPairEntropy

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointNativeGroupedEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

section FiniteGroups

variable {U K A : Type*} [Fintype U] [Fintype K] [Fintype A]

def groupMeasure (p : U → ℝ) (group : U → K) (q : U → A → ℝ)
    (k : K) (a : A) : ℝ :=
  ∑ u, if group u = k then p u * q u a else 0

omit [Fintype K] in
theorem groupMeasure_total (p : U → ℝ) (group : U → K) (q : U → A → ℝ)
    (hq : ∀ u, ∑ a, q u a = 1) (k : K) :
    ∑ a, groupMeasure p group q k a =
      JointCompatibilityIncidence.groupMass p group k := by
  unfold groupMeasure JointCompatibilityIncidence.groupMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : group u = k
  · simp only [hu, ite_true, ← Finset.mul_sum, hq, mul_one]
  · simp [hu]

omit [Fintype K] [Fintype A] in
theorem groupMeasure_zero_of_mass_zero (p : U → ℝ) (group : U → K)
    (q : U → A → ℝ) (hp : ∀ u, 0 ≤ p u) (k : K)
    (hm : JointCompatibilityIncidence.groupMass p group k = 0) :
    groupMeasure p group q k = fun _ => 0 := by
  have ht : ∀ u, (if group u = k then p u else 0) = 0 := by
    have hn : ∀ u ∈ (Finset.univ : Finset U),
        0 ≤ (if group u = k then p u else 0) := by
      intro u _
      split_ifs
      · exact hp u
      · exact le_rfl
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hm
    exact fun u => hz u (Finset.mem_univ u)
  funext a
  apply Finset.sum_eq_zero
  intro u _
  by_cases hu : group u = k
  · have hpu : p u = 0 := by simpa only [hu, ite_true] using ht u
    simp [hu, hpu]
  · simp [hu]

omit [Fintype K] in
theorem group_term_eq_homogeneous (p : U → ℝ) (group : U → K)
    (q : U → A → ℝ) (hp : ∀ u, 0 ≤ p u)
    (hq : ∀ u, ∑ a, q u a = 1) (k : K) :
    JointCompatibilityIncidence.groupMass p group k *
      finiteEntropy (JointCompatibilityIncidence.groupLaw p group q k) =
      homogeneousEntropy (groupMeasure p group q k) := by
  by_cases hm : JointCompatibilityIncidence.groupMass p group k = 0
  · rw [hm, zero_mul, groupMeasure_zero_of_mass_zero p group q hp k hm,
      homogeneousEntropy_zero]
  · have ht := groupMeasure_total p group q hq k
    have hn : ∑ a, groupMeasure p group q k a ≠ 0 := by rwa [ht]
    rw [homogeneousEntropy_eq_mass_mul _ hn, ht]
    rfl

theorem groupedEntropy_eq_sum_homogeneous (p : U → ℝ) (group : U → K)
    (q : U → A → ℝ) (hp : ∀ u, 0 ≤ p u)
    (hq : ∀ u, ∑ a, q u a = 1) :
    JointCompatibilityIncidence.groupedEntropy p group q =
      ∑ k, homogeneousEntropy (groupMeasure p group q k) := by
  unfold JointCompatibilityIncidence.groupedEntropy
  exact Finset.sum_congr rfl fun k _ => group_term_eq_homogeneous p group q hp hq k

theorem homogeneousEntropy_mul_normalized (s : ℝ) (q : A → ℝ)
    (hq : ∑ a, q a = 1) :
    homogeneousEntropy (fun a => s * q a) = s * homogeneousEntropy q := by
  have he : finiteEntropy (fun a => s * q a) =
      entropyTerm s + s * finiteEntropy q := by
    simp only [finiteEntropy, entropyTerm_mul, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hq, one_mul]
  rw [homogeneousEntropy, ← Finset.mul_sum, hq, mul_one, he,
    homogeneousEntropy_normalized q hq]
  unfold entropyTerm
  ring

def singletonResidualGroup (d : U → Prop) (weight : U → K) (u : U) : U ⊕ K :=
  if d u then Sum.inl u else Sum.inr (weight u)

omit [Fintype U] [Fintype K] in
theorem singletonResidualGroup_eq_inl (d : U → Prop) (weight : U → K)
    (u v : U) :
    singletonResidualGroup d weight v = Sum.inl u ↔ d u ∧ v = u := by
  constructor
  · intro h
    by_cases hv : d v
    · have he : v = u := by simpa [singletonResidualGroup, hv] using h
      exact ⟨he ▸ hv, he⟩
    · simp [singletonResidualGroup, hv] at h
  · rintro ⟨hu, rfl⟩
    simp [singletonResidualGroup, hu]

omit [Fintype U] [Fintype K] in
theorem singletonResidualGroup_eq_inr (d : U → Prop) (weight : U → K)
    (u : U) (k : K) :
    singletonResidualGroup d weight u = Sum.inr k ↔ ¬ d u ∧ weight u = k := by
  by_cases hu : d u <;> simp [singletonResidualGroup, hu]

omit [Fintype K] [Fintype A] in
theorem groupMeasure_singleton (p : U → ℝ) (d : U → Prop)
    (weight : U → K) (q : U → A → ℝ) (u : U) :
    groupMeasure p (singletonResidualGroup d weight) q (Sum.inl u) =
      fun a => if d u then p u * q u a else 0 := by
  funext a
  simp only [groupMeasure, singletonResidualGroup_eq_inl]
  by_cases hu : d u <;> simp [hu]

omit [Fintype K] [Fintype A] in
theorem groupMeasure_residual (p : U → ℝ) (d : U → Prop)
    (weight : U → K) (q : U → A → ℝ) (k : K) :
    groupMeasure p (singletonResidualGroup d weight) q (Sum.inr k) =
      fun a => ∑ u, if ¬ d u ∧ weight u = k then p u * q u a else 0 := by
  funext a
  simp only [groupMeasure, singletonResidualGroup_eq_inr]

theorem groupedEntropy_singletons_residuals (p : U → ℝ) (d : U → Prop)
    (weight : U → K) (q : U → A → ℝ) (hp : ∀ u, 0 ≤ p u)
    (hq : ∀ u, ∑ a, q u a = 1) :
    JointCompatibilityIncidence.groupedEntropy p (singletonResidualGroup d weight) q =
      (∑ u, if d u then p u * homogeneousEntropy (q u) else 0) +
      ∑ k, homogeneousEntropy (fun a =>
        ∑ u, if ¬ d u ∧ weight u = k then p u * q u a else 0) := by
  rw [groupedEntropy_eq_sum_homogeneous p _ q hp hq, Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro u _
    rw [groupMeasure_singleton]
    by_cases hu : d u
    · simp only [hu, ite_true]
      exact homogeneousEntropy_mul_normalized (p u) (q u) (hq u)
    · simp only [hu, ite_false, homogeneousEntropy_zero]
  · apply Finset.sum_congr rfl
    intro k _
    rw [groupMeasure_residual]

end FiniteGroups

section NativeSupport

variable {A : Type*} [Fintype A]

abbrev SupportIndex (support : List Shape) := Fin support.length

def ownWeight (support : List Shape) (priority : Placement) (position : Fin 3)
    (hbound : ∀ i : SupportIndex support, support[i.val] (priority position) < 17)
    (i : SupportIndex support) : Fin 17 :=
  ⟨support[i.val] (priority position), hbound i⟩

def nativeGroup (support : List Shape) (priority : Placement) (position : Fin 3)
    (hbound : ∀ i : SupportIndex support, support[i.val] (priority position) < 17) :
    SupportIndex support → SupportIndex support ⊕ Fin 17 :=
  singletonResidualGroup
    (fun i => AllFieldNativeCapacity.designated priority position support[i.val])
    (ownWeight support priority position hbound)

theorem groupedEntropy_eq_native (support : List Shape) (p : Shape → ℝ)
    (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ)
    (hbound : ∀ i : SupportIndex support, support[i.val] (priority position) < 17)
    (hp : ∀ i : SupportIndex support, 0 ≤ p support[i.val])
    (hq : ∀ i : SupportIndex support, ∑ a, q support[i.val] a = 1) :
    JointCompatibilityIncidence.groupedEntropy
      (fun i : SupportIndex support => p support[i.val])
      (nativeGroup support priority position hbound)
      (fun i : SupportIndex support => q support[i.val]) =
      AllFieldNativeCapacity.groupedEntropy support p priority position q := by
  rw [nativeGroup, groupedEntropy_singletons_residuals _ _ _ _ hp hq]
  unfold AllFieldNativeCapacity.groupedEntropy AllFieldNativeCapacity.singletonEntropy
  congr 1
  · exact Fin.sum_univ_fun_getElem support fun u =>
      if AllFieldNativeCapacity.designated priority position u
      then p u * homogeneousEntropy (q u) else 0
  · apply Finset.sum_congr rfl
    intro k _
    congr 1
    funext a
    simp only [ownWeight, Fin.ext_iff]
    exact Fin.sum_univ_fun_getElem support fun u =>
      if ¬ AllFieldNativeCapacity.designated priority position u ∧
          u (priority position) = k.val then p u * q u a else 0

end NativeSupport

end MatrixMultiplication.JointNativeGroupedEntropy

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
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
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointGroupedEntropyEmbedding

open MatrixMultiplication.Foundation JointCompatibilityIncidence JointNativeGroupedEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {U V K L A : Type*}
  [Fintype U] [Fintype V] [Fintype K] [Fintype L] [Fintype A]

omit [Fintype K] [Fintype L] in
theorem groupMass_label_injective (j : K → L) (hj : Function.Injective j)
    (p : U → ℝ) (group : U → K) (k : K) :
    groupMass p (j ∘ group) (j k) = groupMass p group k := by
  simp only [groupMass, Function.comp_apply, hj.eq_iff]

omit [Fintype K] [Fintype L] [Fintype A] in
theorem groupLaw_label_injective (j : K → L) (hj : Function.Injective j)
    (p : U → ℝ) (group : U → K) (q : U → A → ℝ) (k : K) :
    groupLaw p (j ∘ group) q (j k) = groupLaw p group q k := by
  funext a
  simp only [groupLaw, groupMass_label_injective j hj,
    Function.comp_apply, hj.eq_iff]

omit [Fintype K] [Fintype L] in
theorem groupMass_label_not_mem_range (j : K → L) (p : U → ℝ)
    (group : U → K) (l : L) (hl : l ∉ Set.range j) :
    groupMass p (j ∘ group) l = 0 := by
  apply Finset.sum_eq_zero
  intro u _
  exact ite_eq_right (fun h => hl ⟨group u, h⟩)

theorem groupedEntropy_label_injective (j : K → L) (hj : Function.Injective j)
    (p : U → ℝ) (group : U → K) (q : U → A → ℝ) :
    groupedEntropy p (j ∘ group) q = groupedEntropy p group q := by
  unfold groupedEntropy
  symm
  apply Fintype.sum_of_injective j hj
  · intro l hl
    rw [groupMass_label_not_mem_range j p group l hl, zero_mul]
  · intro k
    rw [groupMass_label_injective j hj, groupLaw_label_injective j hj]

def pushforwardWeight (p : U → ℝ) (f : U → V) (v : V) : ℝ :=
  ∑ u, if f u = v then p u else 0

theorem sum_pushforwardWeight_mul (p : U → ℝ) (f : U → V) (test : V → ℝ) :
    (∑ v, pushforwardWeight p f v * test v) = ∑ u, p u * test (f u) := by
  simp only [pushforwardWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp only [ite_mul, zero_mul]
  simp

omit [Fintype K] in
theorem groupMass_pushforward (p : U → ℝ) (f : U → V)
    (group : V → K) (k : K) :
    groupMass (pushforwardWeight p f) group k = groupMass p (group ∘ f) k := by
  simpa only [groupMass, mul_ite, mul_one, mul_zero, Function.comp_apply] using
    (sum_pushforwardWeight_mul p f (fun v => if group v = k then 1 else 0))

omit [Fintype K] [Fintype A] in
theorem groupMeasure_pushforward (p : U → ℝ) (f : U → V)
    (group : V → K) (q : V → A → ℝ) (k : K) :
    groupMeasure (pushforwardWeight p f) group q k =
      groupMeasure p (group ∘ f) (q ∘ f) k := by
  funext a
  simpa only [groupMeasure, mul_ite, mul_zero, Function.comp_apply] using
    (sum_pushforwardWeight_mul p f (fun v => if group v = k then q v a else 0))

omit [Fintype K] [Fintype A] in
theorem groupLaw_pushforward (p : U → ℝ) (f : U → V)
    (group : V → K) (q : V → A → ℝ) (k : K) :
    groupLaw (pushforwardWeight p f) group q k =
      groupLaw p (group ∘ f) (q ∘ f) k := by
  funext a
  change groupMeasure (pushforwardWeight p f) group q k a /
      groupMass (pushforwardWeight p f) group k =
    groupMeasure p (group ∘ f) (q ∘ f) k a / groupMass p (group ∘ f) k
  rw [groupMeasure_pushforward, groupMass_pushforward]

theorem groupedEntropy_pushforward (p : U → ℝ) (f : U → V)
    (group : V → K) (q : V → A → ℝ) :
    groupedEntropy (pushforwardWeight p f) group q =
      groupedEntropy p (group ∘ f) (q ∘ f) := by
  simp only [groupedEntropy, groupMass_pushforward, groupLaw_pushforward]

theorem groupedEntropy_pushforward_of_agree (p : U → ℝ) (f : U → V)
    (group : V → K) (qU : U → A → ℝ) (qV : V → A → ℝ)
    (hq : ∀ u, qV (f u) = qU u) :
    groupedEntropy (pushforwardWeight p f) group qV =
      groupedEntropy p (group ∘ f) qU := by
  rw [groupedEntropy_pushforward]
  have he : qV ∘ f = qU := funext hq
  rw [he]

theorem groupedEntropy_pushforward_embedding (p : U → ℝ) (f : U → V)
    (groupU : U → K) (groupV : V → L) (j : K → L) (hj : Function.Injective j)
    (hgroup : ∀ u, groupV (f u) = j (groupU u))
    (qU : U → A → ℝ) (qV : V → A → ℝ) (hq : ∀ u, qV (f u) = qU u) :
    groupedEntropy (pushforwardWeight p f) groupV qV = groupedEntropy p groupU qU := by
  rw [groupedEntropy_pushforward_of_agree p f groupV qU qV hq]
  have hg : groupV ∘ f = j ∘ groupU := funext hgroup
  rw [hg, groupedEntropy_label_injective j hj]

theorem sum_map_mass_mul (p : FiniteLaw U) (f : U → V) (test : V → ℝ) :
    (∑ v, (p.map f).mass v * test v) = ∑ u, p.mass u * test (f u) := by
  simpa only [FiniteLaw.map_mass, pushforwardWeight] using
    (sum_pushforwardWeight_mul p.mass f test)

omit [Fintype K] in
theorem groupMass_map (p : FiniteLaw U) (f : U → V)
    (group : V → K) (k : K) :
    groupMass (p.map f).mass group k = groupMass p.mass (group ∘ f) k := by
  simpa only [groupMass, mul_ite, mul_one, mul_zero, Function.comp_apply] using
    (sum_map_mass_mul p f (fun v => if group v = k then 1 else 0))

omit [Fintype K] [Fintype A] in
theorem groupMeasure_map (p : FiniteLaw U) (f : U → V)
    (group : V → K) (q : V → A → ℝ) (k : K) :
    groupMeasure (p.map f).mass group q k =
      groupMeasure p.mass (group ∘ f) (q ∘ f) k := by
  funext a
  simpa only [groupMeasure, mul_ite, mul_zero, Function.comp_apply] using
    (sum_map_mass_mul p f (fun v => if group v = k then q v a else 0))

omit [Fintype K] [Fintype A] in
theorem groupLaw_map (p : FiniteLaw U) (f : U → V)
    (group : V → K) (q : V → A → ℝ) (k : K) :
    groupLaw (p.map f).mass group q k = groupLaw p.mass (group ∘ f) (q ∘ f) k := by
  funext a
  change groupMeasure (p.map f).mass group q k a / groupMass (p.map f).mass group k =
    groupMeasure p.mass (group ∘ f) (q ∘ f) k a / groupMass p.mass (group ∘ f) k
  rw [groupMeasure_map, groupMass_map]

theorem groupedEntropy_map (p : FiniteLaw U) (f : U → V)
    (group : V → K) (q : V → A → ℝ) :
    groupedEntropy (p.map f).mass group q =
      groupedEntropy p.mass (group ∘ f) (q ∘ f) := by
  simp only [groupedEntropy, groupMass_map, groupLaw_map]

theorem groupedEntropy_map_of_agree (p : FiniteLaw U) (f : U → V)
    (group : V → K) (qU : U → A → ℝ) (qV : V → A → ℝ)
    (hq : ∀ u, qV (f u) = qU u) :
    groupedEntropy (p.map f).mass group qV =
      groupedEntropy p.mass (group ∘ f) qU := by
  rw [groupedEntropy_map]
  have he : qV ∘ f = qU := funext hq
  rw [he]

theorem groupedEntropy_map_embedding (p : FiniteLaw U) (f : U → V)
    (groupU : U → K) (groupV : V → L) (j : K → L) (hj : Function.Injective j)
    (hgroup : ∀ u, groupV (f u) = j (groupU u))
    (qU : U → A → ℝ) (qV : V → A → ℝ) (hq : ∀ u, qV (f u) = qU u) :
    groupedEntropy (p.map f).mass groupV qV = groupedEntropy p.mass groupU qU := by
  rw [groupedEntropy_map_of_agree p f groupV qU qV hq]
  have hg : groupV ∘ f = j ∘ groupU := funext hgroup
  rw [hg, groupedEntropy_label_injective j hj]

end MatrixMultiplication.JointGroupedEntropyEmbedding

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
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
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldNativeGroupedRates

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open JointNativeGroupedEntropy JointGroupedEntropyPartition
open AllFieldNativeCapacity AllFieldPairConditionalEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

section Reindex

variable {U K A : Type*} [Fintype U] [Fintype K] [Fintype A]

omit [Fintype U] [Fintype K] in
theorem singletonResidualGroup_transport (e : U ≃ U) (c : K ≃ K)
    (d : U → Prop) (weight : U → K)
    (hw : ∀ u, c (weight u) = weight (e u)) :
    (Equiv.sumCongr e c) ∘ singletonResidualGroup (d ∘ e) weight =
      singletonResidualGroup d weight ∘ e := by
  funext u
  by_cases hu : d (e u) <;>
    simp [singletonResidualGroup, Function.comp_apply, hu, hw]

theorem singletonResidual_groupedEntropy_reindex (e : U ≃ U) (c : K ≃ K)
    (p : U → ℝ) (d : U → Prop) (weight : U → K) (q : U → A → ℝ)
    (hp : ∀ u, p (e u) = p u) (hw : ∀ u, c (weight u) = weight (e u)) :
    JointCompatibilityIncidence.groupedEntropy p
      (singletonResidualGroup (d ∘ e) weight) (q ∘ e) =
      JointCompatibilityIncidence.groupedEntropy p (singletonResidualGroup d weight) q := by
  calc
    _ = JointCompatibilityIncidence.groupedEntropy p
        ((Equiv.sumCongr e c) ∘ singletonResidualGroup (d ∘ e) weight) (q ∘ e) :=
      (JointCompatibilityIncidence.groupedEntropy_relabel (Equiv.sumCongr e c) p _ _).symm
    _ = JointCompatibilityIncidence.groupedEntropy p
        (singletonResidualGroup d weight ∘ e) (q ∘ e) := by
      rw [singletonResidualGroup_transport e c d weight hw]
    _ = _ := JointCompatibilityIncidence.groupedEntropy_reindex e p _ q hp

theorem right_conditional_sum_eq (e : U ≃ U) (c : K ≃ K)
    (p : FiniteLaw U) (d : U → Prop) (weight : U → K) (q : U → A → ℝ)
    (hp : ∀ u, p.mass (e u) = p.mass u)
    (hw : ∀ u, c (weight u) = weight (e u)) (hq : ∀ u, ∑ a, q u a = 1) :
    (∑ k, (p.map weight).mass k *
      JointCompatibilityIncidence.groupedEntropy (p.conditional weight k).mass
        (JointCompatibilityIncidence.designatedGroup (d ∘ e)) (q ∘ e)) =
      JointCompatibilityIncidence.groupedEntropy p.mass (singletonResidualGroup d weight) q := by
  rw [← groupedEntropy_conditional_partition p (d ∘ e) weight (q ∘ e)
    (fun u => hq (e u))]
  exact singletonResidual_groupedEntropy_reindex e c p.mass d weight q hp hw

end Reindex

def supportSubtypeEquiv {α : Type*} (xs : List α) (f : α → α)
    (hm : ∀ x ∈ xs, f x ∈ xs) (hi : ∀ x ∈ xs, f (f x) = x) :
    Equiv.Perm {x // x ∈ xs} where
  toFun x := ⟨f x.val, hm x.val x.property⟩
  invFun x := ⟨f x.val, hm x.val x.property⟩
  left_inv x := Subtype.ext (hi x.val x.property)
  right_inv x := Subtype.ext (hi x.val x.property)

def supportIndexEquiv {α : Type*} [DecidableEq α] (xs : List α) (hn : xs.Nodup)
    (f : α → α) (hm : ∀ x ∈ xs, f x ∈ xs) (hi : ∀ x ∈ xs, f (f x) = x) :
    Equiv.Perm (Fin xs.length) :=
  ((hn.getEquiv xs).trans (supportSubtypeEquiv xs f hm hi)).trans (hn.getEquiv xs).symm

theorem supportIndexEquiv_get {α : Type*} [DecidableEq α] (xs : List α)
    (hn : xs.Nodup) (f : α → α) (hm : ∀ x ∈ xs, f x ∈ xs)
    (hi : ∀ x ∈ xs, f (f x) = x) (i : Fin xs.length) :
    xs.get (supportIndexEquiv xs hn f hm hi i) = f (xs.get i) := by
  exact congrArg Subtype.val ((hn.getEquiv xs).apply_symm_apply
    ((supportSubtypeEquiv xs f hm hi) ((hn.getEquiv xs) i)))

def boundedComplement (s : ℕ) (hs : s < 17) (k : Fin 17) : Fin 17 :=
  ⟨if k.val ≤ s then s - k.val else k.val, by
    split_ifs
    · exact lt_of_le_of_lt (Nat.sub_le _ _) hs
    · exact k.isLt⟩

theorem boundedComplement_involutive (s : ℕ) (hs : s < 17) :
    Function.Involutive (boundedComplement s hs) := by
  intro k
  apply Fin.ext
  dsimp only [boundedComplement]
  split_ifs <;> omega

def boundedComplementEquiv (s : ℕ) (hs : s < 17) : Equiv.Perm (Fin 17) where
  toFun := boundedComplement s hs
  invFun := boundedComplement s hs
  left_inv := boundedComplement_involutive s hs
  right_inv := boundedComplement_involutive s hs

section NativeSupport

variable {A : Type*} [Fintype A]

theorem native_right_conditional_sum_eq (support : List Shape) (s : Shape)
    (p : Shape → ℝ) (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ)
    (hn : support.Nodup) (hm : ∀ u ∈ support, complement s u ∈ support)
    (hsupp : ∀ u ∈ support, ∀ side, u side ≤ s side)
    (hs : s (priority position) < 17)
    (hbound : ∀ i : SupportIndex support, support[i.val] (priority position) < 17)
    (law : FiniteLaw (SupportIndex support))
    (hlaw : ∀ i : SupportIndex support, law.mass i = p support[i.val])
    (hp : ∀ u ∈ support, p (complement s u) = p u)
    (hq : ∀ i : SupportIndex support, ∑ a, q support[i.val] a = 1) :
    (∑ k : Fin 17, (law.map (ownWeight support priority position hbound)).mass k *
      JointCompatibilityIncidence.groupedEntropy
        (law.conditional (ownWeight support priority position hbound) k).mass
        (JointCompatibilityIncidence.designatedGroup (fun i =>
          AllFieldNativeCapacity.designated priority position (complement s support[i.val])))
        (fun i => q (complement s support[i.val]))) =
      AllFieldNativeCapacity.groupedEntropy support p priority position q := by
  let hi : ∀ u ∈ support, complement s (complement s u) = u :=
    fun u hu => complement_involution_of_le s u (hsupp u hu)
  let e := supportIndexEquiv support hn (complement s) hm hi
  let c := boundedComplementEquiv (s (priority position)) hs
  let weight := ownWeight support priority position hbound
  let d : SupportIndex support → Prop :=
    fun i => AllFieldNativeCapacity.designated priority position support[i.val]
  let q₀ : SupportIndex support → A → ℝ := fun i => q support[i.val]
  have he (i : SupportIndex support) :
      support[(e i).val] = complement s support[i.val] := by
    simpa only [List.get_eq_getElem] using
      supportIndexEquiv_get support hn (complement s) hm hi i
  have hmass (i : SupportIndex support) : law.mass (e i) = law.mass i := by
    simp only [hlaw, he]
    exact hp _ (List.getElem_mem i.isLt)
  have hw (i : SupportIndex support) : c (weight i) = weight (e i) := by
    apply Fin.ext
    change (if support[i.val] (priority position) ≤ s (priority position)
      then s (priority position) - support[i.val] (priority position)
      else support[i.val] (priority position)) = support[(e i).val] (priority position)
    rw [ite_eq_left (hsupp _ (List.getElem_mem i.isLt) _), he]
    rfl
  have hright := right_conditional_sum_eq e c law d weight q₀ hmass hw hq
  have hd : d ∘ e = fun i =>
      AllFieldNativeCapacity.designated priority position (complement s support[i.val]) := by
    funext i
    dsimp only [d, Function.comp_apply]
    rw [he]
  have hqr : q₀ ∘ e = fun i => q (complement s support[i.val]) := by
    funext i
    dsimp only [q₀, Function.comp_apply]
    rw [he]
  rw [hd, hqr] at hright
  have hnonneg (i : SupportIndex support) : 0 ≤ p support[i.val] := by
    rw [← hlaw i]
    exact law.nonneg i
  have hmassfun : law.mass = fun i : SupportIndex support => p support[i.val] := funext hlaw
  calc
    _ = JointCompatibilityIncidence.groupedEntropy law.mass
        (nativeGroup support priority position hbound) (fun i => q support[i.val]) := by
      simpa only [d, q₀, weight, nativeGroup] using hright
    _ = _ := by
      rw [hmassfun]
      exact groupedEntropy_eq_native support p priority position q hbound hnonneg hq

theorem native_two_conditional_sums_eq (support : List Shape) (s : Shape)
    (p : Shape → ℝ) (priority : Placement) (position : Fin 3) (q : Shape → A → ℝ)
    (hn : support.Nodup) (hm : ∀ u ∈ support, complement s u ∈ support)
    (hsupp : ∀ u ∈ support, ∀ side, u side ≤ s side)
    (hs : s (priority position) < 17)
    (hbound : ∀ i : SupportIndex support, support[i.val] (priority position) < 17)
    (law : FiniteLaw (SupportIndex support))
    (hlaw : ∀ i : SupportIndex support, law.mass i = p support[i.val])
    (hp : ∀ u ∈ support, p (complement s u) = p u)
    (hq : ∀ i : SupportIndex support, ∑ a, q support[i.val] a = 1) :
    (∑ k : Fin 17, (law.map (ownWeight support priority position hbound)).mass k *
      (JointCompatibilityIncidence.groupedEntropy
        (law.conditional (ownWeight support priority position hbound) k).mass
        (JointCompatibilityIncidence.designatedGroup (fun i =>
          AllFieldNativeCapacity.designated priority position support[i.val]))
        (fun i => q support[i.val]) +
      JointCompatibilityIncidence.groupedEntropy
        (law.conditional (ownWeight support priority position hbound) k).mass
        (JointCompatibilityIncidence.designatedGroup (fun i =>
          AllFieldNativeCapacity.designated priority position (complement s support[i.val])))
        (fun i => q (complement s support[i.val])))) =
      2 * AllFieldNativeCapacity.groupedEntropy support p priority position q := by
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← native_groupedEntropy_eq_sum_conditional support p priority position q hbound law hlaw hq,
    native_right_conditional_sum_eq support s p priority position q hn hm hsupp hs
      hbound law hlaw hp hq]
  ring

end NativeSupport

def twoHalfConditionalCost {A : Type*} [Fintype A]
    (support : List Shape) (s : Shape) (priority : Placement) (position : Fin 3)
    (q : Shape → A → ℝ) (law : FiniteLaw (SupportIndex support))
    (weight : SupportIndex support → Fin 17) : ℝ :=
  ∑ k : Fin 17, (law.map weight).mass k *
    (JointCompatibilityIncidence.groupedEntropy (law.conditional weight k).mass
      (JointCompatibilityIncidence.designatedGroup (fun i =>
        AllFieldNativeCapacity.designated priority position support[i.val]))
      (fun i => q support[i.val]) +
    JointCompatibilityIncidence.groupedEntropy (law.conditional weight k).mass
      (JointCompatibilityIncidence.designatedGroup (fun i =>
        AllFieldNativeCapacity.designated priority position (complement s support[i.val])))
      (fun i => q (complement s support[i.val])))

theorem stageA_twoHalfConditionalCost_eq (g : Shape) (hg : g ∈ positiveInitial)
    (priority : Placement) (position : Fin 3) :
    twoHalfConditionalCost (below g) g priority position
      (fun u a => (halfLaw u (priority position) a : ℝ)) (stageASplitLaw g hg)
      (stageASplitWeight g hg (priority position)) =
      2 * AllFieldNativeCapacity.groupedEntropy (below g)
        (fun u => (stageALaw g u : ℝ)) priority position
        (fun u a => (halfLaw u (priority position) a : ℝ)) := by
  have hs : g (priority position) < 17 :=
    Nat.lt_succ_of_le ((positiveInitial_shape_spec g hg).1 (priority position))
  let hb : ∀ i : SupportIndex (below g), (below g)[i.val] (priority position) < 17 :=
    fun i => lt_of_le_of_lt (below_le (List.getElem_mem i.isLt) _) hs
  have hq (i : SupportIndex (below g)) :
      ∑ a, (halfLaw (below g)[i.val] (priority position) a : ℝ) = 1 :=
    (halfFiniteLaw _ (stageA_children_size g hg _ (List.getElem_mem i.isLt))
      (priority position)).total
  have hh := native_two_conditional_sums_eq (below g) g
    (fun u => (stageALaw g u : ℝ)) priority position
    (fun u a => (halfLaw u (priority position) a : ℝ))
    (stageA_below_nodup g hg) (fun u hu => (stageA_support_complement g hg u hu).1)
    (fun _ hu => below_le hu) hs hb (stageASplitLaw g hg) (fun _ => rfl)
    (fun u hu => by rw [stageALaw_complement g u hg hu]) hq
  exact hh

theorem stageB_twoHalfConditionalCost_eq (t : Shape) (ht : t ∈ positiveSecond)
    (priority : Placement) (position : Fin 3) :
    twoHalfConditionalCost (below t) t priority position
      (fun u a => (littleLaw t u (priority position) a : ℝ)) (stageBSplitLaw t ht)
      (stageBSplitWeight t ht (priority position)) =
      2 * AllFieldNativeCapacity.groupedEntropy (below t)
        (fun u => (stageBLaw t u : ℝ)) priority position
        (fun u a => (littleLaw t u (priority position) a : ℝ)) := by
  have hs : t (priority position) < 17 :=
    Nat.lt_succ_of_le ((positiveSecond_shape_spec t ht).1 (priority position))
  let hb : ∀ i : SupportIndex (below t), (below t)[i.val] (priority position) < 17 :=
    fun i => lt_of_le_of_lt (below_le (List.getElem_mem i.isLt) _) hs
  have hq (i : SupportIndex (below t)) :
      ∑ a, (littleLaw t (below t)[i.val] (priority position) a : ℝ) = 1 :=
    (littleFiniteLaw t _ (priority position)).total
  have hh := native_two_conditional_sums_eq (below t) t
    (fun u => (stageBLaw t u : ℝ)) priority position
    (fun u a => (littleLaw t u (priority position) a : ℝ))
    (stageB_below_nodup t ht) (fun u hu => (stageB_support_complement t ht u hu).1)
    (fun _ hu => below_le hu) hs hb (stageBSplitLaw t ht) (fun _ => rfl)
    (fun u hu => by rw [stageBLaw_complement t u ht hu]) hq
  exact hh

theorem stageA_twoHalfConditionalCost_eq_entropy_sub_capacity
    (g : Shape) (hg : g ∈ positiveInitial) (side : Fin 3) (hside : side ≠ 0) :
    twoHalfConditionalCost (below g) g (Equiv.refl (Fin 3)) side
      (fun u a => (halfLaw u side a : ℝ)) (stageASplitLaw g hg)
      (stageASplitWeight g hg side) =
      finiteEntropy (stageAPairLaw g hg side).mass - stageACapacity g side := by
  rw [stageACapacity_sharing g hg side hside]
  have hh := stageA_twoHalfConditionalCost_eq g hg (Equiv.refl (Fin 3)) side
  simpa only [Equiv.refl_apply, sub_sub_cancel] using hh

theorem stageB_twoHalfConditionalCost_eq_entropy_sub_capacity
    (t : Shape) (ht : t ∈ positiveSecond) (side : Fin 3) (hside : side ≠ 0) :
    twoHalfConditionalCost (below t) t (stageBPriority t) side
      (fun u a => (littleLaw t u (stageBPriority t side) a : ℝ)) (stageBSplitLaw t ht)
      (stageBSplitWeight t ht (stageBPriority t side)) =
      finiteEntropy (stageBPairLaw t ht (stageBPriority t side)).mass -
        stageBCapacity t side := by
  rw [stageBCapacity_sharing t ht side hside]
  have hh := stageB_twoHalfConditionalCost_eq t ht (stageBPriority t) side
  simpa only [sub_sub_cancel] using hh

end MatrixMultiplication.AllFieldNativeGroupedRates

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupProjectedEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws
open AllFieldHistoryChildLaws AllFieldGroupOrbitData AllFieldGroupDegrees
open AllFieldGroupNativeLaws AllFieldGroupPairWindows AllFieldGroupDegreeLaws
open JointCompatibilityScaling JointCompatibilityRateLimit JointCompatibilityControls
open JointCompatibilityIncidence JointGroupedEntropyEmbedding JointGroupedEntropyPartition
open AllFieldGroupBranchDesignation AllFieldGroupBranchLaws AllFieldNativeGroupedRates
open AllFieldScheduledYield AllFieldGroupPairEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

section Kernel

variable {U V G A : Type*} [Fintype U] [Fintype V] [Fintype G] [Fintype A]

theorem groupedEntropy_congr_law_on_support (p : U → ℝ) (group : U → G)
    (q q' : U → A → ℝ) (hq : ∀ u, p u ≠ 0 → q u = q' u) :
    groupedEntropy p group q = groupedEntropy p group q' := by
  have he (g : G) : groupLaw p group q g = groupLaw p group q' g := by
    funext a
    unfold groupLaw
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    by_cases hp : p u = 0
    · simp only [hp, zero_mul]
    · rw [hq u hp]
  simp only [groupedEntropy, he]

theorem groupedEntropy_designated_pushforward (p : U → ℝ) (f : U → V)
    (hf : Function.Injective f) (d : V → Prop) (d' : U → Prop)
    (hd : ∀ u, d (f u) ↔ d' u) (q : V → A → ℝ) (q' : U → A → ℝ)
    (hq : ∀ u, p u ≠ 0 → q (f u) = q' u) :
    groupedEntropy (pushforwardWeight p f) (designatedGroup d) q =
      groupedEntropy p (designatedGroup d') q' := by
  rw [groupedEntropy_pushforward]
  have hg : designatedGroup d ∘ f = Option.map f ∘ designatedGroup d' := by
    funext u
    by_cases hu : d' u
    · simp [designatedGroup, (hd u).mpr hu, hu]
    · simp [designatedGroup, mt (hd u).mp hu, hu]
  rw [hg, groupedEntropy_label_injective (Option.map f) (Option.map_injective hf)]
  exact groupedEntropy_congr_law_on_support p _ _ q' hq

theorem groupedEntropy_const_one (p : U → ℝ) (group : U → G) :
    groupedEntropy p group (fun _ (_ : A) => 1) = 0 := by
  unfold groupedEntropy
  apply Finset.sum_eq_zero
  intro g _
  by_cases hg : groupMass p group g = 0
  · rw [hg, zero_mul]
  · have he : groupLaw p group (fun _ (_ : A) => 1) g = fun _ => 1 := by
      funext a
      simp only [groupLaw, mul_one]
      exact div_self hg
    rw [he]
    simp [finiteEntropy, entropyTerm]

omit [Fintype V] [Fintype G] in
theorem pushforwardWeight_mask (p : U → ℝ) (f : U → V)
    (weight : V → G) (k : G) :
    (fun v => if weight v = k then pushforwardWeight p f v else 0) =
      pushforwardWeight (fun u => if weight (f u) = k then p u else 0) f := by
  funext v
  unfold pushforwardWeight
  by_cases hv : weight v = k
  · simp only [hv, ite_true]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : f u = v <;> simp [hu, hv]
  · simp only [hv, ite_false]
    symm
    apply Finset.sum_eq_zero
    intro u _
    by_cases hu : f u = v <;> simp [hu, hv]

end Kernel

variable {K tick : ℕ} {sigma : Placement}

def maskedBranchMass (h : ActiveOrder K tick sigma) (side : Fin 3) (k : Fin 17)
    (b : h.val.val.1.Branch) : ℝ :=
  if nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side) b = k
  then (branchLaw h.val.val.1).mass b else 0

theorem classCounts_cast_eq_pushforward (allocation : Allocation) (side : Fin 3)
    (h : ActiveOrder K tick sigma) (k : Fin 17) :
    (fun u => (base allocation sigma side (h, k) u : ℝ)) =
      fun u => (parentBase allocation h : ℝ) *
        pushforwardWeight (maskedBranchMass h side k) (branchShape h.val.val) u := by
  have hpmap : (placedLaw h.val.val).mass =
      pushforwardWeight (branchLaw h.val.val.1).mass (branchShape h.val.val) := by
    funext u
    simp only [placedLaw, FiniteLaw.map_mass, pushforwardWeight]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : branchShape h.val.val b = u <;> simp only [hb, ite_true, ite_false]
  have hm : (fun u => if JointPopulation.shapeSide (sigma side) u = k
      then (placedLaw h.val.val).mass u else 0) =
      pushforwardWeight (maskedBranchMass h side k) (branchShape h.val.val) := by
    rw [hpmap]
    funext u
    unfold pushforwardWeight maskedBranchMass
    by_cases hu : JointPopulation.shapeSide (sigma side) u = k
    · simp only [hu, ite_true]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : branchShape h.val.val b = u
      · have hk : nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side) b = k := by
          rw [← order_branch_weight h side b, hb]
          exact hu
        simp only [hb, hk, ite_true]
      · simp only [hb, ite_false]
    · simp only [hu, ite_false]
      symm
      apply Finset.sum_eq_zero
      intro b _
      by_cases hb : branchShape h.val.val b = u
      · have hk : nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side) b ≠ k := by
          rw [← order_branch_weight h side b, hb]
          exact hu
        simp only [hb, hk, ite_true, ite_false]
      · simp only [hb, ite_false]
  funext u
  change ((if JointPopulation.shapeSide (sigma side) u = k
    then Counts allocation 1 sigma h u else 0 : ℕ) : ℝ) = _
  rw [Nat.cast_ite, Nat.cast_zero]
  rw [← hm]
  by_cases hu : JointPopulation.shapeSide (sigma side) u = k
  · simp only [hu, ite_true]
    exact jointCounts_cast allocation 1 h.val.val u
  · simp only [hu, ite_false, mul_zero]

def branchHalfLaw (w : Work K) (right : Bool) (side : Fin 3)
    (b : w.Branch) (a : w.Statistic) : ℝ :=
  (w.childLaw (halfShape w.parentShape (w.splitShape b) right) (w.priority side) a : ℝ)

theorem class_groupedEntropy_eq_masked (allocation : Allocation) (right : Bool)
    (side : Fin 3) (hside : side ≠ 0) (h : ActiveOrder K tick sigma) (k : Fin 17) :
    groupedEntropy (fun u => (base allocation sigma side (h, k) u : ℝ))
      (designatedGroup (classDesignated right side sigma (h, k)))
      (nativeLaw allocation right side sigma (h, k)) =
      (parentBase allocation h : ℝ) *
        groupedEntropy (maskedBranchMass h side k)
          (designatedGroup (nativeBranchDesignated h.val.val.1 right side))
          (branchHalfLaw h.val.val.1 right side) := by
  rw [classCounts_cast_eq_pushforward, groupedEntropy_mul]
  congr 1
  apply groupedEntropy_designated_pushforward _ _ (branchShape_injective h.val.val)
    _ _ (fun b => designated_branchShape right side h hside b)
  intro b hb
  have hp : (branchLaw h.val.val.1).mass b ≠ 0 := by
    intro hp
    apply hb
    simp only [maskedBranchMass, hp, ite_self]
  exact supportedHalfLaw_branchShape_of_mass_ne_zero allocation right h b hp side

theorem maskedBranchMass_eq_conditional (h : ActiveOrder K tick sigma)
    (side : Fin 3) (k : Fin 17) :
    maskedBranchMass h side k = fun b =>
      ((branchLaw h.val.val.1).map
        (nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side))).mass k *
      ((branchLaw h.val.val.1).conditional
        (nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side)) k).mass b := by
  funext b
  exact ((branchLaw h.val.val.1).map_mass_mul_conditional
    (nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side)) k b).symm

def branchConditionalCost (w : Work K) (side : Fin 3) : ℝ :=
  ∑ k : Fin 17,
    ((branchLaw w).map (nativeSplitWeightCode w (w.priority side))).mass k *
      (groupedEntropy ((branchLaw w).conditional
          (nativeSplitWeightCode w (w.priority side)) k).mass
        (designatedGroup (nativeBranchDesignated w false side)) (branchHalfLaw w false side) +
      groupedEntropy ((branchLaw w).conditional
          (nativeSplitWeightCode w (w.priority side)) k).mass
        (designatedGroup (nativeBranchDesignated w true side)) (branchHalfLaw w true side))

theorem history_projected_entropy_eq (allocation : Allocation)
    (side : Fin 3) (hside : side ≠ 0) (h : ActiveOrder K tick sigma) :
    (∑ k : Fin 17,
      (groupedEntropy (fun u => (base allocation sigma side (h, k) u : ℝ))
        (designatedGroup (classDesignated false side sigma (h, k)))
        (nativeLaw allocation false side sigma (h, k)) +
      groupedEntropy (fun u => (base allocation sigma side (h, k) u : ℝ))
        (designatedGroup (classDesignated true side sigma (h, k)))
        (nativeLaw allocation true side sigma (h, k)))) =
      (parentBase allocation h : ℝ) * branchConditionalCost h.val.val.1 side := by
  simp_rw [class_groupedEntropy_eq_masked allocation _ side hside,
    maskedBranchMass_eq_conditional, groupedEntropy_mul]
  simp only [branchConditionalCost, Finset.mul_sum, mul_add]

theorem branchConditionalCost_eq (w : Work K) (side : Fin 3) (hside : side ≠ 0) :
    branchConditionalCost w side =
      if w.stage ≠ 2 then
        finiteEntropy (nativePairLaw w (w.priority side)).mass - workCapacity w side
      else 0 := by
  cases w with
  | stageA h =>
      have hs : (Work.stageA h).stage ≠ 2 := by change (0 : Fin 3) ≠ 2; decide
      have hl : branchLaw (Work.stageA h) =
          AllFieldNativeCapacity.stageASplitLaw (initialShape h.val) h.property := rfl
      have hw : nativeSplitWeightCode (Work.stageA h) ((Work.stageA h).priority side) =
          AllFieldPairConditionalEntropy.stageASplitWeight (initialShape h.val) h.property side := by
        funext b
        apply Fin.ext
        rfl
      have hd (right : Bool) : nativeBranchDesignated (Work.stageA h) right side =
          fun b => AllFieldNativeCapacity.designated (Equiv.refl (Fin 3)) side
            (halfShape (initialShape h.val) (below (initialShape h.val))[b.val] right) := by
        funext b
        apply propext
        change (_ ∧ _) ↔ _
        exact ⟨fun hh => hh.2, fun hh => ⟨hs, hh⟩⟩
      have hq (right : Bool) : branchHalfLaw (Work.stageA h) right side =
          fun b a => (halfLaw
            (halfShape (initialShape h.val) (below (initialShape h.val))[b.val] right)
            side a : ℝ) := rfl
      rw [ite_eq_left hs]
      rw [branchConditionalCost, hl, hw]
      simp_rw [hd, hq]
      exact stageA_twoHalfConditionalCost_eq_entropy_sub_capacity _ h.property side hside
  | stageB h =>
      have hs : (Work.stageB h).stage ≠ 2 := by change (1 : Fin 3) ≠ 2; decide
      have hl : branchLaw (Work.stageB h) =
          AllFieldNativeCapacity.stageBSplitLaw (aShape h.val) h.property := rfl
      have hw : nativeSplitWeightCode (Work.stageB h) ((Work.stageB h).priority side) =
          AllFieldPairConditionalEntropy.stageBSplitWeight (aShape h.val) h.property
            (stageBPriority (aShape h.val) side) := by
        funext b
        apply Fin.ext
        rfl
      have hd (right : Bool) : nativeBranchDesignated (Work.stageB h) right side =
          fun b => AllFieldNativeCapacity.designated (stageBPriority (aShape h.val)) side
            (halfShape (aShape h.val) (below (aShape h.val))[b.val] right) := by
        funext b
        apply propext
        change (_ ∧ _) ↔ _
        exact ⟨fun hh => hh.2, fun hh => ⟨hs, hh⟩⟩
      have hq (right : Bool) : branchHalfLaw (Work.stageB h) right side =
          fun b a => (littleLaw (aShape h.val)
            (halfShape (aShape h.val) (below (aShape h.val))[b.val] right)
            (stageBPriority (aShape h.val) side) a : ℝ) := rfl
      rw [ite_eq_left hs]
      rw [branchConditionalCost, hl, hw]
      simp_rw [hd, hq]
      exact stageB_twoHalfConditionalCost_eq_entropy_sub_capacity _ h.property side hside
  | stageC h =>
      rw [ite_eq_right (show ¬ (Work.stageC h).stage ≠ 2 by simp [Work.stage])]
      unfold branchConditionalCost
      have hq (right : Bool) : branchHalfLaw (Work.stageC h) right side =
          fun _ _ => 1 := by
        funext b a
        simp only [branchHalfLaw, Work.childLaw, Rat.cast_one]
      simp only [hq, groupedEntropy_const_one, zero_add, mul_zero, Finset.sum_const_zero]

theorem branchConditionalCost_eq_observed (h : ActiveOrder K tick sigma)
    (side : Fin 3) (hside : side ≠ 0) :
    branchConditionalCost h.val.val.1 side =
      observedEntropy h side - workCapacity h.val.val.1 side := by
  rw [branchConditionalCost_eq _ side hside]
  unfold observedEntropy
  by_cases hs : h.val.val.1.stage ≠ 2
  · rw [ite_eq_left hs, ite_eq_left hs]
  · rw [ite_eq_right hs, ite_eq_right hs]
    have hc : workCapacity h.val.val.1 side = finiteEntropy
        (JointPopulationRates.sideMass (orderLaw h).mass (sigma side)) := by
      rcases h with ⟨⟨⟨w, phi⟩, ht⟩, ho⟩
      cases w with
      | stageA a => exact False.elim (hs (by change (0 : Fin 3) ≠ 2; decide))
      | stageB a => exact False.elim (hs (by change (1 : Fin 3) ≠ 2; decide))
      | stageC a =>
          have hh := AllFieldActiveCapacity.workCapacity_stageC_physical a phi side
          simpa only [ho, orderLaw] using hh
    rw [hc, sub_self]

theorem projected_native_entropy_eq (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (hside : side ≠ 0) :
    projectedReferenceEntropy (base (K := K) (tick := tick) allocation sigma side)
        (classDesignated false side sigma)
        (groupCap (base allocation sigma side) (classDesignated false side sigma)
          (nativeLaw allocation false side sigma) 0) +
      projectedReferenceEntropy (base (K := K) (tick := tick) allocation sigma side)
        (classDesignated true side sigma)
        (groupCap (base allocation sigma side) (classDesignated true side sigma)
          (nativeLaw allocation true side sigma) 0) =
      ∑ h : ActiveOrder K tick sigma, (parentBase allocation h : ℝ) *
        (observedEntropy h side - workCapacity h.val.val.1 side) := by
  rw [JointProjectedGroupEntropy.projectedReferenceEntropy_eq_sum_counts_groupedEntropy,
    JointProjectedGroupEntropy.projectedReferenceEntropy_eq_sum_counts_groupedEntropy,
    ← Finset.sum_add_distrib, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  rw [history_projected_entropy_eq allocation side hside,
    branchConditionalCost_eq_observed h side hside]

end MatrixMultiplication.AllFieldGroupProjectedEntropy

end
end

end MatrixAllFields

end OAI
