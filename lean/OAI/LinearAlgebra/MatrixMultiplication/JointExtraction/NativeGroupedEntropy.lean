import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.NativeCapacity
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CompatibilityIncidence
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

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

end OAI
