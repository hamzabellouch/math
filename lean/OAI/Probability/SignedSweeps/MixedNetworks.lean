import OAI.Probability.SignedSweeps.MaskedKernels
import OAI.Probability.SignedSweeps.PermutationRows

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma sampleSweep_uniform (d : ℕ) (x y : Fin (2 ^ d)) :
    finiteProb (fun p : PhysicalSettings d => sampleSweep d (physicalSettingsEquiv d p) x = y) =
      ((2 ^ d : ℕ) : ℝ)⁻¹ := by
  have h := sweepEndpointProb_insert_isolated (I := Unit) d ∅ (fun _ => x) (fun _ => y)
    () (by simp)
  have hz : sweepEndpointProb d (∅ : Finset Unit) (fun _ => x) (fun _ => y) = 1 := by
    simp [sweepEndpointProb]
  rw [hz, mul_one] at h
  convert h using 1
  unfold sweepEndpointProb
  apply finiteProb_congr
  intro p
  simp

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev SubsetNetwork (A : Finset I) := Option {a : I // a ∉ A}

def labelNetwork (A : Finset I) (i : I) : SubsetNetwork A :=
  if h : i ∈ A then none else some ⟨i,h⟩

omit [Fintype I] in
@[simp] lemma labelNetwork_of_mem (A : Finset I) {i : I} (hi : i ∈ A) : labelNetwork A i = none := by
  simp only [labelNetwork, dite_eq_left hi]

omit [Fintype I] in
@[simp] lemma labelNetwork_of_notMem (A : Finset I) {i : I} (hi : i ∉ A) :
    labelNetwork A i = some ⟨i,hi⟩ := by simp only [labelNetwork, dite_eq_right hi]

def mixedNetworkPermutation (d : ℕ) (A : Finset I)
    (p : SubsetNetwork A → PhysicalSettings d) : Equiv.Perm (I → Fin (2 ^ d)) :=
  Equiv.piCongrRight (fun i => sampleSweep d (physicalSettingsEquiv d (p (labelNetwork A i))))

omit [Fintype I] in
@[simp] lemma mixedNetworkPermutation_apply (d : ℕ) (A : Finset I)
    (p : SubsetNetwork A → PhysicalSettings d) (x : I → Fin (2 ^ d)) (i : I) :
    mixedNetworkPermutation d A p x i =
      sampleSweep d (physicalSettingsEquiv d (p (labelNetwork A i))) (x i) := rfl

omit [Fintype I] in
@[simp] lemma mixedNetworkPermutation_symm_apply (d : ℕ) (A : Finset I)
    (p : SubsetNetwork A → PhysicalSettings d) (x : I → Fin (2 ^ d)) (i : I) :
    (mixedNetworkPermutation d A p).symm x i =
      (sampleSweep d (physicalSettingsEquiv d (p (labelNetwork A i)))).symm (x i) := rfl

theorem subsetEndpointKernel_eq_mixedProb (d : ℕ) (A : Finset I)
    (x y : InjectiveTuple I (2 ^ d)) :
    subsetEndpointKernel d A x y = finiteProb (fun p : SubsetNetwork A → PhysicalSettings d =>
      mixedNetworkPermutation d A p x = y) := by
  let P : SubsetNetwork A → PhysicalSettings d → Prop := fun j p => match j with
    | none => ∀ i ∈ A, sampleSweep d (physicalSettingsEquiv d p) (x i) = y i
    | some i => sampleSweep d (physicalSettingsEquiv d p) (x i.1) = y i.1
  have he : finiteProb (fun p : SubsetNetwork A → PhysicalSettings d =>
      mixedNetworkPermutation d A p x = y) = ∏ j : SubsetNetwork A, finiteProb (P j) := by
    calc
      _ = finiteProb (fun p : SubsetNetwork A → PhysicalSettings d => ∀ j, P j (p j)) := by
        apply finiteProb_congr
        intro p
        constructor
        · intro h j
          have h' := congrFun h
          cases j with
          | none =>
            intro i hi
            simpa only [mixedNetworkPermutation_apply, labelNetwork_of_mem A hi] using h' i
          | some a =>
            change sampleSweep d (physicalSettingsEquiv d (p (some a))) (x a.1) = y a.1
            simpa only [mixedNetworkPermutation_apply, labelNetwork_of_notMem A a.2] using h' a.1
        · intro h
          funext i
          by_cases hi : i ∈ A
          · simpa only [mixedNetworkPermutation_apply, labelNetwork_of_mem A hi] using h none i hi
          · simpa only [mixedNetworkPermutation_apply, labelNetwork_of_notMem A hi] using h (some ⟨i,hi⟩)
      _ = _ := finiteProb_pi_forall (fun _ => PhysicalSettings d) P
  rw [he, Fintype.prod_option]
  change _ = sweepEndpointProb d A x y * ∏ i : {a : I // a ∉ A},
    finiteProb (fun p : PhysicalSettings d => sampleSweep d (physicalSettingsEquiv d p) (x i.1) = y i.1)
  simp only [sampleSweep_uniform, Finset.prod_const, Finset.card_univ]
  have hc : Fintype.card {a : I // a ∉ A} = Fintype.card I - A.card := by
    simpa only [Fintype.card_coe] using Fintype.card_subtype_compl (fun a => a ∈ A)
  rw [hc]
  unfold subsetEndpointKernel normalizedEndpointProb
  have hn : (((2 ^ d : ℕ) : ℝ)) ≠ 0 := by positivity
  have hp : (((2 ^ d : ℕ) : ℝ)) ^ Fintype.card I =
      (((2 ^ d : ℕ) : ℝ)) ^ A.card * (((2 ^ d : ℕ) : ℝ)) ^ (Fintype.card I - A.card) := by
    rw [← pow_add, Nat.add_sub_of_le (Finset.card_le_univ A)]
  rw [hp, inv_pow]
  field_simp

lemma maskedEndpointKernel_eq_mixed (d : ℕ) (A : Finset I) (x y : InjectiveTuple I (2 ^ d)) :
    maskedEndpointKernel d A x y =
      maskedPermutationKernel (mixedNetworkPermutation d A)
        (fun x y => NoIsolatedVertex (endpointEncounter d x y) Finset.univ) x y := by
  unfold maskedEndpointKernel maskedPermutationKernel
  rw [subsetEndpointKernel_eq_mixedProb]

def networkInitialSubsets {n : ℕ} (A : Finset I) (x : InjectiveTuple I n) : SubsetNetwork A → Finset (Fin n)
  | none => A.image x
  | some i => {x i.1}

lemma networkInitialSubsets_total {n : ℕ} (A : Finset I) (x : InjectiveTuple I n) :
    (∑ j : SubsetNetwork A, (networkInitialSubsets A x j).card) = Fintype.card I := by
  rw [Fintype.sum_option]
  change (A.image x).card + (∑ _ : {a : I // a ∉ A}, ({x _} : Finset (Fin n)).card) = _
  simp only [Finset.card_image_of_injective A x.injective, Finset.card_singleton,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  have hc : Fintype.card {a : I // a ∉ A} = Fintype.card I - A.card := by
    simpa only [Fintype.card_coe] using Fintype.card_subtype_compl (fun a => a ∈ A)
  rw [hc]
  exact Nat.add_sub_of_le (Finset.card_le_univ A)

end SignedSweeps
end

end OAI
