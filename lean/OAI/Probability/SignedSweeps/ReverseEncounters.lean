import OAI.Probability.SignedSweeps.NetworkSampling

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
lemma labelNetwork_eq_none_iff (A : Finset I) (i : I) : labelNetwork A i = none ↔ i ∈ A := by
  unfold labelNetwork
  split_ifs with hi <;> simp [hi]

omit [Fintype I] in
lemma labelNetwork_eq_some_iff (A : Finset I) (i : I) (b : {a : I // a ∉ A}) :
    labelNetwork A i = some b ↔ i = b.1 := by
  constructor
  · intro h
    unfold labelNetwork at h
    split_ifs at h with hi
    exact congrArg Subtype.val (Option.some.inj h)
  · intro h
    subst i
    exact labelNetwork_of_notMem A b.2

omit [Fintype I] in
lemma mem_networkInitialSubsets {n : ℕ} (A : Finset I) (x : InjectiveTuple I n)
    (j : SubsetNetwork A) (t : Fin n) :
    t ∈ networkInitialSubsets A x j ↔ ∃ i, labelNetwork A i = j ∧ x i = t := by
  cases j with
  | none =>
    simp only [networkInitialSubsets, Finset.mem_image, labelNetwork_eq_none_iff]
  | some b =>
    simp only [networkInitialSubsets, Finset.mem_singleton, labelNetwork_eq_some_iff,
      exists_eq_left, eq_comm]

def labelLocation {n : ℕ} (A : Finset I) (y : I → Fin n) (i : I) : SubsetNetwork A × Fin n :=
  (labelNetwork A i, y i)

def labelOccupancy {n : ℕ} (A : Finset I) (y : I → Fin n) : Finset (SubsetNetwork A × Fin n) :=
  Finset.univ.image (labelLocation A y)

omit [Fintype I] in
lemma labelLocation_injective_sampled {d : ℕ} (A : Finset I) (x : InjectiveTuple I (2 ^ d))
    (p : SubsetNetwork A → PhysicalSettings d) :
    Function.Injective (labelLocation A (mixedNetworkPermutation d A p x)) := by
  intro i j h
  have hj : labelNetwork A i = labelNetwork A j := congrArg Prod.fst h
  have hs : sampleSweep d (physicalSettingsEquiv d (p (labelNetwork A i))) (x i) =
      sampleSweep d (physicalSettingsEquiv d (p (labelNetwork A j))) (x j) := congrArg Prod.snd h
  rw [hj] at hs
  exact x.injective ((sampleSweep d _).injective hs)

lemma labelOccupancy_eq_sampleSubset {d : ℕ} (A : Finset I) (x : InjectiveTuple I (2 ^ d))
    (p : SubsetNetwork A → PhysicalSettings d) :
    labelOccupancy A (mixedNetworkPermutation d A p x) =
      independentSampleSubset (networkInitialSubsets A x) p := by
  apply subsetFiberEquiv.injective
  funext j
  apply Finset.ext
  intro t
  rw [show subsetFiberEquiv (independentSampleSubset (networkInitialSubsets A x) p) j =
      _ from fiber_independentSampleSubset _ p j]
  change t ∈ subsetFiber (labelOccupancy A (mixedNetworkPermutation d A p x)) j ↔ _
  rw [mem_subsetFiber]
  simp only [labelOccupancy, Finset.mem_image, Finset.mem_univ, true_and,
    labelLocation, Prod.mk.injEq, mixedNetworkPermutation_apply]
  constructor
  · rintro ⟨i,hi,ht⟩
    refine ⟨x i, (mem_networkInitialSubsets A x j (x i)).mpr ⟨i,hi,rfl⟩, ?_⟩
    simpa only [hi] using ht
  · rintro ⟨u,hu,ht⟩
    obtain ⟨i,hi,he⟩ := (mem_networkInitialSubsets A x j u).mp hu
    refine ⟨i,hi,?_⟩
    simpa only [hi, he] using ht

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def reverseNetworkState {J : Type*} (d : ℕ) (p : J → PhysicalSettings d)
    (j : J) (i : Fin d) : SymmetricGroup (2 ^ d) :=
  sweepPrefix d (physicalSettingsEquiv d (p j)) i.1 *
    (sampleSweep d (physicalSettingsEquiv d (p j)))⁻¹

lemma reverseNetworkState_eq_endpointPath {J : Type*} (d : ℕ) (p : J → PhysicalSettings d)
    (j : J) (i : Fin d) (y : Fin (2 ^ d)) :
    reverseNetworkState d p j i y = endpointPath d i.1
      ((sampleSweep d (physicalSettingsEquiv d (p j))).symm y) y := by
  have h := sweepPrefix_eq_endpointPath d (physicalSettingsEquiv d (p j))
    ((sampleSweep d (physicalSettingsEquiv d (p j))).symm y) i.1 (Nat.le_of_lt i.2)
  simpa only [reverseNetworkState, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using h

lemma same_switch_eq_or_flip {d : ℕ} (i : Fin d) (x y : Fin (2 ^ d))
    (h : ∀ j, j ≠ i → (positionsEquiv d).symm y j = (positionsEquiv d).symm x j) :
    y = x ∨ y = flipPermutation d i x := by
  rcases binary_eq_or_flip i ((positionsEquiv d).symm x) ((positionsEquiv d).symm y) h with he | he
  · exact Or.inl ((positionsEquiv d).symm.injective he)
  · right
    apply (positionsEquiv d).symm.injective
    simpa only [flipPermutation, Equiv.permCongr_apply, Equiv.symm_apply_apply] using he

lemma endpointEncounter_maps_to_network {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (A : Finset I) (p : SubsetNetwork A → PhysicalSettings d) (y : I → Fin (2 ^ d))
    (hy : Function.Injective (labelLocation A y)) (a b : I)
    (hab : (endpointEncounter d ((mixedNetworkPermutation d A p).symm y) y).Adj a b) :
    (encounterGraph (reverseNetworkState d p)).Adj (labelLocation A y a) (labelLocation A y b) := by
  obtain ⟨hne,i,hi⟩ := hab
  refine ⟨fun he => hne (hy he), i, ?_⟩
  change reverseNetworkState d p (labelNetwork A b) i (y b) =
      reverseNetworkState d p (labelNetwork A a) i (y a) ∨
    reverseNetworkState d p (labelNetwork A b) i (y b) =
      flipPermutation d i (reverseNetworkState d p (labelNetwork A a) i (y a))
  apply same_switch_eq_or_flip
  intro j hj
  rw [reverseNetworkState_eq_endpointPath, reverseNetworkState_eq_endpointPath]
  exact (congrFun hi ⟨j,hj⟩).symm

lemma NoIsolatedVertex_image {I X : Type*} [DecidableEq I] [DecidableEq X]
    (G : SimpleGraph I) (H : SimpleGraph X) (S : Finset I) (f : I → X)
    (h : ∀ a b, G.Adj a b → H.Adj (f a) (f b)) (hS : NoIsolatedVertex G S) :
    NoIsolatedVertex H (S.image f) := by
  intro x hx
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,hab⟩ := hS a ha
  exact ⟨f b,Finset.mem_image.mpr ⟨b,hb,rfl⟩,h a b hab⟩

lemma reverse_endpoint_noIsolates_implies_network {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (A : Finset I) (x : InjectiveTuple I (2 ^ d))
    (p b : SubsetNetwork A → PhysicalSettings d)
    (h : NoIsolatedVertex (endpointEncounter d
      ((mixedNetworkPermutation d A b).symm (mixedNetworkPermutation d A p x))
      (mixedNetworkPermutation d A p x)) Finset.univ) :
    NoIsolatedVertex (encounterGraph (reverseNetworkState d b))
      (independentSampleSubset (networkInitialSubsets A x) p) := by
  rw [← labelOccupancy_eq_sampleSubset]
  exact NoIsolatedVertex_image _ _ _ _ (endpointEncounter_maps_to_network A b _
    (labelLocation_injective_sampled A x p)) h

end SignedSweeps
end

end OAI
