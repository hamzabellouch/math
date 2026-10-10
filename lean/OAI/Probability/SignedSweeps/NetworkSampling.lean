import OAI.Probability.SignedSweeps.MixedNetworks

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma sweptSubsetLaw_eq_sampleProb (d : ℕ) (S T : Finset (Fin (2 ^ d))) :
    sweptSubsetLaw d S T = finiteProb (fun p : PhysicalSettings d =>
      S.image (sampleSweep d (physicalSettingsEquiv d p)) = T) := by
  unfold sweptSubsetLaw
  rw [subsetSweep_eq_sampleMean, ← finiteMean_equiv ℝ (physicalSettingsEquiv d)
    (fun a => subsetRepresentation (Fin (2 ^ d)) (sampleSweep d a))]
  simp only [finiteMean, LinearMap.smul_apply, LinearMap.sum_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, subsetRepresentation, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  unfold finiteProb finiteMean
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  have h : T.image ((sampleSweep d (physicalSettingsEquiv d p))⁻¹ : SymmetricGroup (2 ^ d)) = S ↔
      S.image (sampleSweep d (physicalSettingsEquiv d p)) = T := by
    constructor
    · intro h
      rw [← h, Finset.image_image]
      simp only [Function.comp_def, Equiv.Perm.coe_inv, Equiv.apply_symm_apply, Finset.image_id']
    · intro h
      rw [← h, Finset.image_image]
      simp only [Function.comp_def, Equiv.Perm.coe_inv, Equiv.symm_apply_apply, Finset.image_id']
  simp only [h]
  split_ifs <;> rfl

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J] {d : ℕ}

def independentSampleSubset (S : J → Finset (Fin (2 ^ d))) (p : J → PhysicalSettings d) :
    Finset (J × Fin (2 ^ d)) :=
  subsetFiberEquiv.symm (fun j => (S j).image (sampleSweep d (physicalSettingsEquiv d (p j))))

lemma fiber_independentSampleSubset (S : J → Finset (Fin (2 ^ d))) (p : J → PhysicalSettings d) (j : J) :
    subsetFiber (independentSampleSubset S p) j =
      (S j).image (sampleSweep d (physicalSettingsEquiv d (p j))) := by
  exact congrFun (subsetFiberEquiv.apply_symm_apply _) j

lemma independentSampleSubset_law (S : J → Finset (Fin (2 ^ d))) (T : Finset (J × Fin (2 ^ d))) :
    finiteProb (fun p : J → PhysicalSettings d => independentSampleSubset S p = T) = independentSweptLaw S T := by
  calc
    _ = finiteProb (fun p : J → PhysicalSettings d => ∀ j,
        (S j).image (sampleSweep d (physicalSettingsEquiv d (p j))) = subsetFiber T j) := by
      apply finiteProb_congr
      intro p
      constructor
      · intro h j
        rw [← fiber_independentSampleSubset, h]
      · intro h
        apply subsetFiberEquiv.injective
        funext j
        rw [show subsetFiberEquiv (independentSampleSubset S p) j = _ from fiber_independentSampleSubset S p j]
        exact h j
    _ = ∏ j, finiteProb (fun p : PhysicalSettings d =>
        (S j).image (sampleSweep d (physicalSettingsEquiv d p)) = subsetFiber T j) :=
      finiteProb_pi_forall (fun _ : J => PhysicalSettings d) (fun j p =>
        (S j).image (sampleSweep d (physicalSettingsEquiv d p)) = subsetFiber T j)
    _ = _ := by
      simp only [← sweptSubsetLaw_eq_sampleProb, independentSweptLaw, independentSubsetLaw]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma finiteProb_eq_sum_fibers {A X : Type*} [Fintype A] [Fintype X]
    (s : A → X) (R : X → Prop) :
    finiteProb (fun a => R (s a)) = ∑ x : {x : X // R x}, finiteProb (fun a => s a = x.1) := by
  have h := finiteProb_real_kernel_apply s (fun x => if R x then 1 else 0)
  change _ = finiteProb (fun a => R (s a)) at h
  rw [← h, ← Finset.sum_subtype (Finset.univ.filter R) (by simp) (fun x => finiteProb (fun a => s a = x))]
  simp only [Finset.sum_filter, mul_ite, mul_one, mul_zero]

theorem independentSampleSubset_noIsolates_bound {J : Type*} [Fintype J] [DecidableEq J] {d : ℕ}
    (state : J → Fin d → SymmetricGroup (2 ^ d)) (S : J → Finset (Fin (2 ^ d)))
    (k : ℕ) (hk : k = ∑ j, (S j).card)
    (hΔ : 0 < 2 * (d : ℝ) * k / (2 ^ d : ℕ))
    (hΔ1 : 2 * (d : ℝ) * k / (2 ^ d : ℕ) ≤ 1) :
    finiteProb (fun p : J → PhysicalSettings d => NoIsolatedVertex (encounterGraph state)
      (independentSampleSubset S p)) ≤
        (Real.sqrt (2 * (d : ℝ) * k / (2 ^ d : ℕ))) ^ k * Real.exp (Real.exp 2 * k) := by
  rw [finiteProb_eq_sum_fibers]
  simp only [independentSampleSubset_law]
  exact swept_network_noIsolates_bound state S k hk hΔ hΔ1

end SignedSweeps
end

end OAI
