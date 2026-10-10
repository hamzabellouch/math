import OAI.NumberTheory.JointDickman.Amplification.ConditionedRootErrorLimit
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSiteTranspose

namespace OAI

/-! # Transferring bounded tests to independent auxiliary roots -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

theorem finiteExpectation_abs_bound {Ω : Type*} [Fintype Ω]
    (w f : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) :
    |finiteExpectation w f| ≤ finiteExpectation w (fun x => |f x|) := by
  unfold finiteExpectation
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro x _
  rw [abs_mul,abs_of_nonneg (hw x)]

theorem finiteExpectation_difference_l1 {Ω : Type*} [Fintype Ω]
    (w v f : Ω → ℝ) {L : ℝ} (hf : ∀ x, |f x| ≤ L) :
    |finiteExpectation w f-finiteExpectation v f| ≤ L*(∑ x, |w x-v x|) := by
  unfold finiteExpectation
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ x, |w x*f x-v x*f x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |w x-v x| * L := by
      apply sum_le_sum
      intro x _
      rw [← sub_mul,abs_mul]
      exact mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)
    _ = _ := by rw [← sum_mul,mul_comm]

theorem siteConditionedRoot_test {B L T H M : ℕ} {τ C : ℝ}
    (S : Fin M → Finset ℕ)
    (F : (blockCandidates B L T H M τ C S → (auxiliaryPrimes B).powerset) → ℝ)
    {K : ℝ} (hF : ∀ R, |F R| ≤ K) :
    |finiteExpectation (siteConditionedRootProductMass B (blockCandidates B L T H M τ C S) S)
        (fun R => F (primeSiteTranspose (blockCandidates B L T H M τ C S) (auxiliaryPrimes B) R))-
      finiteExpectation (siteProductMass
        (fun _ : blockCandidates B L T H M τ C S => independentPrimeSetMass B)) F| ≤
      K*siteConditionedError B L T H M τ C S := by
  let I := blockCandidates B L T H M τ C S
  have hind : finiteExpectation (siteProductMass (fun _ : I => independentPrimeSetMass B)) F =
      finiteExpectation (bernoulliProductMass I (fun p : auxiliaryPrimes B => fun _ => 1/(p.val : ℝ)))
        (fun R => F (primeSiteTranspose I (auxiliaryPrimes B) R)) :=
    (primeSiteTranspose_sum I (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) F).symm
  rw [hind]
  exact finiteExpectation_difference_l1 _ _ _ (fun R => hF (primeSiteTranspose I (auxiliaryPrimes B) R))

open Classical in
theorem averaged_siteConditionedRoot_test {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ), 0 < T →
      (T : ℝ) ≤ Real.exp B → (M : ℝ) ≤ Real.exp B → M ≤ B^2 →
      ∀ F : (S : Fin M → (auxiliaryPrimes B).powerset) →
        (blockCandidates B L T H M τ C (fun i => (S i).val) → (auxiliaryPrimes B).powerset) → ℝ,
      (∀ S R, |F S R| ≤ (B : ℝ)^10) →
      |finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => finiteExpectation
          (siteConditionedRootProductMass B (blockCandidates B L T H M τ C (fun i => (S i).val))
            (fun i => (S i).val))
          (fun R => F S (primeSiteTranspose
            (blockCandidates B L T H M τ C (fun i => (S i).val)) (auxiliaryPrimes B) R)))-
       finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => finiteExpectation (siteProductMass
          (fun _ : blockCandidates B L T H M τ C (fun i => (S i).val) => independentPrimeSetMass B)) (F S))| ≤
        (B : ℝ)^10*conditionedRootError B := by
  filter_upwards [averaged_siteConditionedError hL hτ hτsmall,eventually_ge_atTop 1] with B hB hB1
  intro C T H M hT hTexp hMexp hM F hF
  let w := siteProductMass (fun _ : Fin M => independentPrimeSetMass B)
  have hw : ∀ S, 0 ≤ w S := siteProductMass_nonneg _ (fun _ => independentPrimeSetMass_nonneg B)
  rw [← finiteExpectation_sub]
  apply (finiteExpectation_abs_bound w _ hw).trans
  calc
    _ ≤ finiteExpectation w (fun S => (B : ℝ)^10*
        siteConditionedError B L T H M τ C (fun i => (S i).val)) :=
      finiteExpectation_mono w hw (fun S => siteConditionedRoot_test _ (F S) (hF S))
    _ = (B : ℝ)^10*finiteExpectation w
        (fun S => siteConditionedError B L T H M τ C (fun i => (S i).val)) := finiteExpectation_const_mul _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((hB C T H M hT hTexp hMexp hM).trans (conditionedRootError_majorant hB1 hT hM))
      (by positivity)

end JointDickman

end OAI
