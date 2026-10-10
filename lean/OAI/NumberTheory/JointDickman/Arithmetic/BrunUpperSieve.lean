import OAI.NumberTheory.JointDickman.Arithmetic.BrunBlockPopulation
import OAI.NumberTheory.JointDickman.Arithmetic.BrunBlockMeanProduct
import OAI.NumberTheory.JointDickman.Arithmetic.BrunBlockDimension
import OAI.NumberTheory.JointDickman.Arithmetic.BrunProductCutoff

namespace OAI

/-! # An unconditional proof of the required upper sieve

Even inclusion-exclusion truncations on disjoint logarithmic prime blocks have
coefficients of absolute value one. Their orders grow with the block index,
so their errors are summable while every supported prime product stays below
`z`. This proves the finite-event consequence of Ford's Theorem 2.4 used here.
-/
namespace JointDickman
open Finset

noncomputable def brunSieveConstant (κ A : ℝ) : ℝ :=
  Real.exp (Real.exp (4*(κ*Real.log 2+A/Real.log 2)) + (κ*Real.log 8+A/Real.log 2))

 theorem brunPrimeBlocks_survival {P : Finset ℕ} {g : ℕ → ℝ} {κ A z : ℝ}
    (hP : ∀ p ∈ P, p.Prime ∧ (p:ℝ) ≤ z)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hd : SieveDimension P g κ A z) (hz : 2 ≤ z) (N : ℕ)
    (hN : ∀ p ∈ P, (Real.log z/8)/(2:ℝ)^N < Real.log p) :
    (∏ i : Fin N, ∏ p ∈ brunPrimeBlock P (Real.log z/8) i.val, (1-g p)) ≤
      Real.exp (κ*Real.log 8+A/Real.log 2)*(∏ p ∈ P, (1-g p)) := by
  have hL : 0 ≤ Real.log z/8 := div_nonneg (Real.log_nonneg (by linarith)) (by norm_num)
  have hdj : (↑(univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint
      (fun i : Fin N => brunPrimeBlock P (Real.log z/8) i.val) := by
    intro i _ j _ hij
    exact brunPrimeBlocks_disjoint P hL N hij
  rw [← prod_biUnion hdj]
  change (∏ p ∈ brunBlockUnion (fun i : Fin N => brunPrimeBlock P (Real.log z/8) i.val), (1-g p)) ≤ _
  rw [brunPrimeBlocks_union P hL N hN]
  exact sieve_survival_subset (filter_subset _ _) hg (brunPrimeTail_inverse_bound hP hg hκ hA hd hz)

 theorem brunPrimeBlocks_mean_bound {P : Finset ℕ} {g : ℕ → ℝ} {κ A z : ℝ}
    (hP : ∀ p ∈ P, p.Prime ∧ (p:ℝ) ≤ z)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (hd : SieveDimension P g κ A z) (hz : 2 ≤ z) (N : ℕ)
    (hN : ∀ p ∈ P, (Real.log z/8)/(2:ℝ)^N < Real.log p) :
    (∏ i : Fin N, brunMean (brunPrimeBlock P (Real.log z/8) i.val) g (i.val+1)) ≤
      brunSieveConstant κ A*(∏ p ∈ P, (1-g p)) := by
  have hlog : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hL : 0 ≤ Real.log z/8 := by positivity
  have hLz : Real.log z/8 ≤ Real.log z := by linarith
  calc
    _ ≤ (∏ i : Fin N, ∏ p ∈ brunPrimeBlock P (Real.log z/8) i.val, (1-g p))*
        Real.exp (Real.exp (4*(κ*Real.log 2+A/Real.log 2))) := by
      apply brunBlockMean_product
      · intro i p hp
        exact hg p (brunPrimeBlock_subset _ _ _ hp)
      · intro i
        exact brunPrimeBlock_inverse_bound hP hg hκ hA hd hz hL hLz i.val
    _ ≤ (Real.exp (κ*Real.log 8+A/Real.log 2)*(∏ p ∈ P, (1-g p)))*
        Real.exp (Real.exp (4*(κ*Real.log 2+A/Real.log 2))) :=
      mul_le_mul_of_nonneg_right (brunPrimeBlocks_survival hP hg hκ hA hd hz N hN) (Real.exp_pos _).le
    _ = _ := by
      conv_rhs => rw [brunSieveConstant,Real.exp_add]
      ring

 theorem fordUpperSieveInput : PublishedInputs.FordUpperSieveInput := by
  intro κ A hκ hA
  refine ⟨brunSieveConstant κ A,Real.exp_pos _,?_⟩
  intro X _ P E w M z g hz hM hw hP hg hd
  have hlog : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hL : 0 ≤ Real.log z/8 := by positivity
  obtain ⟨N,hN⟩ := exists_brun_block_depth (Real.log z/8)
  have hNP : ∀ p ∈ P, (Real.log z/8)/(2:ℝ)^N < Real.log p :=
    fun p hp => hN.trans_le (prime_log_two_le (hP p hp).1)
  have hpop := brunBlock_population_bound P (fun i : Fin N => brunPrimeBlock P (Real.log z/8) i.val)
    (fun i => i.val+1) (brunPrimeBlocks_disjoint P hL N)
    (fun i => brunPrimeBlock_subset _ _ _) E w hw M z g
    (fun D hD => brunPrimeBlocks_cutoff P hL (by linarith) (by linarith)
      (fun p hp => by exact_mod_cast (hP p hp).1.pos) N D hD)
  apply hpop.trans
  apply add_le_add _ le_rfl
  calc
    _ ≤ M*(brunSieveConstant κ A*(∏ p ∈ P, (1-g p))) :=
      mul_le_mul_of_nonneg_left (brunPrimeBlocks_mean_bound hP hg hκ.le hA hd hz N hNP) hM
    _ = _ := by ring

end JointDickman

end OAI
