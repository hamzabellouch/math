import OAI.NumberTheory.JointDickman.Probability.SiteConditionedRootProduct
import OAI.NumberTheory.JointDickman.Amplification.ActualCandidateProduct

namespace OAI

/-! # Averaged distance of the conditioned root model from independent roots -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

noncomputable def siteConditionedError (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) : ℝ :=
  let I := blockCandidates B L T H M τ C S
  ∑ R, |siteConditionedRootProductMass B I S R-
    bernoulliProductMass I (fun p : auxiliaryPrimes B => fun _ => 1/(p.val : ℝ)) R|

theorem siteConditionedError_le_two {B L T H M : ℕ} {τ C : ℝ}
    (S : Fin M → Finset ℕ) (hsize : ∀ p ∈ auxiliaryPrimes B, M < p) :
    siteConditionedError B L T H M τ C S ≤ 2 := by
  let I := blockCandidates B L T H M τ C S
  let a := fun p : auxiliaryPrimes B => @siteConditionedRootPrimeMass M I S p.val
    ⟨auxiliaryPrimes_prime B p.val p.property⟩
  let b := fun p : auxiliaryPrimes B => fun R : I.powerset =>
    bernoulliSubsetMass I (fun _ => 1/(p.val : ℝ)) R.val
  have ha (p : auxiliaryPrimes B) (R : I.powerset) : 0 ≤ a p R := by
    let : Fact p.val.Prime := ⟨auxiliaryPrimes_prime B p.val p.property⟩
    exact siteConditionedRootPrimeMass_nonneg I S p.val R
  have haone (p : auxiliaryPrimes B) : ∑ R, a p R = 1 := by
    let : Fact p.val.Prime := ⟨auxiliaryPrimes_prime B p.val p.property⟩
    exact siteConditionedRootPrimeMass_sum I S p.val (hsize p.val p.property)
  have hb (p : auxiliaryPrimes B) (R : I.powerset) : 0 ≤ b p R := by
    apply bernoulliSubsetMass_nonneg (mem_powerset.mp R.property)
    intro _ _
    have hp : (1 : ℝ) ≤ p.val := by exact_mod_cast (auxiliaryPrimes_prime B p.val p.property).one_le
    exact ⟨by positivity,(div_le_one (by linarith)).mpr hp⟩
  have hbone (p : auxiliaryPrimes B) : ∑ R, b p R = 1 :=
    (sum_coe_sort _ _).trans (bernoulliSubsetMass_sum _ _)
  exact finiteMass_l1_le_two (finiteProductMass a) (finiteProductMass b)
    (finiteProductMass_nonneg a ha) (finiteProductMass_nonneg b hb)
    (finiteProductMass_sum a haone) (finiteProductMass_sum b hbone)

open Classical in
theorem siteConditionedError_pointwise {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ) (S : Fin M → Finset ℕ),
      (T : ℝ) ≤ Real.exp B → (M : ℝ) ≤ Real.exp B → M ≤ B^2 →
      siteConditionedError B L T H M τ C S ≤
        212*(B : ℝ)^19/(auxiliaryCutoff B : ℝ)+
        2*(B : ℝ)^6*occupiedPrimeReciprocalMass B S+
        if RepeatedCandidateRoot B L T H M τ C S then 2 else 0 := by
  filter_upwards [blockCandidates_card hL hτ hτsmall,eventually_ge_atTop 2] with B hcard hB
  intro C T H M S hT hMexp hM
  have ho : 0 ≤ occupiedPrimeReciprocalMass B S := by
    unfold occupiedPrimeReciprocalMass
    exact sum_nonneg (fun _ _ => by split_ifs <;> positivity)
  by_cases hr : RepeatedCandidateRoot B L T H M τ C S
  · rw [ite_eq_left hr]
    exact (siteConditionedError_le_two S (fun p hp => (block_prime_twice_sites hB hM hp).1)).trans
      (le_add_of_nonneg_left (by positivity))
  · rw [ite_eq_right hr,add_zero]
    let I := blockCandidates B L T H M τ C S
    have hP : 0 < auxiliaryCutoff B := pow_pos (by omega) 1000
    have hs : (∑ p ∈ auxiliaryPrimes B, 1/(p : ℝ)^2) ≤ 1/(auxiliaryCutoff B : ℝ) :=
      sum_reciprocal_square_tail _ hP.ne' (fun p hp => by exact_mod_cast (mem_filter.mp hp).2)
    have hd := candidateDefectPrimes_mass hB hT hMexp hP I
      (fun _ he => (mem_blockCandidates.mp he).2) (actual_candidate_roots_inj hr)
    have hn : (I.card : ℝ) ≤ (B : ℝ)^6 := by
      exact_mod_cast candidate_count_power_bound hM (hcard C T H M S)
    exact (siteConditionedRootProduct_l1 I S
      (fun p hp => (block_prime_twice_sites hB hM hp).1)
      (fun p hp => (block_prime_twice_sites hB hM hp).2)).trans
      (add_le_add (root_product_error_polynomial (by omega) hM (hcard C T H M S) hs hd)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) ho))

end JointDickman

end OAI
