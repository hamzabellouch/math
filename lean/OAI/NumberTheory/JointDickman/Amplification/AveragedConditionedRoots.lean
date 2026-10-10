import OAI.NumberTheory.JointDickman.Probability.SiteConditionedError

namespace OAI

/-! # Averaging the conditioned root comparison over the actual candidate lists -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

open Classical in
theorem averaged_siteConditionedError {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ), 0 < T →
      (T : ℝ) ≤ Real.exp B → (M : ℝ) ≤ Real.exp B → M ≤ B^2 →
      finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => siteConditionedError B L T H M τ C (fun i => (S i).val)) ≤
        212*(B : ℝ)^19/(auxiliaryCutoff B : ℝ)+
        2*(B : ℝ)^6*(M : ℝ)/(auxiliaryCutoff B : ℝ)+
        2*((M : ℝ)^3*(B : ℝ)^2/((T : ℝ)*Real.exp B)) := by
  filter_upwards [siteConditionedError_pointwise hL hτ hτsmall,
    repeatedCandidateRoot_probability hL hτ hτsmall,eventually_ge_atTop 2]
    with B hpoint hrepeat hB
  intro C T H M hT hTexp hMexp hM
  let w := siteProductMass (fun _ : Fin M => independentPrimeSetMass B)
  have hw : ∀ S, 0 ≤ w S := siteProductMass_nonneg _ (fun _ => independentPrimeSetMass_nonneg B)
  have hwone : ∑ S, w S = 1 := siteProductMass_sum _ (fun _ => independentPrimeSetMass_sum B)
  have hind : finiteExpectation w (fun S =>
      if RepeatedCandidateRoot B L T H M τ C (fun i => (S i).val) then 2 else 0) =
      2*finiteProbability w (fun S => RepeatedCandidateRoot B L T H M τ C (fun i => (S i).val)) := by
    unfold finiteExpectation finiteProbability
    dsimp only
    rw [mul_sum]
    apply sum_congr rfl
    intro S _
    by_cases h : RepeatedCandidateRoot B L T H M τ C (fun i => (S i).val) <;> simp [h,mul_comm]
  have hs : (∑ p ∈ auxiliaryPrimes B, 1/(p : ℝ)^2) ≤ 1/(auxiliaryCutoff B : ℝ) :=
    sum_reciprocal_square_tail _ (pow_ne_zero _ (by omega))
      (fun p hp => by exact_mod_cast (mem_filter.mp hp).2)
  have hoc : finiteExpectation w (fun S => occupiedPrimeReciprocalMass B (fun i => (S i).val)) ≤
      (M : ℝ)/(auxiliaryCutoff B : ℝ) :=
    (independent_occupied_prime_mass B M).trans (by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg M))
  calc
    _ ≤ finiteExpectation w (fun S =>
        212*(B : ℝ)^19/(auxiliaryCutoff B : ℝ)+
        2*(B : ℝ)^6*occupiedPrimeReciprocalMass B (fun i => (S i).val)+
        if RepeatedCandidateRoot B L T H M τ C (fun i => (S i).val) then 2 else 0) :=
      finiteExpectation_mono w hw (fun S => hpoint C T H M _ hTexp hMexp hM)
    _ = 212*(B : ℝ)^19/(auxiliaryCutoff B : ℝ)+
        2*(B : ℝ)^6*finiteExpectation w (fun S => occupiedPrimeReciprocalMass B (fun i => (S i).val))+
        2*finiteProbability w (fun S => RepeatedCandidateRoot B L T H M τ C (fun i => (S i).val)) := by
      rw [finiteExpectation_add,finiteExpectation_add,finiteExpectation_const w hwone,
        finiteExpectation_const_mul,hind]
    _ ≤ _ := by
      have ha := mul_le_mul_of_nonneg_left hoc (show 0 ≤ 2*(B : ℝ)^6 by positivity)
      have hb := mul_le_mul_of_nonneg_left (hrepeat C T H M hT) (show (0 : ℝ) ≤ 2 by norm_num)
      convert add_le_add (add_le_add le_rfl ha) hb using 1
      ring

end JointDickman

end OAI
