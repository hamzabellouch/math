import OAI.NumberTheory.JointDickman.Amplification.FinitePointMass
import OAI.NumberTheory.JointDickman.Probability.CandidateThirdSiteProbability

namespace OAI

/-! # Finite subset laws controlled by their hit probabilities -/

namespace JointDickman
open Finset PublishedInputs

open Classical in
theorem finitePushMass_probability {Ω A : Type*} [Fintype Ω] [Fintype A]
    (w : Ω → ℝ) (f : Ω → A) (E : A → Prop) :
    finiteProbability (finitePushMass w f) E = finiteProbability w (fun x => E (f x)) := by
  simp only [finiteProbability_eq_indicator_mean,finiteExpectation]
  exact finitePushMass_test_real w f (fun a => if E a then 1 else 0)

open Classical in
theorem finiteHitMass_l1_point {α : Type*} [DecidableEq α]
    (I : Finset α) (w : I.powerset → ℝ) (hw : ∀ S, 0 ≤ w S)
    (hwone : ∑ S, w S = 1) :
    (∑ S, |w S-(if S.val = ∅ then 1 else 0)|) ≤
      2*∑ i ∈ I, finiteProbability w (fun S => i ∈ S.val) := by
  let empty : I.powerset := ⟨∅,by simp⟩
  have hempty (S : I.powerset) : S = empty ↔ S.val = ∅ := Subtype.ext_iff
  have hp := finiteMass_l1_point w hw hwone empty
  simp only [hempty] at hp
  rw [hp]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hevent : (fun S : I.powerset => S.val ≠ ∅) =
      (fun S => ∃ i ∈ I, i ∈ S.val) := by
    funext S
    apply propext
    constructor
    · intro h
      obtain ⟨i,hi⟩ := nonempty_iff_ne_empty.mpr h
      exact ⟨i,mem_powerset.mp S.property hi,hi⟩
    · rintro ⟨i,_,hi⟩ h
      simp only [h,Finset.notMem_empty] at hi
  simp only [ne_eq,hempty] at ⊢
  rw [hevent]
  exact finiteProbability_exists_mem w hw I (fun i S => i ∈ S.val)

open Classical in
theorem finiteHitMass_l1_le_marginals {α : Type*} [DecidableEq α]
    (I : Finset α) (w v : I.powerset → ℝ)
    (hw : ∀ S, 0 ≤ w S) (hv : ∀ S, 0 ≤ v S)
    (hwone : ∑ S, w S = 1) (hvone : ∑ S, v S = 1) :
    (∑ S, |w S-v S|) ≤
      2*∑ i ∈ I, finiteProbability w (fun S => i ∈ S.val)+
      2*∑ i ∈ I, finiteProbability v (fun S => i ∈ S.val) := by
  calc
    _ ≤ (∑ S, |w S-(if S.val = ∅ then 1 else 0)|)+
        ∑ S, |v S-(if S.val = ∅ then 1 else 0)| := by
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro S _
      simpa only [abs_sub_comm] using
        abs_sub_le (w S) (if S.val = ∅ then 1 else 0) (v S)
    _ ≤ _ := add_le_add (finiteHitMass_l1_point I w hw hwone)
      (finiteHitMass_l1_point I v hv hvone)

end JointDickman

end OAI
