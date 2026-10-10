import OAI.NumberTheory.JointDickman.Amplification.RestrictedRootMass
import OAI.NumberTheory.JointDickman.Amplification.ConditionedRootComparison

namespace OAI

/-! # Both the regular and defective restricted root laws -/

namespace JointDickman
open Finset PublishedInputs

open Classical in
theorem restrictedRootMass_eq_categorical {α : Type*} [DecidableEq α]
    (I : Finset α) {p : ℕ} (root : α → ZMod p)
    (hinj : Set.InjOn root I) (U : Finset (ZMod p)) (hU : 0 < U.card)
    (hroot : ∀ i ∈ I, root i ∈ U) (S : I.powerset) :
    restrictedRootMass I root U S =
      categoricalSubsetMass I (fun _ => 1/(U.card : ℝ)) S.val := by
  have h := root_site_uniform_restricted_mean I root hinj U hU hroot
    (fun R => if R = S.val then (1 : ℝ) else 0)
  have hr : (∑ R ∈ I.powerset, categoricalSubsetMass I (fun _ => 1/(U.card : ℝ)) R*
      (if R = S.val then 1 else 0)) =
      categoricalSubsetMass I (fun _ => 1/(U.card : ℝ)) S.val := by
    simp only [mul_ite,mul_one,mul_zero]
    exact (sum_ite_eq' I.powerset S.val _).trans (ite_eq_left S.property)
  rw [hr] at h
  apply Eq.trans _ h
  unfold restrictedRootMass finitePushMass
  simp only [rootHitType,Subtype.ext_iff,sum_div,ite_div,zero_div]
  exact sum_coe_sort U (fun r => if rootHitSet I root r = S.val then 1/(U.card : ℝ) else 0)

open Classical in
/-- Even at a defective prime, each individual root test occupies at
most one allowed residue. No distinctness assumption is used here. -/
theorem restrictedRootMass_l1_crude {α : Type*} [DecidableEq α]
    (I : Finset α) {p : ℕ} (hp : p.Prime) (root : α → ZMod p)
    (U : Finset (ZMod p)) (hU : 0 < U.card) :
    (∑ S : I.powerset, |restrictedRootMass I root U S-
      bernoulliSubsetMass I (fun _ => 1/(p : ℝ)) S.val|) ≤
      2*(I.card : ℝ)/(U.card : ℝ)+2*(I.card : ℝ)/(p : ℝ) := by
  have hq (i : α) (_hi : i ∈ I) : 0 ≤ 1/(p : ℝ) ∧ 1/(p : ℝ) ≤ 1 := by
    have hpos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact ⟨by positivity,(div_le_one hpos).mpr (by exact_mod_cast hp.one_le)⟩
  have hv : (∑ S : I.powerset, bernoulliSubsetMass I (fun _ => 1/(p : ℝ)) S.val) = 1 :=
    (sum_coe_sort _ _).trans (bernoulliSubsetMass_sum _ _)
  apply (finiteHitMass_l1_le_marginals I (restrictedRootMass I root U)
    (fun S => bernoulliSubsetMass I (fun _ => 1/(p : ℝ)) S.val)
    (restrictedRootMass_nonneg I root U)
    (fun S => bernoulliSubsetMass_nonneg (mem_powerset.mp S.property) hq)
    (restrictedRootMass_sum I root U hU) hv).trans
  calc
    _ ≤ 2*(∑ _i ∈ I, 1/(U.card : ℝ))+2*(∑ _i ∈ I, 1/(p : ℝ)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (sum_le_sum (fun i hi =>
          restrictedRootMass_hit_le I root U hi)) (by norm_num)
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact sum_le_sum (fun i hi => (bernoulliSubsetMass_hit I _ hi).le)
    _ = _ := by simp [div_eq_mul_inv]; ring

open Classical in
theorem restrictedRootMass_l1_good {α : Type*} [DecidableEq α]
    (I : Finset α) {p : ℕ} [NeZero p] (root : α → ZMod p)
    (hinj : Set.InjOn root I) (forbidden : Finset (ZMod p))
    (hsize : forbidden.card < p) (hhalf : 2*forbidden.card ≤ p)
    (havoid : ∀ i ∈ I, root i ∉ forbidden) :
    (∑ S : I.powerset, |restrictedRootMass I root (univ \ forbidden) S-
      bernoulliSubsetMass I (fun _ => 1/(p : ℝ)) S.val|) ≤
      8*((I.card : ℝ)+(forbidden.card : ℝ))^2/(p : ℝ)^2 := by
  have hcard : (univ \ forbidden).card = p-forbidden.card := by
    rw [card_sdiff_of_subset (subset_univ forbidden),card_univ,ZMod.card]
  have hU : 0 < (univ \ forbidden).card := by rw [hcard]; omega
  have hroot (i : α) (hi : i ∈ I) : root i ∈ univ \ forbidden :=
    mem_sdiff.mpr ⟨mem_univ _,havoid i hi⟩
  simp_rw [restrictedRootMass_eq_categorical I root hinj _ hU hroot,hcard]
  exact (sum_coe_sort _ _).trans_le (unoccupied_categorical_l1 I p forbidden.card hsize hhalf)

end JointDickman

end OAI
