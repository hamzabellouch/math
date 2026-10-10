import OAI.NumberTheory.JointDickman.Amplification.FiniteHitMass
import OAI.NumberTheory.JointDickman.Arithmetic.BlockPrimeSites
import OAI.NumberTheory.JointDickman.Arithmetic.RequiredPrimeSubset

namespace OAI

/-! # The actual root-hit law on a restricted residue set -/

namespace JointDickman
open Finset PublishedInputs

noncomputable def restrictedRootMass {α : Type*} [DecidableEq α]
    (I : Finset α) {p : ℕ} (root : α → ZMod p) (U : Finset (ZMod p))
    (S : I.powerset) : ℝ :=
  finitePushMass (fun _ : U => 1/(U.card : ℝ)) (fun r => rootHitType I root r.val) S

theorem restrictedRootMass_nonneg {α : Type*} [DecidableEq α]
    (I : Finset α) {p : ℕ} (root : α → ZMod p) (U : Finset (ZMod p))
    (S : I.powerset) : 0 ≤ restrictedRootMass I root U S :=
  finitePushMass_nonneg _ (fun _ => by positivity) _ _

theorem restrictedRootMass_sum {α : Type*} [DecidableEq α]
    (I : Finset α) {p : ℕ} (root : α → ZMod p) (U : Finset (ZMod p)) (hU : 0 < U.card) :
    (∑ S, restrictedRootMass I root U S) = 1 := by
  classical
  unfold restrictedRootMass
  rw [finitePushMass_sum]
  simp only [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul]
  field_simp

open Classical in
theorem restrictedRootMass_hit_le {α : Type*} [DecidableEq α]
    (I : Finset α) {p : ℕ} (root : α → ZMod p) (U : Finset (ZMod p))
    {i : α} (hi : i ∈ I) :
    finiteProbability (restrictedRootMass I root U) (fun S => i ∈ S.val) ≤ 1/(U.card : ℝ) := by
  unfold restrictedRootMass
  rw [finitePushMass_probability]
  unfold finiteProbability
  have he (r : U) : i ∈ (rootHitType I root r.val).val ↔ root i = r.val := by
    simp only [rootHitType,rootHitSet,mem_filter,hi,true_and]
  simp only [he]
  have hh : (∑ r : U, if root i = r.val then 1/(U.card : ℝ) else 0) =
      ∑ r ∈ U, if root i = r then 1/(U.card : ℝ) else 0 :=
    sum_coe_sort U (fun r => if root i = r then 1/(U.card : ℝ) else 0)
  rw [hh]
  by_cases hr : root i ∈ U
  · simp [eq_comm,hr]
  · simp [eq_comm,hr]

open Classical in
theorem bernoulliSubsetMass_hit {α : Type*} [DecidableEq α]
    (I : Finset α) (q : α → ℝ) {i : α} (hi : i ∈ I) :
    finiteProbability (fun S : I.powerset => bernoulliSubsetMass I q S.val)
      (fun S => i ∈ S.val) = q i := by
  unfold finiteProbability
  dsimp only
  have hh := sum_coe_sort I.powerset
    (fun S => if i ∈ S then bernoulliSubsetMass I q S else 0)
  calc
    _ = ∑ S ∈ I.powerset, if i ∈ S then bernoulliSubsetMass I q S else 0 := by
      convert hh using 1
      apply sum_congr rfl
      intro S _
      by_cases hs : i ∈ S.val <;> simp [hs]
    _ = q i := by
      simpa only [singleton_subset_iff,prod_singleton] using
        bernoulliSubsetMass_required I {i} q (singleton_subset_iff.mpr hi)

end JointDickman

end OAI
