import OAI.NumberTheory.JointDickman.Arithmetic.OccupiedPrimeMass
import OAI.NumberTheory.JointDickman.Amplification.OutsideCandidateMass

namespace OAI

/-! # Cost of setting auxiliary root tests to zero at occupied primes -/

namespace JointDickman
open Finset

open Classical in
theorem bernoulli_l1_empty {α : Type*} [DecidableEq α] (I : Finset α)
    (p : ℕ) (hp : p.Prime) :
    (∑ S : I.powerset, |(if S.val = ∅ then 1 else 0)-
      bernoulliSubsetMass I (fun _ => 1/(p : ℝ)) S.val|) ≤ 2*(I.card : ℝ)/(p : ℝ) := by
  have hq (_i : α) (_hi : _i ∈ I) : 0 ≤ 1/(p : ℝ) ∧ 1/(p : ℝ) ≤ 1 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact ⟨by positivity,(div_le_one hp0).mpr (by exact_mod_cast hp.one_le)⟩
  have h := finiteHitMass_l1_point I
    (fun S : I.powerset => bernoulliSubsetMass I (fun _ => 1/(p : ℝ)) S.val)
    (fun S => bernoulliSubsetMass_nonneg (mem_powerset.mp S.property) hq)
    ((sum_coe_sort _ _).trans (bernoulliSubsetMass_sum _ _))
  have hh : (∑ i ∈ I, finiteProbability
      (fun S : I.powerset => bernoulliSubsetMass I (fun _ => 1/(p : ℝ)) S.val)
      (fun S => i ∈ S.val)) = (I.card : ℝ)/(p : ℝ) := by
    calc
      _ = ∑ _i ∈ I, 1/(p : ℝ) := sum_congr rfl (fun i hi => bernoulliSubsetMass_hit I _ hi)
      _ = _ := by simp [div_eq_mul_inv]
  rw [hh] at h
  simpa only [abs_sub_comm,mul_div_assoc] using h

open Classical in
noncomputable def siteConditionedRootPrimeMass {M : ℕ}
    (I : Finset (BlockCandidateIndex M)) (S : Fin M → Finset ℕ)
    (p : ℕ) [Fact p.Prime] (R : I.powerset) : ℝ :=
  if ∃ i, p ∈ S i then (if R.val = ∅ then 1 else 0) else outsideCandidatePrimeMass I p R

open Classical in
theorem siteConditionedRootPrimeMass_nonneg {M : ℕ}
    (I : Finset (BlockCandidateIndex M)) (S : Fin M → Finset ℕ)
    (p : ℕ) [Fact p.Prime] (R : I.powerset) : 0 ≤ siteConditionedRootPrimeMass I S p R := by
  unfold siteConditionedRootPrimeMass
  split_ifs <;> first | positivity | exact outsideCandidatePrimeMass_nonneg I p R

open Classical in
theorem siteConditionedRootPrimeMass_sum {M : ℕ}
    (I : Finset (BlockCandidateIndex M)) (S : Fin M → Finset ℕ)
    (p : ℕ) [Fact p.Prime] (hp : M < p) : (∑ R, siteConditionedRootPrimeMass I S p R) = 1 := by
  by_cases ho : ∃ i, p ∈ S i
  · simp only [siteConditionedRootPrimeMass,ho,ite_true]
    let empty : I.powerset := ⟨∅,by simp⟩
    have he (R : I.powerset) : R.val = ∅ ↔ R = empty :=
      ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
    simp only [he]
    simp
  · simpa only [siteConditionedRootPrimeMass,ho,ite_false] using outsideCandidatePrimeMass_sum I p hp

open Classical in
theorem siteConditionedRootPrimeMass_l1 {B M p : ℕ} [Fact p.Prime]
    (I : Finset (BlockCandidateIndex M)) (S : Fin M → Finset ℕ)
    (hp : p ∈ auxiliaryPrimes B) (hsize : M < p) (hhalf : 2*M ≤ p) :
    (∑ R : I.powerset, |siteConditionedRootPrimeMass I S p R-
      bernoulliSubsetMass I (fun _ => 1/(p : ℝ)) R.val|) ≤
      8*((I.card : ℝ)+(M : ℝ))^2/(p : ℝ)^2+
      (if p ∈ candidateDefectPrimes B I then 6*(I.card : ℝ)/(p : ℝ) else 0)+
      (if ∃ i, p ∈ S i then 2*(I.card : ℝ)/(p : ℝ) else 0) := by
  by_cases ho : ∃ i, p ∈ S i
  · simp only [siteConditionedRootPrimeMass,ho,ite_true]
    apply (bernoulli_l1_empty I p Fact.out).trans
    have hn : 0 ≤ 8*((I.card : ℝ)+(M : ℝ))^2/(p : ℝ)^2+
        (if p ∈ candidateDefectPrimes B I then 6*(I.card : ℝ)/(p : ℝ) else 0) := by
      split_ifs <;> positivity
    exact le_add_of_nonneg_left hn
  · simpa only [siteConditionedRootPrimeMass,ho,ite_false,add_zero] using
      outsideCandidatePrimeMass_l1 I hp hsize hhalf

end JointDickman

end OAI
