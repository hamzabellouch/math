import OAI.NumberTheory.JointDickman.Amplification.CandidateRepeatProbability
import OAI.NumberTheory.JointDickman.Amplification.IndependentForcedHits

namespace OAI

/-! # Occupied third-site primes that force an auxiliary root hit -/

namespace JointDickman
open Finset PublishedInputs

def CandidateForcedWitness {M : ℕ} (B : ℕ) (e : BlockCandidateIndex M)
    (S : Fin M → Finset ℕ) : Prop :=
  ∃ s : Fin M, s ≠ e.1.1 ∧ s ≠ e.1.2 ∧
    ∃ p ∈ candidateForcedPrimes B e s, p ∈ S s

open Classical in
theorem forcedWitness_merge_iff {B M : ℕ} (e : BlockCandidateIndex M)
    (a : ({e.1.1,e.1.2} : Finset (Fin M)) → (auxiliaryPrimes B).powerset)
    (b : {s : Fin M // s ∉ ({e.1.1,e.1.2} : Finset (Fin M))} → (auxiliaryPrimes B).powerset) :
    CandidateForcedWitness B e (fun i => (mergeSitePartition {e.1.1,e.1.2} a b i).val) ↔
      ∃ s : {s : Fin M // s ∉ ({e.1.1,e.1.2} : Finset (Fin M))},
        ∃ p ∈ candidateForcedPrimes B e s.val, p ∈ (b s).val := by
  constructor
  · rintro ⟨s,hi,hk,p,hp,hS⟩
    have hs : s ∉ ({e.1.1,e.1.2} : Finset (Fin M)) := by
      simp only [mem_insert,mem_singleton]; tauto
    refine ⟨⟨s,hs⟩,p,hp,?_⟩
    simpa only [mergeSitePartition,dite_eq_right hs] using hS
  · rintro ⟨s,p,hp,hS⟩
    have hs : s.val ≠ e.1.1 ∧ s.val ≠ e.1.2 := by
      simpa only [mem_insert,mem_singleton,not_or] using s.property
    refine ⟨s.val,hs.1,hs.2,p,hp,?_⟩
    simpa only [mergeSitePartition,dite_eq_right s.property] using hS

open Classical in
theorem forcedWitness_remaining_probability {B L T H M : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B) {e : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e)
    (a : ({e.1.1,e.1.2} : Finset (Fin M)) → (auxiliaryPrimes B).powerset) :
    finiteProbability
      (siteProductMass (fun _ : {s : Fin M // s ∉ ({e.1.1,e.1.2} : Finset (Fin M))} =>
        independentPrimeSetMass B))
      (fun b => CandidateForcedWitness B e
        (fun i => (mergeSitePartition {e.1.1,e.1.2} a b i).val)) ≤
      (M : ℝ)*(5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)) := by
  classical
  let I : Finset (Fin M) := {e.1.1,e.1.2}
  let w := siteProductMass (fun _ : {s : Fin M // s ∉ I} => independentPrimeSetMass B)
  let D := 5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hs (s : {s : Fin M // s ∉ I}) : finiteProbability w
      (fun b => ∃ p ∈ candidateForcedPrimes B e s.val, p ∈ (b s).val) ≤ D := by
    have hm := siteProduct_expectation_coordinate
      (fun _ : {s : Fin M // s ∉ I} => independentPrimeSetMass B)
      (fun _ => independentPrimeSetMass_sum B) s
      (fun R => if ∃ p ∈ candidateForcedPrimes B e s.val, p ∈ R.val then 1 else 0)
    have hh := hm.le.trans (candidate_forced_hit_bound hB hT hM hP he s.val)
    rw [finiteProbability_eq_indicator_mean]
    convert hh using 1
    apply congrArg (finiteExpectation w)
    funext b
    split_ifs <;> rfl
  have hevent : (fun b => CandidateForcedWitness B e
      (fun i => (mergeSitePartition I a b i).val)) =
      (fun b => ∃ s : {s : Fin M // s ∉ I},
        ∃ p ∈ candidateForcedPrimes B e s.val, p ∈ (b s).val) := by
    funext b
    exact propext (forcedWitness_merge_iff e a b)
  rw [hevent]
  calc
    _ ≤ ∑ s : {s : Fin M // s ∉ I}, finiteProbability w
        (fun b => ∃ p ∈ candidateForcedPrimes B e s.val, p ∈ (b s).val) :=
      finiteProbability_union_le w
        (siteProductMass_nonneg _ (fun _ => independentPrimeSetMass_nonneg B)) _
    _ ≤ ∑ _s : {s : Fin M // s ∉ I}, D := sum_le_sum (fun s _ => hs s)
    _ = (Fintype.card {s : Fin M // s ∉ I} : ℝ)*D := by simp
    _ ≤ (M : ℝ)*D := by
      apply mul_le_mul_of_nonneg_right _ hD
      exact_mod_cast (show Fintype.card {s : Fin M // s ∉ I} ≤ M from by
        simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun s : Fin M => s ∉ I))

end JointDickman

end OAI
