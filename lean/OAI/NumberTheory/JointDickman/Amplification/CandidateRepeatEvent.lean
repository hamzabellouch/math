import OAI.NumberTheory.JointDickman.Counting.IndependentLargeCoefficients
import OAI.NumberTheory.JointDickman.Probability.SitePartition

namespace OAI

/-! # The local third-site event covering coincident rational roots -/

namespace JointDickman
open Finset PublishedInputs

open Classical in
noncomputable def pairSplitChoices (B L : ℕ) (τ C : ℝ) (S R : Finset ℕ) :
    Finset (Finset ℕ × Finset ℕ) :=
  (endpointSplits B L τ C S).product (endpointSplits B L τ C R)

def CandidateRepeatWitness {M : ℕ} (T : ℕ) (e : BlockCandidateIndex M)
    (S : Fin M → Finset ℕ) : Prop :=
  ∃ s : Fin M, s ≠ e.1.1 ∧ s ≠ e.1.2 ∧
    T*candidateQuotient e ≤ (candidateSiteValue e s).natAbs ∧
    PrimeProductAvailable (candidateSiteValue e s).natAbs (S s)

def PairRepeatEvent (B L T H M : ℕ) (τ C : ℝ) (i k : Fin M)
    (S : Fin M → Finset ℕ) : Prop :=
  ∃ ab ∈ pairSplitChoices B L τ C (S i) (S k),
    BlockCandidateAdmissible B L T H τ C ((i,k),ab) ∧
    CandidateRepeatWitness T ((i,k),ab) S

/-- This event is a consequence of actual candidate membership and equal
rational roots, not a premise about independence. -/
theorem coincident_candidates_pair_event {B L T H M : ℕ} {τ C : ℝ}
    {S : Fin M → Finset ℕ} {e f : BlockCandidateIndex M}
    (he : e ∈ blockCandidates B L T H M τ C S)
    (hf : f ∈ blockCandidates B L T H M τ C S)
    (hp : e.1 ≠ f.1) (hr : blockCandidateRoot e = blockCandidateRoot f) :
    PairRepeatEvent B L T H M τ C e.1.1 e.1.2 S := by
  have hw := coincident_candidate_has_third_coefficient he hf hp hr
  obtain ⟨hs,ha⟩ := mem_blockCandidates.mp he
  refine ⟨e.2,?_,?_,?_⟩
  · simpa only [pairSplitChoices,Finset.product_eq_sprod,mem_product] using hs
  · exact ha
  · obtain ⟨s,hi,hk,havail,hlarge⟩ := hw
    exact ⟨s,hi,hk,hlarge,havail⟩

open Classical in
theorem repeatWitness_merge_iff {B T M : ℕ} (e : BlockCandidateIndex M)
    (a : ({e.1.1,e.1.2} : Finset (Fin M)) → (auxiliaryPrimes B).powerset)
    (b : {s : Fin M // s ∉ ({e.1.1,e.1.2} : Finset (Fin M))} → (auxiliaryPrimes B).powerset) :
    CandidateRepeatWitness T e (fun i => (mergeSitePartition {e.1.1,e.1.2} a b i).val) ↔
      ∃ s : {s : Fin M // s ∉ ({e.1.1,e.1.2} : Finset (Fin M))},
        T*candidateQuotient e ≤ (candidateSiteValue e s.val).natAbs ∧
        PrimeProductAvailable (candidateSiteValue e s.val).natAbs (b s).val := by
  constructor
  · rintro ⟨s,hi,hk,hlarge,havail⟩
    have hs : s ∉ ({e.1.1,e.1.2} : Finset (Fin M)) := by simp only [mem_insert,mem_singleton]; tauto
    refine ⟨⟨s,hs⟩,hlarge,?_⟩
    simpa only [mergeSitePartition,dite_eq_right hs] using havail
  · rintro ⟨s,hlarge,havail⟩
    have hs : s.val ≠ e.1.1 ∧ s.val ≠ e.1.2 := by simpa only [mem_insert,mem_singleton,not_or] using s.property
    refine ⟨s.val,hs.1,hs.2,hlarge,?_⟩
    simpa only [mergeSitePartition,dite_eq_right s.property] using havail

open Classical in
/-- Exposing the two endpoints leaves the third-site witness bounded by
M/(T c), even though its prescribed coefficients depend on those endpoints. -/
theorem repeatWitness_remaining_probability {B L T H M : ℕ} {τ C : ℝ}
    (hT : 0 < T) {e : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e)
    (a : ({e.1.1,e.1.2} : Finset (Fin M)) → (auxiliaryPrimes B).powerset) :
    finiteProbability
      (siteProductMass (fun _ : {s : Fin M // s ∉ ({e.1.1,e.1.2} : Finset (Fin M))} =>
        independentPrimeSetMass B))
      (fun b => CandidateRepeatWitness T e
        (fun i => (mergeSitePartition {e.1.1,e.1.2} a b i).val)) ≤
      (M : ℝ)/((T : ℝ)*Real.exp B) := by
  let I : Finset (Fin M) := {e.1.1,e.1.2}
  have hN : 0 < T*candidateQuotient e := Nat.mul_pos hT he.2.2.2.1
  have hq : (0 : ℝ) < (T : ℝ)*candidateQuotient e := by exact_mod_cast hN
  have hbig : (T : ℝ)*Real.exp B ≤ (T : ℝ)*candidateQuotient e :=
    mul_le_mul_of_nonneg_left (candidate_quotient_exp_bounds he).1 (Nat.cast_nonneg T)
  have hevent : (fun b => CandidateRepeatWitness T e (fun i => (mergeSitePartition I a b i).val)) =
      (fun b => ∃ s : {s : Fin M // s ∉ I},
        T*candidateQuotient e ≤ (candidateSiteValue e s.val).natAbs ∧
        PrimeProductAvailable (candidateSiteValue e s.val).natAbs (b s).val) := by
    funext b
    exact propext (repeatWitness_merge_iff e a b)
  rw [hevent]
  calc
    _ ≤ (Fintype.card {s : Fin M // s ∉ I} : ℝ)/(T*candidateQuotient e : ℕ) :=
      independent_large_coefficients_probability (ι := {s : Fin M // s ∉ I})
        B (T*candidateQuotient e) hN (fun s => (candidateSiteValue e s.val).natAbs)
    _ ≤ (M : ℝ)/((T : ℝ)*candidateQuotient e) := by
      push_cast
      apply div_le_div_of_nonneg_right _ hq.le
      exact_mod_cast (show Fintype.card {s : Fin M // s ∉ I} ≤ M from by
        simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun s : Fin M => s ∉ I))
    _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg M) (by positivity) hbig

end JointDickman

end OAI
