import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.CoveredCenter
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplingStateMachine

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
variable {n : ℕ}
noncomputable def assignmentWeight (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : State n) (u : Fin n) : ℚ :=
  (D.filter (fun p=>chosenId δ S Δ s p=u.val)).card
lemma assignmentWeight_cast [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (Δ : ℚ) (s : State n) (u : Fin n) :
    (assignmentWeight δ D S Δ s u:ℝ)=Completion.assignmentWeight D (Sampling.completionAssignment S (Δ:ℝ) s.real) u := by
  have he (p : Fin n) : chosenId δ S Δ s p=u.val ↔ Sampling.completionAssignment S (Δ:ℝ) s.real p=Completion.Virtual.real u := by
    rw [Sampling.completionAssignment_real_iff,chosenId_eq δ hδ]
    change tagId (Sampling.chosen S (Δ:ℝ) s.real p)=tagId (Sampling.realTag u) ↔ _
    exact tagId_injective.eq_iff
  simp only [assignmentWeight,Completion.assignmentWeight,he,Rat.cast_natCast]
end MetricKMedianRecovery.RationalSampling
namespace MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
noncomputable def identity (x : List Bool) : List Bool := discardPrefix (BinarySamplingOracle.reference x)
noncomputable def identity_computes : PolyComputes identity := BinarySamplingOracle.reference_computes.comp discardPrefix_computes
noncomputable def identities (x : List Bool) : List Bool := mapWith identity (pairBits (x,field 1 x))
noncomputable def identities_computes : PolyComputes identities := by
  have identitiesComputes := (id_computes.pair (field_computes 1)).comp (mapWith_computes identity_computes)
  unfold identities
  simpa only [Function.comp_def,id_eq] using identitiesComputes
lemma identities_pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) :
    identities (BinarySamplingOracle.pack δ D S Δ s)=encode ((D.sort (·≤·)).map (fun p=>(RationalSampling.chosenId δ S Δ s p).bits)) := by
  unfold identities
  rw [show field 1 (BinarySamplingOracle.pack δ D S Δ s)=BinaryFinSet.encode D by simp [BinarySamplingOracle.pack,field_encode]]
  simp only [BinaryFinSet.encode_eq,mapWith_encode,List.map_map,Function.comp_def,identity,BinarySamplingOracle.reference_pair,discardPrefix_pairBits]
noncomputable def count (x : List Bool) : List Bool := Count.run (filterWith WordEq.eq x)
noncomputable def count_computes : PolyComputes count := (filterWith_computes WordEq.eq_computes).comp Count.run_computes
lemma filter_card (D : Finset (Fin n)) (p : Fin n→Prop) [DecidablePred p] :
    ((D.sort (·≤·)).filter (fun i=>decide (p i))).length=(D.filter p).card := by
  rw [←List.toFinset_card_of_nodup ((Finset.sort_nodup D (·≤·)).filter _),List.toFinset_filter,Finset.sort_toFinset]
  simp only [decide_eq_true_eq]
lemma count_pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (u : Fin n) :
    count (pairBits (u.val.bits,identities (BinarySamplingOracle.pack δ D S Δ s)))=
      List.replicate (D.filter (fun p=>RationalSampling.chosenId δ S Δ s p=u.val)).card true := by
  rw [count,identities_pack,filterWith_encode]
  simp only [WordEq.eq_pair,List.filter_map,Function.comp_def,List.length_map,Count.run_encode]
  rw [filter_card]
  congr 2
  ext p
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro _
  constructor
  · intro h
    simpa only [value_bits] using (congrArg value h).symm
  · intro h
    exact (congrArg Nat.bits h).symm
noncomputable def run (x : List Bool) : List Bool := BinaryRational.encode ((count x).length:ℚ)
noncomputable def run_computes : PolyComputes run := by
  change PolyComputes (fun x=>BinaryRational.encode ((count x).length:ℚ))
  simpa only [Function.comp_apply,UnaryResources.lengthBits_eq,value_bits] using RatOps.nat (count_computes.comp UnaryResources.lengthBits_computes)
lemma run_pack (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (u : Fin n) :
    run (pairBits (u.val.bits,identities (BinarySamplingOracle.pack δ D S Δ s)))=
      BinaryRational.encode (RationalSampling.assignmentWeight δ D S Δ s u) := by
  simp only [run,count_pack,List.length_replicate,RationalSampling.assignmentWeight]
end MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight

end OAI
