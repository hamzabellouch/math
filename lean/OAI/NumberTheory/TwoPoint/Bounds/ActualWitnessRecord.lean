import OAI.NumberTheory.TwoPoint.Walks.AttachedWitnessCatalog
import OAI.NumberTheory.TwoPoint.Bounds.NumericalWitnessEncoding

namespace OAI

/-! Encode an actual attached witness family without adding any numerical choices. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem actual_witness_has_encoded_record {n : ℕ} {ι : Type*}
    (main : List SignedStep) (word : Fin n → List SignedStep)
    (attachment : Fin n → ℕ) (hatt : ∀ i, attachment i ≤ main.length)
    (P Q : Finset ℕ) (T h s J : ℕ) (supply : ℕ → ℕ → Prop) (p : ι → ℕ)
    (hnum : NumericalWitnessEvent main word p h s J supply)
    (hT : Fintype.card (ActualPrimeSlot (recordedWitnessWord main word).get) ≤ T)
    (ht : ∀ t ∈ recordedWitnessWord main word, Squarefree t.tuple)
    (hq : ∀ t ∈ recordedWitnessWord main word, Squarefree t.padding)
    (hP : ∀ t ∈ recordedWitnessWord main word, t.tuple.primeFactors ⊆ P)
    (hQ : ∀ t ∈ recordedWitnessWord main word, t.padding.primeFactors ⊆ Q)
    (hd : ∀ t ∈ recordedWitnessWord main word, ∀ u ∈ recordedWitnessWord main word,
      Disjoint t.tuple.primeFactors u.padding.primeFactors)
    (hprime : ∀ p ∈ P, p.Prime) :
    ∃ d : WitnessRecord n (recordedWitnessWord main word).length,
      ∃ e : PrimeWordEncoding (recordedWitnessWord main word).length T P Q,
        e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
          h s J supply ∧
        e.decode = recordedWitnessWord main word ∧
        e.decode.take d.1.1.val = main ∧
        (∀ i, (e.decode.drop (d.1.2.1 i).val).take (d.1.2.2 i).val = word i) ∧
        (∀ i, (d.2 i).val = attachment i) ∧
        e.weight = ∏ q ∈ wordDivisorPrimeSupport e.decode, (q : ℝ)⁻¹ := by
  let v := recordedWitnessWord main word
  obtain ⟨d, hdmain, hdword, hdatt⟩ := recorded_witness_record main word attachment hatt
  have hnum' : NumericalWitnessEvent ((List.ofFn v.get).take d.1.1.val)
      (fun i => ((List.ofFn v.get).drop (d.1.2.1 i).val).take (d.1.2.2 i).val)
      p h s J supply := by
    simpa only [List.ofFn_get, v, hdmain, hdword] using hnum
  obtain ⟨e, he, hdecode, hweight⟩ := PrimeWordEncoding.covers_witnesses v.get hT
    (fun i => ht _ (List.get_mem v i)) (fun i => hq _ (List.get_mem v i))
    (fun i => hP _ (List.get_mem v i)) (fun i => hQ _ (List.get_mem v i))
    (fun i j => hd _ (List.get_mem v i) _ (List.get_mem v j)) hprime
    d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
    h s J supply p hnum'
  rw [List.ofFn_get] at hdecode hweight
  refine ⟨d, e, he, hdecode, ?_, ?_, hdatt, ?_⟩
  · simpa only [hdecode] using hdmain
  · intro i
    simpa only [hdecode] using hdword i
  · simpa only [hdecode] using hweight

end TwoPointCorrelations

end OAI
