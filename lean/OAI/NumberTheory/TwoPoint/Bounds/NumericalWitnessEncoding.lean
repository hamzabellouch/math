import OAI.NumberTheory.TwoPoint.Walks.WitnessRelabel
import OAI.NumberTheory.TwoPoint.Bounds.EncodedWitnessSum

namespace OAI

/-! Actual numerical witness families are covered by the prime-slot catalog. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma LabeledPrimeWord.realizes_support_covered {ι : Type*} [DecidableEq ι]
    (w : LabeledPrimeWord ι) (value : ι → ℕ) (hw : w.Realizes value)
    (hprime : ∀ i, (value i).Prime) (r : ℕ) (hr : r ∈ wordPrimeSupport w.word) :
    ∃ i, value i = r := by
  obtain ⟨t, ht, hr⟩ := (mem_wordPrimeSupport r w.word).mp hr
  obtain ⟨k, hk⟩ := List.get_of_mem ht
  have hpr := (Nat.mem_primeFactors.mp hr).1
  have hdvd := (Nat.mem_primeFactors.mp hr).2.1
  have htup : (∏ i ∈ w.labels k, value i) = t.tuple := (hw k).trans (congrArg SignedStep.tuple hk)
  rw [← htup] at hdvd
  obtain ⟨i, _, hi⟩ := (hpr.prime.dvd_finsetProd_iff value).mp hdvd
  exact ⟨i, ((Nat.prime_dvd_prime_iff_eq hpr (hprime i)).mp hi).symm⟩

lemma wordPrimeSupport_mono {v w : List SignedStep}
    (hvw : ∀ t ∈ v, t ∈ w) : wordPrimeSupport v ⊆ wordPrimeSupport w := by
  intro p hp
  obtain ⟨t, ht, hpt⟩ := (mem_wordPrimeSupport p v).mp hp
  exact (mem_wordPrimeSupport p w).mpr ⟨t, hvw t ht, hpt⟩

lemma PrimeWordEncoding.tuple_support_covered {R T : ℕ} {P Q : Finset ℕ}
    (e : PrimeWordEncoding R T P Q) (hc : e.2.1.KindConsistent)
    (hi : e.2.1.RowInjective) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ) (hr : r ∈ wordPrimeSupport e.decode) :
    ∃ z, (e.2.2.1 z).val = r := by
  let a := fun z => (e.2.2.1 z).val
  let b := fun z => (e.2.2.2 z).val
  have he := e.2.1.labeledWord_resample hc hi a b
  apply ((e.2.1.labeledWord b).resample a).realizes_support_covered a
    ((e.2.1.labeledWord b).resample_realizes a) (fun z => hP _ (e.2.2.1 z).property) r
  rw [he]
  exact hr

theorem PrimeWordEncoding.covers_witnesses {R T n : ℕ} {P Q : Finset ℕ}
    (w : Fin R → SignedStep)
    (hT : Fintype.card (ActualPrimeSlot w) ≤ T)
    (ht : ∀ i, Squarefree (w i).tuple) (hq : ∀ i, Squarefree (w i).padding)
    (hP : ∀ i, (w i).tuple.primeFactors ⊆ P)
    (hQ : ∀ i, (w i).padding.primeFactors ⊆ Q)
    (hd : ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors)
    (hprime : ∀ p ∈ P, p.Prime)
    (mainLength : ℕ) (start len : Fin n → ℕ) (h s J : ℕ) (supply : ℕ → ℕ → Prop)
    {ι : Type*} (p : ι → ℕ)
    (hnum : NumericalWitnessEvent ((List.ofFn w).take mainLength)
      (fun i => ((List.ofFn w).drop (start i)).take (len i)) p h s J supply) :
    ∃ e : PrimeWordEncoding R T P Q, e.Witnesses n mainLength start len h s J supply ∧
      e.decode = List.ofFn w ∧
      e.weight = ∏ q ∈ wordDivisorPrimeSupport (List.ofFn w), (q : ℝ)⁻¹ := by
  obtain ⟨e, he, hc, hi, hinj, hweight⟩ := covers w hT ht hq hP hQ hd
  have hnum' : NumericalWitnessEvent (e.decode.take mainLength)
      (fun i => (e.decode.drop (start i)).take (len i)) p h s J supply := by
    simpa only [he] using hnum
  have hcover (i : Fin n) (r : ℕ)
      (hr : r ∈ wordPrimeSupport ((e.decode.drop (start i)).take (len i))) :
      ∃ z, (e.2.2.1 z).val = r := by
    apply e.tuple_support_covered hc hi hprime r
    apply wordPrimeSupport_mono (fun t ht => List.mem_of_mem_drop (List.mem_of_mem_take ht)) hr
  exact ⟨e, ⟨hc, hi, hnum'.relabel _ hinj (fun z => hprime _ (e.2.2.1 z).property) hcover⟩,
    he, hweight⟩

theorem numerical_witness_sum_le_encoding {R T n : ℕ} (P Q : Finset ℕ)
    (F : Finset (Fin R → SignedStep)) (mainLength : ℕ) (start len : Fin n → ℕ)
    (h s J : ℕ) (supply : ℕ → ℕ → Prop) {ι : Type*} (p : ι → ℕ)
    (hT : ∀ w ∈ F, Fintype.card (ActualPrimeSlot w) ≤ T)
    (ht : ∀ w ∈ F, ∀ i, Squarefree (w i).tuple)
    (hq : ∀ w ∈ F, ∀ i, Squarefree (w i).padding)
    (hP : ∀ w ∈ F, ∀ i, (w i).tuple.primeFactors ⊆ P)
    (hQ : ∀ w ∈ F, ∀ i, (w i).padding.primeFactors ⊆ Q)
    (hd : ∀ w ∈ F, ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors)
    (hprime : ∀ p ∈ P, p.Prime)
    (hnum : ∀ w ∈ F, NumericalWitnessEvent ((List.ofFn w).take mainLength)
      (fun i => ((List.ofFn w).drop (start i)).take (len i)) p h s J supply) :
    (∑ w ∈ F, ∏ q ∈ wordDivisorPrimeSupport (List.ofFn w), (q : ℝ)⁻¹) ≤
      ∑ e : PrimeWordEncoding R T P Q,
        if e.Witnesses n mainLength start len h s J supply then e.weight else 0 := by
  let V := F.image List.ofFn
  let weight (v : List SignedStep) : ℝ := ∏ q ∈ wordDivisorPrimeSupport v, (q : ℝ)⁻¹
  let cost (e : PrimeWordEncoding R T P Q) : ℝ :=
    if e.Witnesses n mainLength start len h s J supply then e.weight else 0
  have hsum : (∑ w ∈ F, weight (List.ofFn w)) = ∑ v ∈ V, weight v := by
    symm
    exact sum_image (fun _ _ _ _ he => List.ofFn_injective he)
  have hcost (e : PrimeWordEncoding R T P Q) : 0 ≤ cost e := by
    dsimp only [cost]
    split_ifs
    · exact e.weight_nonneg
    · exact le_rfl
  have hcover (v : List SignedStep) (hv : v ∈ V) :
      ∃ e : PrimeWordEncoding R T P Q, e.decode = v ∧ weight v ≤ cost e := by
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
    obtain ⟨e, he, hdecode, hweight⟩ := PrimeWordEncoding.covers_witnesses w (hT w hw)
      (ht w hw) (hq w hw) (hP w hw) (hQ w hw) (hd w hw) hprime
      mainLength start len h s J supply p (hnum w hw)
    refine ⟨e, hdecode, ?_⟩
    dsimp only [cost, weight]
    rw [ite_eq_left he, hweight]
  rw [show (∑ w ∈ F, ∏ q ∈ wordDivisorPrimeSupport (List.ofFn w), (q : ℝ)⁻¹) =
    ∑ v ∈ V, weight v from hsum]
  exact finite_decoding_weight_bound V PrimeWordEncoding.decode weight cost hcost hcover

end TwoPointCorrelations

end OAI
