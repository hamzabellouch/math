import OAI.NumberTheory.TwoPoint.Bounds.ShiftedIntegerPaths
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedWeightIndependence

namespace OAI

/-! The literal masked arithmetic weights depend only on the finite prime residues. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma centeredTuple_eq_of_prime_residues (P : Finset ℕ) (n m : ℤ)
    (hnm : ∀ p ∈ P, (n : ZMod p) = (m : ZMod p)) :
    centeredTuple P n = centeredTuple P m := by
  unfold centeredTuple
  apply prod_congr rfl
  intro p hp
  have he : (p : ℤ) ∣ n ↔ (p : ℤ) ∣ m := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hnm p hp]
  simp only [he]

lemma ProhibitedPrimeFamily.prohibitedSite_congr {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s : ℕ) (n m : ℤ)
    (hnm : ∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) :
    ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n ↔
      ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) m := by
  let (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩
  let x (p : ↥(data.P ∪ data.Q)) : Fin B :=
    ⟨(n : ZMod p.val).val, (ZMod.val_lt _).trans_le (hB _ p.property)⟩
  have hn (p : ↥(data.P ∪ data.Q)) : (n : ZMod p.val) = ((x p).val : ZMod p.val) :=
    (ZMod.natCast_zmod_val _).symm
  exact (data.deletedEvent_iff s B x n hn).symm.trans
    (data.deletedEvent_iff s B x m (fun p => (hnm p).symm.trans (hn p)))

lemma maskedSignedIntegerWeight_residue_congr {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s : ℕ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ data.Q)
    (hg : ∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ d n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
      (extra d n ↔ extra d m))
    (t : SignedStep) (htuple : t.tuple.primeFactors ⊆ data.P) (n m : ℤ)
    (hnm : ∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) :
    maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
      L K extra h (fun z => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) z) t n =
    maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
      L K extra h (fun z => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) z) t m := by
  have hQ : ∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p) :=
    fun p hp => hnm ⟨p, mem_union_right _ hp⟩
  have hshift : ∀ p : ↥(data.P ∪ data.Q),
      ((n + t.displacement h : ℤ) : ZMod p.val) =
        ((m + t.displacement h : ℤ) : ZMod p.val) := by
    intro p
    simp only [Int.cast_add, hnm p]
  have hkeep (a b : ℤ) (hab : ∀ p ∈ data.Q, (a : ZMod p) = (b : ZMod p)) :
      integerEdgeKeep Q u (eligible t.tuple) g L K (extra t.tuple) a ↔
        integerEdgeKeep Q u (eligible t.tuple) g L K (extra t.tuple) b := by
    unfold integerEdgeKeep
    rw [paddingDensity_eq_of_prime_residues data.Q Q u (eligible t.tuple) g hsq hpool a b hab
      (hg a b hab), hextra t.tuple a b hab]
  have hcenter : centeredTuple t.tuple.primeFactors n = centeredTuple t.tuple.primeFactors m :=
    centeredTuple_eq_of_prime_residues _ n m
      (fun p hp => hnm ⟨p, mem_union_left _ (htuple hp)⟩)
  have hperiod : ∀ q ∈ Q, ∀ z,
      centeredTuple t.tuple.primeFactors (z + (h * q * t.tuple : ℕ)) =
        centeredTuple t.tuple.primeFactors z :=
    fun q _ z => centeredTuple_padding_periodic _ h t.tuple
      (fun p hp => (Nat.mem_primeFactors.mp hp).2.1) q z
  have hedge : signedIntegerWeight Q u (eligible t.tuple) g (centeredTuple t.tuple.primeFactors)
      L K (extra t.tuple) h t n =
      signedIntegerWeight Q u (eligible t.tuple) g (centeredTuple t.tuple.primeFactors)
        L K (extra t.tuple) h t m := by
    rw [signedIntegerWeight_departure Q u _ g _ L K _ h t n hperiod,
      signedIntegerWeight_departure Q u _ g _ L K _ h t m hperiod]
    by_cases hq : t.padding ∈ Q
    · have hd := squarefree_divisor_congr data.Q t.padding (hsq _ hq) (hpool _ hq) n m hQ
      have hQs : ∀ p ∈ data.Q,
          ((n + t.displacement h : ℤ) : ZMod p) =
            ((m + t.displacement h : ℤ) : ZMod p) :=
        fun p hp => hshift ⟨p, mem_union_right _ hp⟩
      simp only [hq, true_and, hd, hkeep n m hQ, hkeep _ _ hQs, hcenter,
        hg n m hQ, hg _ _ hQs]
    · simp only [hq, false_and, ite_false]
  dsimp only [maskedSignedIntegerWeight, vertexIndicator]
  simp only [data.prohibitedSite_congr hB s n m hnm,
    data.prohibitedSite_congr hB s _ _ hshift, hedge]
  split_ifs <;> rfl

lemma scalarWalkProduct_residue_congr (P : Finset ℕ) (h : ℕ)
    (weight : SignedStep → ℤ → ℝ) (w : List SignedStep)
    (hw : ∀ t ∈ w, ∀ n m : ℤ, (∀ p ∈ P, (n : ZMod p) = (m : ZMod p)) →
      weight t n = weight t m) (n m : ℤ)
    (hnm : ∀ p ∈ P, (n : ZMod p) = (m : ZMod p)) :
    scalarWalkProduct h weight n w = scalarWalkProduct h weight m w := by
  induction w generalizing n m with
  | nil => rfl
  | cons t w ih =>
      rw [scalarWalkProduct, scalarWalkProduct, hw t (List.mem_cons_self ..) n m hnm,
        ih (fun a ha => hw a (List.mem_cons_of_mem t ha))]
      intro p hp
      simp only [Int.cast_add, hnm p hp]

end TwoPointCorrelations

end OAI
