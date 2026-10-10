import OAI.NumberTheory.TwoPoint.Walks.ProhibitedManyUnlitDecay
import OAI.NumberTheory.TwoPoint.Bounds.TraceCatalogMaps

namespace OAI

/-! The complete many-unlit sum on the same column/padding catalog as the
good and high-rank classes. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_prohibited_column_many_unlit_decay (C Ce Cs : ℝ)
    (hC : 0 ≤ C) (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) :
    ∀ᶠ L : ℝ in atTop, ∀ (R J M S B h s D : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ) (forward : Fin R → Bool)
      (F : Finset (ColumnPrimeAssignment J R P × (Fin R → Q)))
      (label : (ColumnPrimeAssignment J R P × (Fin R → Q)) →
        Fin R × Fin J → ↥(data.P ∪ data.Q))
      (base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (ColumnPrimeAssignment J R P × (Fin R → Q)) →
        (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : (ColumnPrimeAssignment J R P × (Fin R → Q)) → ℝ) (external H : ℝ),
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      1 ≤ R → (R : ℝ) ≤ 2 * L →
      ((S + R * J : ℕ) : ℝ) ≤ Cs * L * Real.log L →
      ((J + M : ℕ) : ℝ) ≤ C * Real.log L →
      ((R * (J + M) : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      0 ≤ external → external ≤ Real.exp (Ce * L) →
      primeHarmonicMass data.P ≤ L ^ (2 : ℕ) → primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) →
      (M : ℝ) ≤ 100 * Real.log L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∀ p ∈ data.P, H ≤ p) →
      (∀ w ∈ F, ∀ i, (columnTuple w.1 i, (w.2 i).val) ∈ data.pairs) →
      (∀ w ∈ F, ∀ i j, (label w (i, j)).val = (w.1 j i).val) →
      (∀ w ∈ F, 0 ≤ cap w) →
      (∀ w ∈ F, ∀ x, 0 ≤ weight w x) →
      (∀ w ∈ F, ∀ x, weight w x ≤ cap w) →
      (∀ w ∈ F, ∀ x, weight w x ≠ 0 → MainPaddingTests Subtype.val h B
        (columnTupleWord w.1 forward (fun i => (w.2 i).val)) x) →
      (∀ w ∈ F, cap w * 2 ^ (singletonLabels (label w)).card ≤
        crudeTraceWeight R S (fun i => (w.2 i).val) L external) →
      (∑ w ∈ F, ∑ U ∈ (nonsingletonSlots (label w)).powerset.filter
        (fun U => ⌊L ^ (1 / 50 : ℝ)⌋₊ < U.card),
        prohibitedDesignatedTerm data hB s D
          (columnTupleWord w.1 forward (fun i => (w.2 i).val)) (label w) base (weight w) U) ≤
        Real.exp (-L ^ (101 / 100 : ℝ)) := by
  filter_upwards [eventually_prohibited_many_unlit_decay C Ce Cs hC hCe hCs,
    eventually_ge_atTop (0 : ℝ)] with L hdecay hL
  intro R J M S B h s D data hB P Q forward F label base weight cap external H
    hprime hdisjoint hR hRL hS hJM hT hRp hext hextL hPmass hQmass hM hH hlo
    hpairs hlabel hcap hweight hwcap hpadding hcost
  by_cases hF : F.Nonempty
  · have : Nonempty (ColumnPrimeAssignment J R P × (Fin R → Q)) := ⟨hF.choose⟩
    let encode := columnStepCode (P := P) (Q := Q) forward
    have hinj : Function.Injective encode := columnStepCode_injective forward hprime hdisjoint
    let decode := Function.invFun encode
    have hdecode (w : ColumnPrimeAssignment J R P × (Fin R → Q)) : decode (encode w) = w :=
      Function.leftInverse_invFun hinj w
    let E := F.image encode
    have hpull (w : Fin R → SignedStep) (hw : w ∈ E) : ∃ v ∈ F, w = encode v := by
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      exact ⟨v, hv, rfl⟩
    have hb := hdecay R J M S B h s D data hB E (fun w => label (decode w)) base
      (fun w => weight (decode w)) (fun w => cap (decode w)) external H
      hR hRL hS hJM hT hRp hext hextL hPmass hQmass hM hH hlo
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; exact hpairs v hv)
      (by
        intro w hw
        obtain ⟨v,hv,rfl⟩ := hpull w hw
        intro i
        change (columnTuple v.1 i).primeFactors = univ.image (fun j => (label (decode (encode v)) (i,j)).val)
        rw [hdecode, columnTuple_primeFactors v.1 i hprime hdisjoint]
        congr 1
        funext j
        exact (hlabel v hv i j).symm)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hcap v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hweight v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hwcap v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode, encode, columnStepCode_word] using hpadding v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw
          simpa only [hdecode, encode, columnStepCode] using hcost v hv)
    rw [largeUnlitCatalog_sum E (fun w => label (decode w)) L hL
      (fun w U => prohibitedDesignatedTerm data hB s D (List.ofFn w)
        (label (decode w)) base (weight (decode w)) U)] at hb
    rw [show E = F.image encode from rfl, sum_image (fun _ _ _ _ he => hinj he)] at hb
    simpa only [hdecode, encode, columnStepCode_word] using hb
  · rw [not_nonempty_iff_eq_empty.mp hF, sum_empty]
    exact (Real.exp_pos _).le

end TwoPointCorrelations

end OAI
