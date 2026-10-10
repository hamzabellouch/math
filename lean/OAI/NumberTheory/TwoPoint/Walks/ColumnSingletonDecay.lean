import OAI.NumberTheory.TwoPoint.Walks.ProhibitedNumericalSingletonDecay
import OAI.NumberTheory.TwoPoint.Bounds.TraceCatalogMaps

namespace OAI

/-! The singleton estimate on the column/padding catalog used by the good
forest estimate.  Prime factorization proves that the encoding is injective. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_prohibited_column_singleton_decay (Cs Cw : ℝ)
    (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (h J M R B s n D K H Y : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ)
      (forward : Fin R → Bool)
      (F : Finset (ColumnPrimeAssignment J R P × (Fin R → Q)))
      (label : (ColumnPrimeAssignment J R P × (Fin R → Q)) →
        Fin R × Fin J → ↥(data.P ∪ data.Q))
      (_base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (ColumnPrimeAssignment J R P × (Fin R → Q)) →
        (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : (ColumnPrimeAssignment J R P × (Fin R → Q)) → ℝ) (A : ℝ),
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      0 ≤ A → (∀ w ∈ F, 0 ≤ cap w) →
      (∀ w ∈ F, ∀ x, 0 ≤ weight w x) → (∀ w ∈ F, ∀ x, weight w x ≤ cap w) →
      (∀ w ∈ F, cap w * 2 ^ (R * J + (singletonLabels (label w)).card) ≤ A) →
      (∀ w ∈ F, ∀ x y, (∀ i, i ∉ univ.image (label w) → x i = y i) → weight w x = weight w y) →
      (∀ w ∈ F, ∀ x, weight w x ≠ 0 → MainPaddingTests Subtype.val h B
        (columnTupleWord w.1 forward (fun i => (w.2 i).val)) x) →
      (∀ w ∈ F, ∀ i, (columnTuple w.1 i, (w.2 i).val) ∈ data.pairs) →
      (∀ w ∈ F, ∀ i j, (label w (i, j)).val = (w.1 j i).val) →
      R + n * s ≤ D → (∀ w ∈ F, n * (s * J) < (singletonLabels (label w)).card) →
      (D : ℝ) ≤ 4 * L → ((J + M : ℕ) : ℝ) ≤ Cs * Real.log L →
      0 < n → (n : ℝ) ≤ 4 * L → 8 * K ≤ n →
      L ^ (1 / 12 : ℝ) / 32 ≤ (K : ℝ) → (K : ℝ) ≤ L →
      1 ≤ primeHarmonicMass data.P →
      primeHarmonicMass data.P ≤ L ^ (2 : ℕ) → primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) →
      1 ≤ Y → (Y : ℝ) ≤ Real.exp L →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H → A ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∑ w ∈ F, |prohibitedCenteredAverage data hB s D
        (columnTupleWord w.1 forward (fun i => (w.2 i).val)) (label w) (weight w)|) ≤
        Real.exp (-L ^ (21 / 20 : ℝ)) := by
  filter_upwards [eventually_prohibited_numerical_singleton_decay Cs Cw hCs hCw] with L hdecay
  intro h J M R B s n D K H Y data hB P Q forward F label base weight cap A hprime hdisjoint
    hA hcap hweight hwcap hcost hdep hpadding hpairs hlabel hD hn hDL hJM hnpos hnL hKn
    hKlo hKhi hmass hPmass hQmass hYpos hYexp hlo hhi hH hAexp
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
    have hb := hdecay h J M R B s n D K H Y data hB E (fun w => label (decode w)) base
      (fun w => weight (decode w)) (fun w => cap (decode w)) A hA
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hcap v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hweight v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hwcap v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hcost v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hdep v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode, encode, columnStepCode_word] using hpadding v hv)
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
      hD
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hn v hv)
      hDL hJM hnpos hnL hKn hKlo hKhi hmass hPmass hQmass hYpos hYexp hlo hhi hH hAexp
    rw [show E = F.image encode from rfl, sum_image (fun _ _ _ _ he => hinj he)] at hb
    simpa only [hdecode, encode, columnStepCode_word] using hb
  · rw [not_nonempty_iff_eq_empty.mp hF, sum_empty]
    exact (Real.exp_pos _).le

end TwoPointCorrelations

end OAI
