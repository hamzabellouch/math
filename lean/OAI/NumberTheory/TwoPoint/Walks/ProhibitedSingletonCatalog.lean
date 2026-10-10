import OAI.NumberTheory.TwoPoint.Bounds.SingletonCenteredCatalog
import OAI.NumberTheory.TwoPoint.Walks.AttachedCatalogAvoidance
import OAI.NumberTheory.TwoPoint.Bounds.MainPaddingTests

namespace OAI

/-! Full singleton cancellation for the actual finite vertex-deletion catalog and padding weight. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem prohibited_singleton_words_le_catalog {h J M : ℕ} {τ : Type*} [Fintype τ]
    (data : ProhibitedPrimeFamily h J M) (B s n D : ℕ)
    (F : Finset (List SignedStep))
    (label : List SignedStep → τ → ↥(data.P ∪ data.Q))
    (target : List SignedStep → τ → Fin B) (base : ↥(data.P ∪ data.Q) → Fin B)
    (R : List SignedStep → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (C : List SignedStep → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (htarget : ∀ main ∈ F, ∀ t, (target main t).val < (label main t).val)
    (hR : ∀ main ∈ F, ∀ x, 0 ≤ R main x)
    (hRC : ∀ main ∈ F, ∀ x, R main x ≤ C main)
    (hC : ∀ main ∈ F, 0 ≤ C main)
    (hcost : ∀ main ∈ F,
      C main * 2 ^ (Fintype.card τ + (singletonLabels (label main)).card) ≤ A)
    (hRdep : ∀ main ∈ F, ∀ x y,
      (∀ i, i ∉ univ.image (label main) → x i = y i) → R main x = R main y)
    (hseen : ∀ main ∈ F, ∀ i ∈ univ.image (label main), i.val ∈ wordDivisorPrimeSupport main)
    (hlabelP : ∀ main ∈ F, ∀ i ∈ univ.image (label main), i.val ∈ data.P)
    (hmainpairs : ∀ main ∈ F, ∀ t ∈ main, (t.tuple, t.padding) ∈ data.pairs)
    (htupleCover : ∀ main ∈ F, ∀ (k : Fin main.length) (i : ↥(data.P ∪ data.Q)),
      i.val ∈ (main.get k).tuple.primeFactors → i ∈ univ.image (label main))
    (position : ∀ main, singletonLabels (label main) → ℕ)
    (hposition : ∀ main ∈ F, ∀ i : singletonLabels (label main), ∀ v,
      TuplePrimeAt main i.val v → v = position main i)
    (hD : ∀ main ∈ F, main.length + n * s ≤ D)
    (hn : ∀ main ∈ F, n * (s * J) < (singletonLabels (label main)).card) :
    (∑ main ∈ F,
      |(data.residueLaw B hB).average (fun x =>
        paddingWeightedFunction (fun p : ↥(data.P ∪ data.Q) => p.val) h B main (R main) x *
        (∏ t, ((if x (label main t) = target main t then (1 : ℝ) else 0) -
          ((label main t).val : ℝ)⁻¹)) * attachedCatalogAvoidance data s B D main x)|) ≤
      A * ∑ r : Fin (D + 1), ∑ d : WitnessRecord n r.val,
        ∑ e : PrimeWordEncoding r.val (r.val * (J + M)) data.P data.Q,
          if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val)
            (fun i => (d.1.2.2 i).val) h s J (fun d q => (d, q) ∈ data.pairs)
          then e.weight else 0 := by
  let p : ↥(data.P ∪ data.Q) → ℕ := Subtype.val
  let R' (main : List SignedStep) := paddingWeightedFunction p h B main (R main)
  let word (_main : List SignedStep) (a : Fin (D + 1) × ProhibitedCatalog data.pairs h s) :=
    decodeStepWord a.2.val
  let attachment (main : List SignedStep) (a : Fin (D + 1) × ProhibitedCatalog data.pairs h s) :=
    min a.1.val main.length
  have hsingle (main : List SignedStep) (hm : main ∈ F)
      (i : ↥(data.P ∪ data.Q)) (hi : i ∈ singletonLabels (label main)) : i.val ∈ data.P := by
    obtain ⟨t, ht⟩ := singleton_occurrence_exists (label main) ⟨i, hi⟩
    exact hlabelP main hm i (mem_image.mpr ⟨t, mem_univ _, ht⟩)
  apply singleton_centered_words_le_catalog p data.prime Subtype.val_injective B h s J n M D
    data.P data.Q (fun d q => (d, q) ∈ data.pairs) F label target base R' word attachment C A hA
    (fun i => hB i.val i.property) data.primeP data.primeQ data.disjoint
    (fun q hq => ⟨⟨q, hq⟩, rfl⟩) htarget
    (fun main hm => paddingWeightedFunction_nonneg p h B main (R main) (hR main hm))
    (fun main hm => paddingWeightedFunction_le p h B main (R main) (C main)
      (hC main hm) (hRC main hm)) hC hcost ?_ hseen
    (fun _ _ a => Nat.min_le_right a.1.val _) (fun _ _ a => a.2.property)
    (fun _ _ a => a.2.property.1.2.1)
    (fun _ _ a => data.catalog_whole_squarefree s a.2)
    (fun _ _ a => data.catalog_tuple_card s a.2)
    (fun _ _ a => data.catalog_prime_support s a.2)
    (fun main hm i hi a => data.catalog_padding_excluded s a.2 i.val (hsingle main hm i hi))
    (fun _ _ a q hq => ⟨⟨q, data.support_subset s a.2 hq⟩, rfl⟩)
    position hposition ?_ ?_ (fun _ _ a => data.catalog_admissible s a.2) hD hn
  · intro main hm x y hxy
    apply paddingWeightedFunction_invariant p (univ.image (label main)) h B main (R main)
      _ (hRdep main hm) x y hxy
    intro k i hi his
    have hq := data.padding_pool _ (hmainpairs main hm _ (List.get_mem main k)) hi
    exact disjoint_left.mp data.disjoint (hlabelP main hm i his) hq
  · intro main hm x hx
    exact paddingWeightedFunction_retained p (univ.image (label main)) h B main (R main) x
      (fun t ht => (data.padding_squarefree _ (hmainpairs main hm t ht)).ne_zero)
      (fun t ht => (data.tuple_squarefree _ (hmainpairs main hm t ht)).ne_zero)
      (htupleCover main hm) hx
  · intro main hm t ht
    have ht' := hmainpairs main hm t ht
    exact ⟨data.tuple_squarefree _ ht', data.padding_squarefree _ ht',
      (data.tuple_card _ ht').le, data.padding_card _ ht', data.tuple_pool _ ht',
      data.padding_pool _ ht'⟩

end TwoPointCorrelations

end OAI
