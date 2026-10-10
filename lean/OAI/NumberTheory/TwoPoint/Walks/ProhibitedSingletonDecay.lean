import OAI.NumberTheory.TwoPoint.Walks.ProhibitedTraceTerms
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedSingletonCatalog
import OAI.NumberTheory.TwoPoint.Bounds.BoundedWitnessDecay
import OAI.NumberTheory.TwoPoint.Walks.WitnessRecordBudget

namespace OAI

/-! Full singleton decay for the original divisibility-centered word and literal vertex deletion. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem eventually_prohibited_singleton_decay (Cs Cw : ℝ) (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (h J M R B s n D K H Y : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (F : Finset (List SignedStep))
      (label : List SignedStep → Fin R × Fin J → ↥(data.P ∪ data.Q))
      (_base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : List SignedStep → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : List SignedStep → ℝ) (A : ℝ),
      0 ≤ A →
      (∀ main ∈ F, 0 ≤ cap main) →
      (∀ main ∈ F, ∀ x, 0 ≤ weight main x) →
      (∀ main ∈ F, ∀ x, weight main x ≤ cap main) →
      (∀ main ∈ F, cap main * 2 ^ (R * J + (singletonLabels (label main)).card) ≤ A) →
      (∀ main ∈ F, ∀ x y, (∀ i, i ∉ univ.image (label main) → x i = y i) →
        weight main x = weight main y) →
      (∀ main ∈ F, ∀ x, weight main x ≠ 0 → MainPaddingTests
        (fun p : ↥(data.P ∪ data.Q) => p.val) h B main x) →
      (∀ main ∈ F, ∀ i ∈ univ.image (label main), i.val ∈ wordDivisorPrimeSupport main) →
      (∀ main ∈ F, ∀ i ∈ univ.image (label main), i.val ∈ data.P) →
      (∀ main ∈ F, ∀ t ∈ main, (t.tuple, t.padding) ∈ data.pairs) →
      (∀ main ∈ F, ∀ (k : Fin main.length) (i : ↥(data.P ∪ data.Q)),
        i.val ∈ (main.get k).tuple.primeFactors → i ∈ univ.image (label main)) →
      (∀ main ∈ F, ∀ i : singletonLabels (label main), ∀ v,
        TuplePrimeAt main i.val v → v = (singletonRepresentative (label main) i).1.val) →
      (∀ main ∈ F, main.length + n * s ≤ D) →
      (∀ main ∈ F, n * (s * J) < (singletonLabels (label main)).card) →
      (D : ℝ) ≤ 4 * L → ((J + M : ℕ) : ℝ) ≤ Cs * Real.log L →
      0 < n → (n : ℝ) ≤ 4 * L → 8 * K ≤ n →
      L ^ (1 / 12 : ℝ) / 32 ≤ (K : ℝ) → (K : ℝ) ≤ L →
      1 ≤ primeHarmonicMass data.P →
      primeHarmonicMass data.P ≤ L ^ (2 : ℕ) → primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) →
      1 ≤ Y → (Y : ℝ) ≤ Real.exp L →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      A ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∑ main ∈ F, |prohibitedCenteredAverage data hB s D main (label main) (weight main)|) ≤
        Real.exp (-L ^ (21 / 20 : ℝ)) := by
  filter_upwards [eventually_bounded_witness_decay Cs Cw hCs hCw,
    eventually_witnessRecordBudget Cs hCs] with L hdecay hbudgetScale
  intro h J M R B s n D K H Y data hB F label base weight cap A hA hcap hw hwcap hcost
    hdep hpadding hseen hlabelP hpairs hcover hposition hD hn hDL hJM
    hnpos hnL hKn hKlo hKhi hmass hPmass hQmass hYpos hYexp hlo hhi hH hAexp
  let N := witnessRecordBudget D J M n
  have hbudget := hbudgetScale D J M n hDL hJM hnL
  have hDN : D ≤ N := by dsimp [N, witnessRecordBudget]; omega
  have hnN : n ≤ N := by dsimp [N, witnessRecordBudget]; omega
  have hslotsN (r : ℕ) (hr : r ≤ D) : r * (J + M) ≤ N :=
    witnessRecordBudget_slots D J M n r hr
  have hslots (r : ℕ) (_hr : r ≤ D) : ((r * (J + M) : ℕ) : ℝ) ≤ Cs * r * Real.log L := by
    have he := mul_le_mul_of_nonneg_left hJM (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    push_cast at he ⊢
    nlinarith
  have hmasked (main : List SignedStep) (hm : main ∈ F) (x : ↥(data.P ∪ data.Q) → Fin B) :
      paddingWeightedFunction (fun p : ↥(data.P ∪ data.Q) => p.val) h B main (weight main) x =
        weight main x := by
    by_cases hx : weight main x = 0
    · simp [paddingWeightedFunction, hx]
    · simp [paddingWeightedFunction, hpadding main hm x hx]
  have hc := prohibited_singleton_words_le_catalog data B s n D F label
    (fun main => tupleForcedTarget data hB main (label main)) base weight cap A hA hB
    (fun main _ t => forcedResidue_lt B (label main t).val (data.prime _).pos
      (hB _ (label main t).property) (wordDisplacement h (main.take t.1.val)))
    hw hwcap hcap (by simpa only [Fintype.card_prod, Fintype.card_fin] using hcost)
    hdep hseen hlabelP hpairs hcover (fun main i => (singletonRepresentative (label main) i).1.val)
    hposition hD hn
  have hslotpoly (r : ℕ) (hr : r ≤ D) : ((r * (J + M) : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) := by
    have he : ((r * (J + M) : ℕ) : ℝ) + 1 ≤ (N : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right (hslotsN r hr) 1
    exact he.trans hbudget
  have hDpoly : (D : ℝ) + 1 ≤ L ^ (2 : ℕ) := by
    have he : (D : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hDN 1
    exact he.trans hbudget
  have hb := hdecay D n K N h s J H Y (fun r => r * (J + M)) data.P data.Q
    (fun d q => (d, q) ∈ data.pairs) A hDL hDN hslots hslotpoly hDpoly
    (fun r hr => (hslotsN r hr).trans (Nat.le_succ _)) hnpos
    (hnN.trans (Nat.le_succ _)) hnL hbudget hKn hKlo hKhi data.primeP hmass hPmass hQmass
    hYpos hYexp hlo hhi hH hA hAexp
  have hleft : (∑ main ∈ F, |prohibitedCenteredAverage data hB s D main (label main) (weight main)|) =
      ∑ main ∈ F, |(data.residueLaw B hB).average (fun x =>
        paddingWeightedFunction (fun p : ↥(data.P ∪ data.Q) => p.val) h B main (weight main) x *
        (∏ t, ((if x (label main t) = tupleForcedTarget data hB main (label main) t
          then (1 : ℝ) else 0) - ((label main t).val : ℝ)⁻¹)) *
        attachedCatalogAvoidance data s B D main x)| := by
    apply sum_congr rfl
    intro main hm
    unfold prohibitedCenteredAverage
    simp_rw [hmasked main hm]
    congr 1
    exact uniform_weighted_divisor_word_average B _ (fun p => (data.prime p).pos)
      (fun p => hB _ p.property) (label main)
      (fun t => wordDisplacement h (main.take t.1.val)) (weight main)
      (attachedCatalogAvoidance data s B D main)
  rw [hleft]
  apply hc.trans
  convert hb using 1
  simp only [mul_sum]

end TwoPointCorrelations

end OAI
