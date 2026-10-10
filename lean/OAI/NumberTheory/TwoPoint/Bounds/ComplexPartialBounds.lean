import OAI.NumberTheory.TwoPoint.Bounds.ComplexPartialProfiles
import OAI.NumberTheory.TwoPoint.Bounds.QuantitativeTupleBins
import OAI.NumberTheory.TwoPoint.Bounds.WeightedShiftAverage

namespace OAI

/-! Exact reciprocal normalization of the complex partial-tuple profiles. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma complexRoughProfile_average (F G : ℕ → ℂ) (Z : Finset ℕ) (h Y : ℕ) :
    positivePrefix (complexRoughProfile F G Z h) Y / (Y : ℂ) =
      weightedRoughShiftAverage F G Z (fun _ => 1) h Y := by
  have he : complexRoughProfile F G Z h = weightedRoughShiftProfile F G Z (fun _ => 1) h := by
    funext n
    simp only [weightedRoughShiftProfile, complexRoughProfile, one_div]
  rw [weightedRoughShiftAverage, he]

lemma complex_partial_tuple_prefix_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i j, j ≠ i → Disjoint (P i) (P j))
    (I : Finset (Fin J)) (q : ℕ) (hq : 0 < q)
    (eligible : ℕ → ℕ → Prop) (F G : ℕ → ℂ) (h X : ℕ)
    (hX : 0 < X) (E : ℝ) (hE : 0 ≤ E)
    (hb : ∀ y : (j : {j // j ∉ I}) → P j,
      ‖weightedRoughShiftAverage
        (fun n => F ((q * ∏ j, (y j).val) * n))
        (fun n => G ((q * ∏ j, (y j).val) * n))
        ((primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q))
        (fun _ => 1) h (X / (q * ∏ j, (y j).val))‖ ≤ E) :
    ‖positivePrefix (tupleComplexPartialProfile P I q eligible F G h) X / (X : ℂ)‖ ≤
      E * ((1 / (q : ℝ)) * ∏ j : {j // j ∉ I}, primeHarmonicMass (P j)) := by
  rw [tupleComplexPartialProfile_prefix P hprime hdisjoint I q hq]
  have he := indexed_rescaled_prefix_bound
    (fun y : (j : {j // j ∉ I}) → P j => q * ∏ j, (y j).val)
    (fun y => complexRoughProfile
      (fun n => F ((q * ∏ j, (y j).val) * n))
      (fun n => G ((q * ∏ j, (y j).val) * n))
      ((primeTupleSlice P I).filter (fun z => eligible ((∏ j, (y j).val) * z) q)) h)
    X E hX hE
    (fun y => Nat.mul_pos hq (prod_pos fun j _ => (hprime j _ (y j).property).pos))
    (fun y => by rw [complexRoughProfile_average]; exact hb y)
  simpa only [Nat.cast_mul, Nat.cast_prod, retained_tuple_reciprocal_sum] using he

end TwoPointCorrelations

end OAI
