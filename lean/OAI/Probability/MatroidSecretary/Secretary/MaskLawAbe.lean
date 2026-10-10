import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
# The source sacrificed-mask law for the secretary transport

The identities below concern the actual complete source seed.  They average
over the branch coin and all mask coordinates, including unused coordinates.
They do not assert a product law conditional on the complete secretary seed.
-/

namespace MatroidProphet

open MeasureTheory Finset

lemma secretary_main_rate :
    (1 / 2 : ℝ) + (1 - 1 / 2) * (1 / 4 + (1 - 1 / 4) * thinningRate) =
      5 / 8 + 3 * ((2 : ℝ) ^ 143)⁻¹ := by
  norm_num [thinningRate]

lemma secretary_main_rate_pos :
    0 < (5 / 8 : ℝ) + 3 * ((2 : ℝ) ^ 143)⁻¹ := by norm_num

lemma secretary_main_rate_lt_one :
    (5 / 8 : ℝ) + 3 * ((2 : ℝ) ^ 143)⁻¹ < 1 := by norm_num

/-- The union of the three sacrificed main-branch masks has precisely the
Bernoulli rate stated in the manuscript.  The test mask is not sacrificed. -/
theorem main_sacrificed_mask_expectation {α : Type*} [DecidableEq α]
    (V : Finset α) (f : Finset α → ℝ) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) V (fun H =>
      bitsExpectation (fun _ => (1 / 4 : ℝ)) V (fun D =>
        bitsExpectation (fun _ => thinningRate) V (fun C => f (H ∪ D ∪ C)))) =
      bitsExpectation (fun _ => (5 / 8 : ℝ) + 3 * ((2 : ℝ) ^ 143)⁻¹) V f := by
  have hinner (H : Finset α) := bitsExpectation_union
    (fun _ : α => (1 / 4 : ℝ)) (fun _ => thinningRate) V (fun S => f (H ∪ S))
  simp only [← Finset.union_assoc] at hinner
  simp_rw [hinner]
  rw [bitsExpectation_union]
  simp only [secretary_main_rate]

/-- The sacrificed mask of the implemented hidden rule, with its branch tag. -/
lemma completeHiddenRule_mask {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (r : Seed (mainSeedBits n)) :
    (completeHiddenRule M hE).mask r =
      if mainBranch r then (mainMasks r).H ∪ (mainMasks r).D ∪ (mainMasks r).C
      else (mainMasks r).H := by
  rfl

/-- Exact joint law of the branch and sacrificed mask.  Arbitrary real test
functions characterize the full finite joint law, not just its marginals. -/
theorem source_sacrificed_mask_expectation {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (f : Bool → Finset (Fin n) → ℝ) :
    (∫ r, f (mainBranch r) ((completeHiddenRule M hE).mask r) ∂sourceSeedLaw n) =
      (1 / 2 : ℝ) *
        bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ (f false) +
      (1 / 2 : ℝ) *
        bitsExpectation (fun _ => (5 / 8 : ℝ) + 3 * ((2 : ℝ) ^ 143)⁻¹)
          Finset.univ (f true) := by
  simp_rw [completeHiddenRule_mask]
  rw [integral_sourceSeedLaw (fun d b =>
    f b (if b then d.H ∪ d.D ∪ d.C else d.H))]
  have hp (g : Bool → ℝ) : fairParityExpectation (fun _ => fairParityExpectation g) =
      (1 / 2 : ℝ) * g false + (1 / 2 : ℝ) * g true := by
    simp only [fairParityExpectation]
    ring
  simp_rw [hp]
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp only [bitsExpectation_add, bitsExpectation_mul_const, bitsExpectation_const]
  rw [main_sacrificed_mask_expectation]

end MatroidProphet

end OAI
