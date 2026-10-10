import OAI.Analysis.CircleDomains.Probability.CountableVisitNorm
import OAI.Analysis.CircleDomains.Probability.FusionSmallSets

namespace OAI

/-! The visit estimate from modulus extraction supplies the finite point-hit
tests used by fusion, with the same numerical constant. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X A : Type*} [MetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem finite_hit_square_sum_le_of_counting_norm
    (μ : ProbabilityMeasure C(PathTime, X)) (a : A → X)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : countingSquareNorm (fun s => meanVisitCount μ (a s)) ≤ ENNReal.ofReal C)
    (F : Finset X) (hF : (↑F : Set X) ⊆ range a) :
    ∑ x ∈ F, pathHitReal μ x ^ 2 ≤ C ^ 2 := by
  classical
  have hs : (∑' s, meanVisitCount μ (a s) ^ 2) ≤ (ENNReal.ofReal C) ^ 2 := by
    have he : countingSquareNorm (fun s => meanVisitCount μ (a s)) ^ 2 =
        ∑' s, meanVisitCount μ (a s) ^ 2 := by
      rw [countingSquareNorm, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
      norm_num
    rw [← he]
    exact pow_le_pow_left' hb 2
  let lift : F → A := fun x => Classical.choose (hF x.property)
  have hlift (x : F) : a (lift x) = x.val := Classical.choose_spec (hF x.property)
  have hinj : Injective lift := by
    intro x y h
    apply Subtype.ext
    rw [← hlift x, ← hlift y, h]
  have hsum : (∑ x : F, pathHitProbability μ x.val ^ 2) ≤ (ENNReal.ofReal C) ^ 2 := by
    calc
      _ ≤ ∑ x : F, meanVisitCount μ (a (lift x)) ^ 2 := by
        apply Finset.sum_le_sum
        intro x _
        rw [hlift]
        exact pow_le_pow_left' (pathHitProbability_le_meanVisitCount μ x.val) 2
      _ ≤ ∑' s, meanVisitCount μ (a s) ^ 2 :=
        calc
          _ = ∑ x ∈ Finset.univ.image lift, meanVisitCount μ (a x) ^ 2 := by
            rw [Finset.sum_image]
            exact fun _ _ _ _ h => hinj h
          _ ≤ _ := ENNReal.sum_le_tsum _
      _ ≤ _ := hs
  have hof : ENNReal.ofReal (∑ x ∈ F, pathHitReal μ x ^ 2) =
      ∑ x : F, pathHitProbability μ x.val ^ 2 := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    rw [← Finset.sum_coe_sort F]
    apply Finset.sum_congr rfl
    intro x _
    rw [ENNReal.ofReal_pow (pathHitReal_nonneg μ x.val), pathHitReal,
      ENNReal.ofReal_toReal (ne_of_lt ((pathHitProbability_le_one μ x.val).trans_lt (by simp)))]
  rw [← hof] at hsum
  have hsumreal := ENNReal.toReal_mono (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hsum
  simpa only [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hC] using hsumreal

omit [SecondCountableTopology X] [BorelSpace X] in
theorem passesHitTests_of_counting_norm
    (μ : ProbabilityMeasure C(PathTime, X)) (a : A → X)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : countingSquareNorm (fun s => meanVisitCount μ (a s)) ≤ ENNReal.ofReal C)
    (ν : Measure X) (hν : ∫⁻ x, pathHitProbability μ x ∂ν = 0) :
    PassesHitTests C μ (range a) ν :=
  ⟨finite_hit_square_sum_le_of_counting_norm μ a hC hb, hν⟩

end CircleDomainRigidity

end

end OAI
