import OAI.Analysis.CircleDomains.Probability.CodePathLaws
import OAI.Analysis.CircleDomains.Probability.PathLawMixtures

namespace OAI

/-! The finite dust hit tests imply the full square sum needed for shrinking
collars, with no enlargement of the constant. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [MeasurableSpace X] [BorelSpace C(PathTime, X)] in
theorem pathHit_square_tsum_le (μ : ProbabilityMeasure C(PathTime, X))
    (B : Set X) (C : ℝ)
    (hfinite : ∀ F : Finset B, ∑ x ∈ F, pathHitReal μ x.val ^ 2 ≤ C ^ 2) :
    (∑' x : B, pathHitProbability μ x.val ^ 2) ≤ ENNReal.ofReal (C ^ 2) := by
  apply ENNReal.summable.tsum_le_of_sum_le
  intro F
  have he : (∑ x ∈ F, pathHitProbability μ x.val ^ 2) =
      ENNReal.ofReal (∑ x ∈ F, pathHitReal μ x.val ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    apply Finset.sum_congr rfl
    intro x hx
    rw [ENNReal.ofReal_pow (pathHitReal_nonneg μ x.val), pathHitReal,
      ENNReal.ofReal_toReal (ne_of_lt ((pathHitProbability_le_one μ x.val).trans_lt (by simp)))]
  rw [he]
  exact ENNReal.ofReal_le_ofReal (hfinite F)

theorem codeHit_square_tsum_le (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (C : ℝ)
    (hfinite : ∀ F : Finset d.dust,
      ∑ x ∈ F, pathHitReal (codePathLaw d P) x.val ^ 2 ≤ C ^ 2) :
    (∑' x : d.dust, codeHitProbability d P x.val ^ 2) ≤ ENNReal.ofReal (C ^ 2) := by
  simpa only [pathHitProbability_codePathLaw] using
    pathHit_square_tsum_le (codePathLaw d P) d.dust C hfinite

theorem codeHit_square_tsum_restrict {S : Set X}
    (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d)) (C : ℝ)
    (hfinite : ∀ F : Finset d.dust,
      ∑ x ∈ F, pathHitReal (codePathLaw d P) x.val ^ 2 ≤ C ^ 2)
    (hS : S ⊆ d.dust) : (∑' x : S, codeHitProbability d P x.val ^ 2) < ∞ := by
  let f : S → d.dust := fun x => ⟨x.val, hS x.property⟩
  have hf : Injective f := fun _ _ h => Subtype.ext (congrArg (fun z : d.dust => z.val) h)
  exact (ENNReal.tsum_comp_le_tsum_of_injective hf
    (fun x : d.dust => codeHitProbability d P x.val ^ 2)).trans_lt
      ((codeHit_square_tsum_le d P C hfinite).trans_lt ENNReal.ofReal_lt_top)

end CircleDomainRigidity

end

end OAI
