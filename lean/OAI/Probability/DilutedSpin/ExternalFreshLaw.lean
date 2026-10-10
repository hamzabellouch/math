import OAI.Probability.DilutedSpin.ExternalRoot
import OAI.Probability.DilutedSpin.ParameterProduct

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y Z : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] {L M : ℕ}
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

lemma externalAverage_fresh_label
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hf : ∀ x, |f x| ≤ B)
    (hE : ∀ i x y, |E i x y| ≤ 1) (t u : ℝ)
    (hA : ∀ i x y, 1/2 ≤ 1+t*D i x y+u*E i x y)
    (label : Z → I) (hl : Measurable label) :
    externalAverage ξ μ ν (τ.map label) r s S a T Q m base old D E f t u =
      ∫ z, ∫ q, rootExternalTreeScore S a T Q (fun l => m l.succ) base old
        (fun i x y => 1+t*D i x y+u*E i x y) E f z (label q) ∂τ ∂fullRootLaw ξ μ ν r s := by
  apply integral_fresh_label (fullRootLaw ξ μ ν r s) τ label hl
  · exact measurable_rootExternalTreeScore S a T Q _ base old _ E f hb
  · intro z
    exact abs_externalTreeScore_le S a T Q _ (base z.1.1 z.1.2.1.1 z.1.2.1.2)
      (rootArray z.1.2.2.1 z.1.2.2.2) z.2 old _ _ f hf (hE z.2) (hA z.2)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
