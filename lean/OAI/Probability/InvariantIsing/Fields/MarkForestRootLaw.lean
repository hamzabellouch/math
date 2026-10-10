import OAI.Probability.IsingPerceptron.ChildLabel

namespace OAI

/-! The one-branch and two-distinct-branch laws of the finite independent mark forest. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {A : Type} [MeasurableSpace A]

lemma markForestRoot_preserving (n : ℕ) (μ : ℕ → ProbabilityMeasure A) (a : ChildLabel) :
    MeasurePreserving (fun z : MarkForest A (n+1) => z a.1 a.2)
      (markForestLaw A (n+1) μ : Measure (MarkForest A (n+1)))
      ((μ 0 : Measure A).prod (markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n))) := by
  let Q := (μ 0 : Measure A).prod (markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n))
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => Q) a.2).comp
    (measurePreserving_eval_infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => Q)) a.1)

lemma markForestRoots_preserving (n : ℕ) (μ : ℕ → ProbabilityMeasure A)
    (a b : ChildLabel) (hab : a ≠ b) :
    MeasurePreserving (fun z : MarkForest A (n+1) => (z a.1 a.2,z b.1 b.2))
      (markForestLaw A (n+1) μ : Measure (MarkForest A (n+1)))
      (((μ 0 : Measure A).prod (markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n))).prod
        ((μ 0 : Measure A).prod (markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n)))) := by
  let Q := (μ 0 : Measure A).prod (markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n))
  have hf : MeasurePreserving (fun z : MarkForest A (n+1) => fun p : ChildLabel => z p.1 p.2)
      (markForestLaw A (n+1) μ : Measure (MarkForest A (n+1)))
      (Measure.infinitePi fun _ : ChildLabel => Q) :=
    ⟨by fun_prop, Measure.infinitePi_map_curry_symm (fun (_ _ : ℕ) => Q)⟩
  have hp : MeasurePreserving (fun z : ChildLabel → A × MarkForest A n => (z a,z b))
      (Measure.infinitePi fun _ : ChildLabel => Q) (Q.prod Q) :=
    ⟨by fun_prop, Measure.infinitePi_map_eval_prod hab⟩
  exact hp.comp hf

end InvariantIsing

end

end OAI
