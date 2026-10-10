import OAI.Probability.InvariantIsing.Fields.MarkForestRootLaw

namespace OAI

/-! Pairing the two independent root seeds separately from their two subforests. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

lemma pairProductShuffle_preserving {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (η : Measure C) (ρ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite η] [SFinite ρ] :
    MeasurePreserving (fun p : (A × B) × (C × D) => ((p.1.1,p.2.1),(p.1.2,p.2.2)))
      ((μ.prod ν).prod (η.prod ρ)) ((μ.prod η).prod (ν.prod ρ)) := by
  have h1 := measurePreserving_prodAssoc μ ν (η.prod ρ)
  have h2 := (MeasurePreserving.id μ).prod
    ((measurePreserving_prodAssoc ν η ρ).symm MeasurableEquiv.prodAssoc)
  have h3 := (MeasurePreserving.id μ).prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := η)).prod (MeasurePreserving.id ρ))
  have h4 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc η ν ρ)
  have h5 := (measurePreserving_prodAssoc μ η (ν.prod ρ)).symm MeasurableEquiv.prodAssoc
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

lemma markForestPairRoots_preserving {A : Type} [MeasurableSpace A]
    (n : ℕ) (μ : ℕ → ProbabilityMeasure A) (a b : ChildLabel) :
    MeasurePreserving (fun p : MarkForest A (n+1) × MarkForest A (n+1) =>
      (((p.1 a.1 a.2).1,(p.2 b.1 b.2).1),((p.1 a.1 a.2).2,(p.2 b.1 b.2).2)))
      ((markForestLaw A (n+1) μ : Measure (MarkForest A (n+1))).prod
        (markForestLaw A (n+1) μ : Measure (MarkForest A (n+1))))
      (((μ 0 : Measure A).prod (μ 0 : Measure A)).prod
        ((markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n)).prod
          (markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n)))) :=
  (pairProductShuffle_preserving _ _ _ _).comp
    ((markForestRoot_preserving n μ a).prod (markForestRoot_preserving n μ b))

lemma markForestDistinctRoots_preserving {A : Type} [MeasurableSpace A]
    (n : ℕ) (μ : ℕ → ProbabilityMeasure A) (a b : ChildLabel) (hab : a ≠ b) :
    MeasurePreserving (fun g : MarkForest A (n+1) =>
      (((g a.1 a.2).1,(g b.1 b.2).1),((g a.1 a.2).2,(g b.1 b.2).2)))
      (markForestLaw A (n+1) μ : Measure (MarkForest A (n+1)))
      (((μ 0 : Measure A).prod (μ 0 : Measure A)).prod
        ((markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n)).prod
          (markForestLaw A n (fun i => μ (i+1)) : Measure (MarkForest A n)))) :=
  (pairProductShuffle_preserving _ _ _ _).comp (markForestRoots_preserving n μ a b hab)

end InvariantIsing

end

end OAI
