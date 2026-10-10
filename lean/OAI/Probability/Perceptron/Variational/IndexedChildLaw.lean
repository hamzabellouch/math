import Mathlib
import OAI.Probability.Perceptron.Cascade.IndexedCascadeRegular

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma indexedCascadeMarks_child_law {S : Type} [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (n : ℕ) (i j : ℕ) :
    MeasurePreserving (fun m : IndexedCascadeMarks S (n+1) => m i j)
      (indexedCascadeMarksLaw ν (n+1) : Measure (IndexedCascadeMarks S (n+1)))
      ((ν : Measure S).prod (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ =>
    (ν : Measure S).prod (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))) j).comp
      (measurePreserving_eval_infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
        (ν : Measure S).prod (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))) i)

lemma indexedCascade_joint_child_law {S : Type} [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (n : ℕ) (z : Fin (n+1) → ℝ) (i j : ℕ) :
    MeasurePreserving (fun p : IndexedCascadeBase (n+1)×IndexedCascadeMarks S (n+1) =>
      ((p.2 i j).1,(((p.1 i).2 j).2,(p.2 i j).2)))
      ((indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))).prod
        (indexedCascadeMarksLaw ν (n+1) : Measure (IndexedCascadeMarks S (n+1))))
      ((ν : Measure S).prod ((indexedCascadeBaseLaw n (fun l => z l.succ) :
        Measure (IndexedCascadeBase n)).prod (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)))) := by
  let B : Measure (IndexedCascadeBase n) := indexedCascadeBaseLaw n (fun l => z l.succ)
  let M : Measure (IndexedCascadeMarks S n) := indexedCascadeMarksLaw ν n
  have hr : MeasurePreserving (fun p : IndexedCascadeBase n×(S×IndexedCascadeMarks S n) =>
      (p.2.1,(p.1,p.2.2))) (B.prod ((ν : Measure S).prod M)) ((ν : Measure S).prod (B.prod M)) :=
    ⟨by fun_prop,prod_rotate_front B (ν : Measure S) M⟩
  exact hr.comp ((indexedCascadeBase_child_law n z i j).prod
    (indexedCascadeMarks_child_law ν n i j))

lemma indexedCascade_ae_children {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) (step : X×S → X) (hs : Measurable step)
    (n : ℕ) (z : Fin (n+1) → ℝ) (P : X×(IndexedCascadeBase n×IndexedCascadeMarks S n) → Prop)
    (hP : MeasurableSet {p | P p})
    (h : ∀ x, ∀ᵐ p ∂(indexedCascadeBaseLaw n (fun l => z l.succ) : Measure (IndexedCascadeBase n)).prod
      (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n)), P (x,p)) (x : X) :
    ∀ᵐ p ∂(indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))).prod
      (indexedCascadeMarksLaw ν (n+1) : Measure (IndexedCascadeMarks S (n+1))), ∀ i j,
        P (step (x,(p.2 i j).1),(((p.1 i).2 j).2,(p.2 i j).2)) := by
  have hprod : ∀ᵐ p ∂(ν : Measure S).prod
      ((indexedCascadeBaseLaw n (fun l => z l.succ) : Measure (IndexedCascadeBase n)).prod
        (indexedCascadeMarksLaw ν n : Measure (IndexedCascadeMarks S n))), P (step (x,p.1),p.2) :=
    (Measure.ae_prod_iff_ae_ae (hP.preimage (by fun_prop))).mpr
      (ae_of_all _ fun s => h (step (x,s)))
  exact ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
    (indexedCascade_joint_child_law ν n z i j).quasiMeasurePreserving.ae hprod

end SphericalPerceptronFreeEnergy
end

end OAI
