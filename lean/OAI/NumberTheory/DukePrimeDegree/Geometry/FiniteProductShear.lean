import OAI.NumberTheory.DukePrimeDegree.Geometry.RootProductReorder
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

/-! # A coordinate shear of a finite root-product measure -/

noncomputable section
open MeasureTheory ProbabilityTheory Function

namespace DukePrimeDegree

def finiteCoordinateEquiv {n : ℕ} (i : Fin (n+1)) :
    (Fin (n+1) → ℝ) ≃ᵐ ((Fin n → ℝ) × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).trans MeasurableEquiv.prodComm

def finiteCoordinateShear {n : ℕ} (i : Fin (n+1)) (F : (Fin n → ℝ) → ℝ)
    (x : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  (finiteCoordinateEquiv i).symm
    ((finiteCoordinateEquiv i x).1,(finiteCoordinateEquiv i x).2 + F (finiteCoordinateEquiv i x).1)

theorem finiteCoordinateShear_preserves {n : ℕ} (i : Fin (n+1))
    (ν : Fin (n+1) → Measure ℝ) [∀ j, SigmaFinite (ν j)]
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F)
    (hinv : ∀ a : ℝ, (ν i).map (fun t => t+a) = ν i) :
    MeasurePreserving (finiteCoordinateShear i F) (Measure.pi ν) (Measure.pi ν) := by
  let η := Measure.pi (fun j : Fin n => ν (i.succAbove j))
  let E := finiteCoordinateEquiv i
  have hE : MeasurePreserving E (Measure.pi ν) (η.prod (ν i)) :=
    (Measure.measurePreserving_swap).comp (measurePreserving_piFinSuccAbove ν i)
  have hshear : MeasurePreserving (fun z : (Fin n → ℝ) × ℝ => (z.1,z.2+F z.1))
      (η.prod (ν i)) (η.prod (ν i)) :=
    (MeasurePreserving.id η).skew_product (measurable_snd.add (hF.comp measurable_fst))
      (Filter.Eventually.of_forall fun w => hinv (F w))
  exact (hE.symm E).comp (hshear.comp hE)

lemma finiteCoordinateShear_apply_same {n : ℕ} (i : Fin (n+1))
    (F : (Fin n → ℝ) → ℝ) (x : Fin (n+1) → ℝ) :
    finiteCoordinateShear i F x i = x i + F (fun j => x (i.succAbove j)) := by
  change i.insertNth (α := fun _ : Fin (n+1) => ℝ) (x i + F (fun j => x (i.succAbove j)))
    (fun j => x (i.succAbove j)) i = _
  simp

lemma finiteCoordinateShear_apply_succAbove {n : ℕ} (i : Fin (n+1))
    (F : (Fin n → ℝ) → ℝ) (x : Fin (n+1) → ℝ) (j : Fin n) :
    finiteCoordinateShear i F x (i.succAbove j) = x (i.succAbove j) := by
  change i.insertNth (α := fun _ : Fin (n+1) => ℝ) (x i + F (fun j => x (i.succAbove j)))
    (fun j => x (i.succAbove j)) (i.succAbove j) = _
  simp

end DukePrimeDegree

end

end OAI
