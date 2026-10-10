import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # Product-measure bounds from a single coordinate's sections -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] {n : ℕ}

theorem pi_measure_le_of_coordinate_sections (μ : Measure X) [IsFiniteMeasure μ]
    (i : Fin (n+1)) (E : Set (Fin (n+1) → X)) (hE : MeasurableSet E) (C : ℝ≥0∞)
    (hsec : ∀ y : Fin n → X, μ {x | i.insertNth x y ∈ E} ≤ C) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) E ≤ C*(μ univ)^n := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) i
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).symm
  have he : (Measure.pi (fun _ : Fin (n+1) => μ)) E =
      (μ.prod (Measure.pi (fun _ : Fin n => μ))) (e.symm ⁻¹' E) := by
    rw [← hm.map_eq,Measure.map_apply hm.measurable hE]
  rw [he,Measure.prod_apply_symm (hE.preimage e.symm.measurable)]
  calc
    _ ≤ ∫⁻ _y : Fin n → X, C ∂Measure.pi (fun _ => μ) := by
      apply lintegral_mono
      intro y
      exact hsec y
    _ = _ := by simp only [lintegral_const,Measure.pi_univ,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

end Falconer

end OAI
