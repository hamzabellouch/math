import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # Splitting the independent parameter cube preserves volume -/

namespace PolycyclicRecognition

open MeasureTheory

theorem measurePreserving_finAppend (n k : ℕ) :
    MeasurePreserving (fun p : (Fin n → ℝ) × (Fin k → ℝ) => Fin.append p.1 p.2)
      volume volume := by
  have h₁ := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin n ⊕ Fin k => ℝ)
  have h₂ := volume_measurePreserving_piCongrLeft
    (fun _ : Fin (n + k) => ℝ) finSumFinEquiv
  convert h₂.comp h₁ using 1
  ext p i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  simp only [Function.comp_apply]
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  cases j with
  | inl j =>
      change Fin.append p.1 p.2 (Fin.castAdd k j) = p.1 j
      simp
  | inr j =>
      change Fin.append p.1 p.2 (Fin.natAdd n j) = p.2 j
      simp

end PolycyclicRecognition

end OAI
