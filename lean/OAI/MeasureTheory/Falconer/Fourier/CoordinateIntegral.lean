import OAI.MeasureTheory.Falconer.Angular.GnomonicChart
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

/-!
# Isolating one Euclidean chart coordinate

This change of coordinates preserves the actual Euclidean volume. It
therefore allows the scalar nonstationary bound to be integrated in the
remaining chart coordinates without any additional measure assumption.
-/

namespace Falconer
open MeasureTheory Set

noncomputable def coordinateEquiv (n : ℕ) : Space (n+1) ≃ᵐ Space n × ℝ :=
  ((MeasurableEquiv.toLp 2 (Fin (n+1) → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0)).trans
      (((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin n → ℝ))).trans
        (MeasurableEquiv.prodComm : ℝ × Space n ≃ᵐ Space n × ℝ))

noncomputable def coordinateJoin {n : ℕ} (x : Space n) (u : ℝ) : Space (n+1) :=
  (coordinateEquiv n).symm (x,u)

theorem coordinateJoin_eq {n : ℕ} (x : Space n) (u : ℝ) :
    coordinateJoin x u = WithLp.toLp 2 (Fin.cons u (WithLp.ofLp x)) := by
  change WithLp.toLp 2 (Fin.insertNth (α := fun _ : Fin (n+1) => ℝ) 0 u
    (WithLp.ofLp x)) = _
  rw [Fin.insertNth_zero]
  simp only [cast_eq]

theorem coordinateEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (coordinateEquiv n) (volume : Measure (Space (n+1)))
      ((volume : Measure (Space n)).prod volume) := by
  have h₀ := PiLp.volume_preserving_ofLp (Fin (n+1))
  have h₁ := volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have h₂ := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin n))
  have h₃ : MeasurePreserving Prod.swap
      ((volume : Measure ℝ).prod (volume : Measure (Space n)))
      ((volume : Measure (Space n)).prod volume) := Measure.measurePreserving_swap
  exact h₃.comp (h₂.comp (h₁.comp h₀))

theorem coordinate_integral {n : ℕ} (f : Space (n+1) → ℂ) :
    (∫ z, f z) = ∫ z : Space n × ℝ, f (coordinateJoin z.1 z.2)
      ∂(volume : Measure (Space n)).prod volume := by
  have h := (coordinateEquiv_measurePreserving n).symm
  exact (h.integral_comp' f).symm

theorem coordinate_iterated_integral {n : ℕ} (f : Space (n+1) → ℂ)
    (hf : Integrable f) :
    (∫ z, f z) = ∫ x : Space n, ∫ u : ℝ, f (coordinateJoin x u) := by
  have h := (coordinateEquiv_measurePreserving n).symm
  have hi : Integrable (fun z : Space n × ℝ => f (coordinateJoin z.1 z.2))
      ((volume : Measure (Space n)).prod volume) :=
    h.integrable_comp_of_integrable hf
  rw [coordinate_integral,integral_prod _ hi]

end Falconer

end OAI
