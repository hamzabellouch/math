import OAI.GroupTheory.PolycyclicRecognition.Algebra.RectangleFiberMass
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # Large coordinate sections of a Euclidean cube -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory
open scoped ENNReal

theorem measurePreserving_cons (n : ℕ) :
    MeasurePreserving (fun z : (Fin n → ℝ) × ℝ => (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) volume := by
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.comp
    (Measure.measurePreserving_swap (μ := (volume : Measure (Fin n → ℝ))) (ν := (volume : Measure ℝ)))
  convert he using 1
  ext z i
  exact Fin.cases (by simp) (fun j => by simp) i

theorem mem_closedBall_cons {n : ℕ} (R : ℝ) (hR : 0 ≤ R)
    (t : ℝ) (x : Fin n → ℝ) :
    (Fin.cons t x : Fin (n + 1) → ℝ) ∈ closedBall 0 R ↔
      t ∈ closedBall 0 R ∧ x ∈ closedBall 0 R := by
  simp only [closedBall_pi (0 : Fin (n + 1) → ℝ) hR,
    closedBall_pi (0 : Fin n → ℝ) hR, mem_pi, mem_univ, forall_const,
    Fin.forall_fin_succ, Fin.cons_zero, Pi.zero_apply, Fin.cons_succ]

theorem realVolume_cube (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (volume (closedBall (0 : Fin n → ℝ) R)).toReal = (2 * R) ^ n := by
  rw [Real.volume_pi_closedBall _ hR, ENNReal.toReal_ofReal (by positivity)]
  simp only [Fintype.card_fin]

theorem exists_large_coordinate_sections (n : ℕ) (R : ℝ) (hR : 0 < R)
    (S : Set (Fin (n + 1) → ℝ)) (hS : MeasurableSet S)
    (hSR : S ⊆ closedBall 0 R) (hm : 0 < (volume S).toReal) :
    ∃ A : Set (Fin n → ℝ), MeasurableSet A ∧ A ⊆ closedBall 0 R ∧
      (volume S).toReal / (4 * R) ≤ (volume A).toReal ∧
      ∀ x ∈ A, (volume S).toReal / (2 * (2 * R) ^ n) ≤
        (volume {t : ℝ | Fin.cons t x ∈ S}).toReal := by
  let T : Set ((Fin n → ℝ) × ℝ) := (fun z => Fin.cons z.2 z.1) ⁻¹' S
  have hT : MeasurableSet T := hS.preimage (measurePreserving_cons n).measurable
  have hTS : (volume.prod volume) T = volume S :=
    (measurePreserving_cons n).measure_preimage hS.nullMeasurableSet
  have hsub : T ⊆ closedBall 0 R ×ˢ closedBall 0 R := by
    intro z hz
    exact ((mem_closedBall_cons R hR.le z.2 z.1).1 (hSR hz)).symm
  have hv : (volume (closedBall (0 : ℝ) R)).toReal = 2 * R := by
    rw [Real.volume_closedBall, ENNReal.toReal_ofReal (by positivity)]
  obtain ⟨A, hA, hAR, hmass, hfiber⟩ := exists_large_sections_in_rectangle
    (volume : Measure (Fin n → ℝ)) (volume : Measure ℝ)
    (closedBall 0 R) (closedBall 0 R) measurableSet_closedBall
    (isCompact_closedBall (0 : Fin n → ℝ) R).measure_ne_top
    (isCompact_closedBall (0 : ℝ) R).measure_ne_top
    (by rw [realVolume_cube n R hR.le]; positivity) (by rw [hv]; positivity)
    T hT hsub (by rwa [hTS])
  refine ⟨A, hA, hAR, ?_, ?_⟩
  · simpa only [hTS, hv, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using hmass
  · intro x hx
    have hh := hfiber x hx
    change ((volume.prod volume) T).toReal /
      (2 * (volume (closedBall (0 : Fin n → ℝ) R)).toReal) ≤
      (volume {t : ℝ | Fin.cons t x ∈ S}).toReal at hh
    simpa only [hTS, realVolume_cube n R hR.le] using hh

end PolycyclicRecognition

end

end OAI
