import Mathlib.MeasureTheory.Integral.Pi
import OAI.Geometry.NodalSets.Elliptic.RealCubeAverage

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Function
noncomputable section

def realFinCube (n : ℕ) : Set (Fin n → ℝ) := univ.pi (fun _ ↦ Icc (-1:ℝ) 1)

lemma realFinCube_volume (n : ℕ) :
    (volume : Measure (Fin n → ℝ)).restrict (realFinCube n) =
      Measure.pi (fun _ : Fin n ↦ volume.restrict (Icc (-1:ℝ) 1)) :=
  Measure.restrict_pi_pi _ _

lemma realFinCube_integrable (n : ℕ) (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    IntegrableOn F (realFinCube n) :=
  hF.continuousOn.integrableOn_compact (isCompact_univ_pi (fun _ ↦ isCompact_Icc))

theorem realFinCube_integral_succ (n : ℕ) (F : (Fin (n+1) → ℝ) → ℝ)
    (hF : Continuous F) :
    (∫ z in realFinCube (n+1), F z) =
      ∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, F (Fin.cons t z) := by
  have hi := realFinCube_integrable (n+1) F hF
  rw [IntegrableOn,realFinCube_volume] at hi
  let μ := fun _ : Fin (n+1) ↦ volume.restrict (Icc (-1:ℝ) 1)
  have hm := (measurePreserving_piFinSuccAbove μ 0).symm
  have hh := hm.integrable_comp_of_integrable hi
  have he := hm.integral_comp' F
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk,Fin.insertNth_zero] at hh he
  simp only [realFinCube_volume]
  exact he.symm.trans (integral_prod _ hh)

lemma realFinCube_integral_zero (F : (Fin 0 → ℝ) → ℝ) :
    (∫ z in realFinCube 0, F z) = F Fin.elim0 := by
  have hs : realFinCube 0 = univ := by ext z; simp [realFinCube]
  rw [hs,Measure.restrict_univ,Measure.volume_pi_eq_dirac Fin.elim0,integral_dirac]

end
end Yau.Geometry

end OAI
