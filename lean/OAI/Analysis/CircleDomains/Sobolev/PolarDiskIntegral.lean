import OAI.Analysis.CircleDomains.Sobolev.PolarAnnulusIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! Signed real polar integration over a disk, on the closed parameter
rectangle needed for the elementary divergence theorem. -/
open Set Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma integral_polar_disk (q : ℂ → ℝ) (R : ℝ) :
    (∫ z in ball (0 : ℂ) R, q z) =
      ∫ p in Icc (0, -Real.pi) (R, Real.pi), p.1 * q (Complex.polarCoord.symm p) := by
  let A := ball (0 : ℂ) R
  let S := Ioo (0 : ℝ) R
  let T := Ioo (-Real.pi) Real.pi
  let f : ℝ × ℝ → ℝ := fun p => p.1 * q (Complex.polarCoord.symm p)
  have hP : MeasurableSet polarCoord.target := polarCoord.open_target.measurableSet
  have hp := Complex.integral_comp_polarCoord_symm (A.indicator q)
  rw [integral_indicator isOpen_ball.measurableSet] at hp
  calc
    _ = ∫ p in polarCoord.target, p.1 * (A.indicator q) (Complex.polarCoord.symm p) := hp.symm
    _ = ∫ p, (S ×ˢ T).indicator f p := by
      rw [← integral_indicator hP]
      apply integral_congr_ae
      filter_upwards [] with p
      by_cases hp : p ∈ polarCoord.target
      · have hp0 : 0 < p.1 := hp.1
        have hmem : Complex.polarCoord.symm p ∈ A ↔ p.1 ∈ S := by
          simp only [A,S,mem_ball_zero_iff,mem_Ioo,Complex.norm_polarCoord_symm,
            abs_of_pos hp0,and_iff_right hp0]
        by_cases hS : p.1 ∈ S
        · have hST : p ∈ S ×ˢ T := ⟨hS,hp.2⟩
          rw [indicator_of_mem hp,indicator_of_mem hST,indicator_of_mem (hmem.mpr hS)]
        · have hST : p ∉ S ×ˢ T := fun h => hS h.1
          rw [indicator_of_mem hp,indicator_of_notMem hST,
            indicator_of_notMem (fun h => hS (hmem.mp h)),mul_zero]
      · have hST : p ∉ S ×ˢ T := fun h => hp ⟨h.1.1,h.2⟩
        rw [indicator_of_notMem hp,indicator_of_notMem hST]
    _ = ∫ p in S ×ˢ T, f p := integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)
    _ = _ := by
      rw [← Icc_prod_Icc,Measure.volume_eq_prod]
      exact setIntegral_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc)

end CircleDomainRigidity

end

end OAI
