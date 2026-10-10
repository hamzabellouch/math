import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierRetainedComparisonBarrier
import OAI.Analysis.CoulombIonization.ThomasFermi.InverseThresholdLimitBarrier

namespace OAI

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier

lemma localTFResponse_eq_coefficient {h : ℝ} (hh : 0 ≤ h) :
    localTFResponse h = (((5/3:ℝ)*tfKinetic)^(3/2:ℝ))⁻¹*h^(3/2:ℝ) := by
  rw [localTFResponse,max_eq_left hh,Real.div_rpow hh (mul_pos (by norm_num) tfKinetic_pos).le]
  ring

lemma localTFResponse_div_radius_four {b : ℝ} (hb : 0 < b) (h : ℝ) :
    localTFResponse (h/b^4) = localTFResponse h/b^6 := by
  have ht := localTFResponse_rescale hb (h/b^4)
  have he : b^4*(h/b^4) = h := by field_simp
  rw [he] at ht
  exact (eq_div_iff (pow_ne_zero 6 hb.ne')).mpr (by linarith)

lemma inverseComparisonAt_of_cell {y : Space} {H μ lo hi xi C : ℝ}
    (hlo : 0 ≤ lo)
    (hcap : (localCellRadius y)^4*H ≤ C)
    (hinv : ∀ h ∈ Icc (lo/100000^4) (hi/100000^4),
      (localTFResponse h < (localCellRadius y)^6*μ → h-xi/100000^4 ≤ (localCellRadius y)^4*H) ∧
      ((localCellRadius y)^6*μ < localTFResponse h → (localCellRadius y)^4*H ≤ h+xi/100000^4)) :
    InverseComparisonAt ‖y‖ H μ (((5/3:ℝ)*tfKinetic)^(3/2:ℝ))⁻¹ lo hi xi (100000^4*C) := by
  have hcap' : ‖y‖^4*H ≤ 100000^4*C := by
    dsimp [localCellRadius] at hcap
    rw [div_pow,div_mul_eq_mul_div] at hcap
    simpa [mul_comm] using (div_le_iff₀ (by norm_num : (0:ℝ) < 100000^4)).mp hcap
  refine ⟨hcap',?_,?_⟩
  · intro h hh ht
    have hh' : h/100000^4 ∈ Icc (lo/100000^4) (hi/100000^4) :=
      ⟨div_le_div_of_nonneg_right hh.1 (by positivity),div_le_div_of_nonneg_right hh.2 (by positivity)⟩
    have hr := localTFResponse_div_radius_four (by norm_num : (0:ℝ) < 100000) h
    rw [localTFResponse_eq_coefficient (hlo.trans hh.1)] at hr
    have hf := (hinv _ hh').1
    simp only [localCellRadius,div_pow,div_mul_eq_mul_div] at hf
    rw [hr] at hf
    have hz := hf ((div_lt_div_iff_of_pos_right (by norm_num : (0:ℝ) < 100000^6)).mpr ht)
    rw [←sub_div] at hz
    exact (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 100000^4)).mp hz
  · intro h hh ht
    have hh' : h/100000^4 ∈ Icc (lo/100000^4) (hi/100000^4) :=
      ⟨div_le_div_of_nonneg_right hh.1 (by positivity),div_le_div_of_nonneg_right hh.2 (by positivity)⟩
    have hr := localTFResponse_div_radius_four (by norm_num : (0:ℝ) < 100000) h
    rw [localTFResponse_eq_coefficient (hlo.trans hh.1)] at hr
    have hf := (hinv _ hh').2
    simp only [localCellRadius,div_pow,div_mul_eq_mul_div] at hf
    rw [hr] at hf
    have hz := hf ((div_lt_div_iff_of_pos_right (by norm_num : (0:ℝ) < 100000^6)).mpr ht)
    rw [←add_div] at hz
    exact (div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 100000^4)).mp hz

end CoulombAtom

end

end OAI
