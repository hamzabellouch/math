import OAI.Geometry.RCD.Heat.EntropyPowerRateContinuous

namespace OAI

/-! # Continuity of the dimensional evolution rate in cost and entropy -/

open Set Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

def dimensionalEntropyRate (K N : ℝ) (z : ℝ × ℝ × ℝ) : ℝ :=
  entropyPowerRate N (-(K*max z.1 0/N)) (Real.exp (-z.2.1/N)) (Real.exp (-z.2.2/N))

theorem dimensionalEntropyRate_eq {K N w e f : ℝ} (hw : 0 ≤ w) :
    dimensionalEntropyRate K N (w,e,f) =
      entropyPowerRate N (-(K*w/N)) (Real.exp (-e/N)) (Real.exp (-f/N)) := by
  simp only [dimensionalEntropyRate,max_eq_left hw]

theorem continuous_dimensionalEntropyRate {K N : ℝ} (hK : K ≤ 0) (hN : 0 < N) :
    Continuous (dimensionalEntropyRate K N) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  unfold dimensionalEntropyRate
  have hn (w : ℝ) : 0 ≤ -(K*max w 0/N) := neg_nonneg.mpr
    (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hK (le_max_right _ _)) hN.le)
  apply tendsto_entropyPowerRate (N := N) (fun (x : ℝ × ℝ × ℝ) => hn x.1) (hn z.1) (Real.exp_ne_zero _)
  · exact (show Continuous (fun x : ℝ × ℝ × ℝ => -(K*max x.1 0/N)) by fun_prop).tendsto z
  · exact (show Continuous (fun x : ℝ × ℝ × ℝ => Real.exp (-x.2.1/N)) by fun_prop).tendsto z
  · exact (show Continuous (fun x : ℝ × ℝ × ℝ => Real.exp (-x.2.2/N)) by fun_prop).tendsto z

end RegularPointCoordinates

end

end OAI
