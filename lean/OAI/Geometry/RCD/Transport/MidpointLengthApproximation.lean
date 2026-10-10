import OAI.Geometry.RCD.Transport.UniformLengthPartition
import OAI.Geometry.RCD.Transport.MidpointReducedComparison

namespace OAI

/-! # Exact midpoint distortion as the limit of finite length bins -/

open Set Filter TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates

def upperLength (ε d : ℝ) : ℝ := ((⌊d/ε⌋₊:ℝ)+1)*ε

theorem upperLength_pos {ε d : ℝ} (hε : 0<ε) : 0<upperLength ε d := by
  unfold upperLength
  positivity

theorem le_upperLength {ε d : ℝ} (hε : 0<ε) (hd : 0≤d) : d≤upperLength ε d :=
  (mem_lengthBin_floor hε hd).2.le

theorem upperLength_le_add {ε d : ℝ} (hε : 0<ε) (hd : 0≤d) : upperLength ε d≤d+ε := by
  have hh := (mem_lengthBin_floor hε hd).1
  dsimp only [upperLength]
  nlinarith

theorem upperLength_tendsto {ε : ℕ → ℝ} (hε : ∀ m, 0<ε m)
    (ht : Tendsto ε atTop (𝓝 0)) {d : ℝ} (hd : 0≤d) :
    Tendsto (fun m => upperLength (ε m) d) atTop (𝓝 d) := by
  have hupper : Tendsto (fun m => d+ε m) atTop (𝓝 d) := by
    simpa only [add_zero] using tendsto_const_nhds.add ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun m => le_upperLength (hε m) hd) (fun m => upperLength_le_add (hε m) hd)

theorem sigma_nonpos_midpoint_eq {K N d : ℝ} (hK : K≤0) (hN : 1<N) (hd : 0≤d) :
    sigma K N (1/2) d=ENNReal.ofReal (1/(2*Real.cosh (d*Real.sqrt (-K/(N-1))/2))) := by
  by_cases hK0 : K=0
  · simp [hK0,sigma]
  by_cases hd0 : d=0
  · simp [hd0,sigma]
  exact sigma_negative_midpoint (lt_of_le_of_ne hK hK0) hN (lt_of_le_of_ne hd (Ne.symm hd0))

theorem sigma_nonpos_midpoint_ne_zero {K N d : ℝ}
    (hK : K≤0) (hN : 1<N) (hd : 0≤d) : sigma K N (1/2) d≠0 := by
  rw [sigma_nonpos_midpoint_eq hK hN hd]
  exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'

theorem sigma_nonpos_midpoint_ne_top {K N d : ℝ}
    (hK : K≤0) (hN : 1<N) (hd : 0≤d) : sigma K N (1/2) d≠∞ := by
  rw [sigma_nonpos_midpoint_eq hK hN hd]
  exact ENNReal.ofReal_ne_top

theorem midpoint_upperLength_tendsto {K N d : ℝ} (hK : K≤0) (hN : 1<N) (hd : 0≤d)
    {ε : ℕ → ℝ} (hε : ∀ m, 0<ε m) (ht : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun m => sigma K N (1/2) (upperLength (ε m) d/2)) atTop
      (𝓝 (sigma K N (1/2) (d/2))) := by
  let F := fun x : ℝ => ENNReal.ofReal (1/(2*Real.cosh (x*Real.sqrt (-K/(N-1))/2)))
  have hF : Continuous F := by
    apply ENNReal.continuous_ofReal.comp
    apply Continuous.div continuous_const
    · fun_prop
    · intro x
      exact mul_ne_zero (by norm_num) (Real.cosh_pos _).ne'
  have hh := hF.continuousAt.tendsto.comp ((upperLength_tendsto hε ht hd).div_const 2)
  rw [sigma_nonpos_midpoint_eq hK hN (div_nonneg hd (by norm_num))]
  apply hh.congr'
  exact Eventually.of_forall (fun m => (sigma_nonpos_midpoint_eq hK hN
    (div_nonneg (upperLength_pos (hε m)).le (by norm_num))).symm)

end RegularPointCoordinates

end

end OAI
