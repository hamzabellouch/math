import OAI.Analysis.LipschitzHilbert.Estimates.SmoothedCommutatorEnergy
import OAI.Analysis.LipschitzHilbert.Fourier.LineCommutatorCoefficientLimit

namespace OAI

/-! Removing coefficient smoothing gives the uniform commutator bound
for every finite collection of actual input frequency bands. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

theorem lineBandedCommutator_energy (J : Finset ℤ) (m b h : SchwartzMap ℝ ℂ)
    (A L : ℝ) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    (∫ x, ‖lineSchwartzCommutator m b (schwartzDerivative 1 (∑ j∈J, lineDyadic h j)) x‖^2)≤
      lineCommutatorEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2) := by
  classical
  by_cases hJ : J.Nonempty
  · let v := J.max' hJ+4
    let N₀ := (-J.min' hJ-4).toNat
    let f := schwartzDerivative 1 (∑ j∈J, lineDyadic h j)
    have hlimit := (lineCommutator_lowpass_tendsto m b f L hLip).norm.pow 2
    have hnorm (g : SchwartzMap ℝ ℂ) : ‖g.toLp 2 volume‖^2=∫ x, ‖g x‖^2 :=
      memLp_toL2_norm_sq volume g (g.memLp 2 volume)
    have hevent : ∀ᶠ N : ℕ in atTop,
        ‖(lineSchwartzCommutator m (lineLowpass b (-(N:ℤ))) f).toLp 2 volume‖^2≤
          lineCommutatorEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2) := by
      filter_upwards [eventually_ge_atTop N₀] with N hN
      have hlo (j : ℤ) (hj : j∈J) : -(N:ℤ)≤j+4 := by
        have hmin := Finset.min'_le J j hj
        dsimp [N₀] at hN
        omega
      have hhi (j : ℤ) (hj : j∈J) : j+4≤v := by
        have hmax := Finset.le_max' J j hj
        dsimp [v]
        omega
      simpa only [hnorm] using smoothedCommutator_energy J m b h A L hA hm hLip (-(N:ℤ)) v hlo hhi
    simpa only [hnorm] using le_of_tendsto hlimit hevent
  · have he : J=∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    subst J
    simp only [Finset.sum_empty,schwartzDerivative_zero,lineSchwartzCommutator_zero_right,
      zero_apply,norm_zero,zero_pow (by decide : 2≠0),integral_zero]
    have hc := lineCommutatorEnergyConstant_nonneg
    positivity

end LipschitzHilbert.PacketRepresentation

end

end OAI
