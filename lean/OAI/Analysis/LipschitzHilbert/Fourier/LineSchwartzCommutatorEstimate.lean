import OAI.Analysis.LipschitzHilbert.Fourier.LineBandedCommutatorEnergy

namespace OAI

/-! The actual Lipschitz multiplier commutator estimate on Schwartz
functions, after both coefficient and input cutoffs have been removed. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform BigOperators Topology
namespace LipschitzHilbert.PacketRepresentation

theorem dyadicSchwartzSum_derivative (N : ℕ) (h : SchwartzMap ℝ ℂ) :
    schwartzDerivative 1 (dyadicSchwartzSum N h)=
      dyadicSchwartzSum N (schwartzDerivative 1 h) := by
  simp only [dyadicSchwartzSum,schwartzDerivative_sum,lineSchwartzProjection_derivative]

theorem lineSchwartz_lipschitz_commutator_energy (m b h : SchwartzMap ℝ ℂ)
    (A L : ℝ) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    (∫ x, ‖lineSchwartzCommutator m b (schwartzDerivative 1 h) x‖^2)≤
      lineCommutatorEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2) := by
  have hlimit := (lineCommutatorL2 m b).continuous.tendsto
    ((schwartzDerivative 1 h).toLp 2 volume) |>.comp (dyadicSchwartzSum_Lp_tendsto (schwartzDerivative 1 h))
  simp only [Function.comp_def,lineCommutatorL2_onSchwartz,←dyadicSchwartzSum_derivative] at hlimit
  have hnorm (g : SchwartzMap ℝ ℂ) : ‖g.toLp 2 volume‖^2=∫ x, ‖g x‖^2 :=
    memLp_toL2_norm_sq volume g (g.memLp 2 volume)
  have hevent : ∀ᶠ N : ℕ in atTop,
      ‖(lineSchwartzCommutator m b (schwartzDerivative 1 (dyadicSchwartzSum N h))).toLp 2 volume‖^2≤
        lineCommutatorEnergyConstant*A^2*L^2*(∫ x, ‖h x‖^2) := by
    apply Filter.Eventually.of_forall
    intro N
    rw [hnorm,dyadicSchwartzSum_eq_window]
    exact lineBandedCommutator_energy (dyadicResolutionWindow N) m b h A L hA hm hLip
  simpa only [hnorm] using le_of_tendsto (hlimit.norm.pow 2) hevent

end LipschitzHilbert.PacketRepresentation

end

end OAI
