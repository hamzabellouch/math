import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergyResolventTransport
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergyRegularDomain
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalSpectralResolvent

namespace OAI

/-! Meromorphic continuation of the actual global weak resolvent past
the finite exceptional spectrum, throughout the Eisenstein half-plane. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

theorem cubicThetaGlobalResolvent_meromorphic {z : ℂ} (hz : z.im≠0 ∨ z.re<2) :
    MeromorphicAt cubicThetaGlobalResolvent z := by
  have h0 := cubicThetaMeromorphic_clm
      (E:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace)
      (F:=CubicThetaGlobalL2 →L[ℂ] CubicThetaGlobalL2)
      (f:=fun w : ℂ => Ring.inverse (cubicThetaEnergyPencil w)) (z:=z)
      cubicThetaEnergyResolventTransport (cubicThetaEnergyInverse_meromorphic hz)
  have h : MeromorphicAt cubicThetaEnergyValueResolvent z := h0
  apply h.congr
  filter_upwards [cubicThetaEnergyPencil_eventually_unit hz] with w hw
  exact cubicThetaEnergyValueResolvent_eq hw

lemma cubicThetaGlobalSpectralParameter_below_threshold {s : ℂ} (hs : 1<s.re) :
    (cubicThetaGlobalSpectralParameter s).im≠0 ∨
      (cubicThetaGlobalSpectralParameter s).re<2 := by
  by_cases hi : s.im=0
  · right
    simp only [cubicThetaGlobalSpectralParameter,Complex.sub_re,Complex.one_re,
      Complex.mul_re,Complex.sub_im,hi]
    norm_num
    nlinarith [sq_pos_of_pos (sub_pos.mpr hs)]
  · rcases cubicThetaGlobalSpectralParameter_regular hs (Or.inl hi) with h|h
    · exact Or.inl h
    · exact Or.inr (h.trans (by norm_num))

theorem cubicThetaGlobalSpectralResolvent_meromorphic {s : ℂ} (hs : 1<s.re) :
    MeromorphicAt cubicThetaGlobalSpectralResolvent s := by
  have h := cubicThetaGlobalResolvent_meromorphic
    (cubicThetaGlobalSpectralParameter_below_threshold hs)
  have hp : AnalyticAt ℂ cubicThetaGlobalSpectralParameter s :=
    analyticAt_const.sub (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
  exact h.comp_analyticAt hp

end CubicFirstMoment

end

end OAI
