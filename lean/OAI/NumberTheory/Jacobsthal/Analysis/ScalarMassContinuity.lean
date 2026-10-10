import OAI.NumberTheory.Jacobsthal.Estimates.ScalarTailRecurrence

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
namespace ErdosOmissionTail
open ErdosContinuousBoundary

theorem scalarTailMass_continuous (n : ℕ) :
    Continuous (fun p : ℝ×ℝ => scalarTailMass n p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let Y : ℝ := |p.1|+(n:ℝ)+5
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  let F : (ℝ×ℝ) → ℝ → ℝ := fun q y => scalarTailIntegrand n q.1 q.2 y
  have hpmap : Continuous (fun q : (ℝ×ℝ)×ℝ => (2*q.2+2-q.1.1,q.1.2)) := by fun_prop
  have hh : Continuous (fun q : (ℝ×ℝ)×ℝ => scalarFreeIterate n terminalBlock (2*q.2+2-q.1.1) q.1.2) :=
    (scalarFreeIterate_continuous terminalBlock_continuous n).comp hpmap
  have hF : Continuous F.uncurry := (continuous_const.mul (continuous_snd.pow 2)).mul hh
  have hI : Continuous (fun q : ℝ×ℝ => ∫ y in Icc (0:ℝ) Y,F q y) :=
    continuous_parametric_integral_of_continuous hF isCompact_Icc
  apply hI.continuousAt.congr_of_eventuallyEq
  have hnear : ∀ᶠ q : ℝ×ℝ in 𝓝 p,q.1 < p.1+1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by linarith : p.1 < p.1+1))
  filter_upwards [hnear] with q hq
  have hp := le_abs_self p.1
  have hp0 := abs_nonneg p.1
  have hhigh : q.1/2+(n:ℝ)+4 ≤ Y := by dsimp [Y]; linarith
  rw [scalarTailMass_bounded n q.1 q.2 Y hY hhigh,
    intervalIntegral.integral_of_le hY,← integral_Icc_eq_integral_Ioc]

end ErdosOmissionTail

end

end Erdos970

end OAI
