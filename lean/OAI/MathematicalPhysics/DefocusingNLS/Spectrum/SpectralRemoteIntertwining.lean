import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteGauge
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteFrameEquation

namespace OAI

/-! A solution transforms through the constructed finite frame with no
additional differential or boundary hypothesis. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralRemote_intertwining_solution
    (T : ℝ → SpectralRemoteOperator) (Y : ℝ → SpectralRemoteSpace)
    (M N : SpectralRemoteOperator) (t : ℝ) (hunit : IsUnit (T t))
    (hT : HasDerivAt T (M*T t-T t*N) t)
    (hY : HasDerivAt Y (M (Y t)) t) :
    HasDerivAt (fun r => Ring.inverse (T r) (Y r))
      (N (Ring.inverse (T t) (Y t))) t := by
  let Z := fun r => Ring.inverse (T r) (Y r)
  have hi : DifferentiableAt ℝ (fun r => Ring.inverse (T r)) t :=
    (differentiableAt_inverse (𝕜 := ℝ) hunit).comp t hT.differentiableAt
  have hZ : DifferentiableAt ℝ Z t :=
    (spectralRemote_operator_apply _ _ _ _ t hi.hasDerivAt hY).differentiableAt
  have hu : ∀ᶠ r in 𝓝 t, IsUnit (T r) :=
    hT.continuousAt.eventually (Units.isOpen.mem_nhds hunit)
  have heq : (fun r => T r (Z r)) =ᶠ[𝓝 t] Y := by
    filter_upwards [hu] with r hr
    change (T r*Ring.inverse (T r)) (Y r) = Y r
    rw [Ring.mul_inverse_cancel _ hr]
    rfl
  have heqt : T t (Z t) = Y t := heq.eq_of_nhds
  have hd := spectralRemote_operator_apply _ _ _ _ t hT hZ.hasDerivAt
  have he := (hd.congr_of_eventuallyEq heq.symm).unique hY
  rw [sub_apply,mul_apply_eq_comp,mul_apply_eq_comp,heqt] at he
  have hderiv : T t (deriv Z t) = T t (N (Z t)) := by
    have hh : T t (deriv Z t) =
        M (Y t) - (M (Y t) - T t (N (Z t))) :=
      eq_sub_of_add_eq (show T t (deriv Z t) +
        (M (Y t) - T t (N (Z t))) = M (Y t) from by
          simpa only [add_comm] using he)
    simpa only [sub_sub_cancel] using hh
  have hz : deriv Z t = N (Z t) := by
    have hh := congrArg (fun v => Ring.inverse (T t) v) hderiv
    change (Ring.inverse (T t)*T t) (deriv Z t) =
      (Ring.inverse (T t)*T t) (N (Z t)) at hh
    rw [Ring.inverse_mul_cancel _ hunit] at hh
    exact hh
  exact hZ.hasDerivAt.congr_deriv hz

end DefocusingNLS

end OAI
