import OAI.Analysis.CircleDomains.Topology.LimitSphereExtension
import Mathlib.Analysis.Complex.Liouville

namespace OAI

/-! A principally normalized Möbius transformation is the identity.
The finite-coordinate remainder is entire and tends to zero at infinity. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem principal_mobius_identity (M : Mobius)
    (hnorm : IsPrincipalNormalized (fun p : Sphere => M • p)) :
    ∀ p : Sphere, M • p = p := by
  have hc : M 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.mp hnorm.1
  have hd : M 1 1 ≠ 0 := by
    intro hd
    apply M.det_ne_zero
    simp [Matrix.det_fin_two,hc,hd]
  have hfinite (z : ℂ) : M • (z : Sphere) =
      (((M 0 0 * z + M 0 1) / M 1 1 : ℂ) : Sphere) := by
    rw [OnePoint.smul_some_eq_ite]
    simp only [hc,zero_mul,zero_add,ite_eq_right hd]
  let R : ℂ → ℂ := fun z => (M 0 0 * z + M 0 1) / M 1 1 - z
  have hR : Differentiable ℂ R := by
    dsimp only [R]
    fun_prop
  have ht : Tendsto R (Filter.cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    have hh := principal_remainder_tendsto_zero hnorm.2
    simpa only [hfinite,finiteCoord_coe] using hh
  have hzero := hR.eq_const_of_tendsto_cocompact ht
  intro p
  cases p using OnePoint.rec with
  | infty => exact hnorm.1
  | coe z =>
    rw [hfinite]
    apply congrArg ((↑) : ℂ → Sphere)
    have hz : R z = 0 := congrFun hzero z
    exact sub_eq_zero.mp hz

end CircleDomainRigidity

end

end OAI
