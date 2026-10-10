import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergyInverseContinuation

namespace OAI

/-! The energy inverse is analytic off the positive real spectral ray,
and meromorphic across its part strictly below the cusp threshold two. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma cubicThetaEnergyMass_positive : cubicThetaEnergyMass.IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self cubicThetaGlobalInclusion

lemma cubicThetaEnergyMass_norm : ‖cubicThetaEnergyMass‖≤1 := by
  rw [cubicThetaEnergyMass,ContinuousLinearMap.norm_adjoint_comp_self]
  exact (mul_le_mul cubicThetaGlobalInclusion_norm cubicThetaGlobalInclusion_norm
    cubicThetaGlobalInclusion.opNorm_nonneg zero_le_one).trans_eq (one_mul 1)

lemma cubicThetaEnergyPencil_unit {z : ℂ} (hz : z.im≠0 ∨ z.re<1) :
    IsUnit (cubicThetaEnergyPencil z) :=
  cubicThetaPositiveContraction_unit cubicThetaEnergyMass cubicThetaEnergyMass_positive
    cubicThetaEnergyMass_norm hz

lemma cubicThetaEnergyInverse_analytic {z : ℂ} (hz : z.im≠0 ∨ z.re<1) :
    AnalyticAt ℂ (fun w => Ring.inverse (cubicThetaEnergyPencil w)) z := by
  have hu := cubicThetaEnergyPencil_unit hz
  have hi : AnalyticAt ℂ Ring.inverse (cubicThetaEnergyPencil z) := by
    convert analyticAt_inverse (𝕜:=ℂ)
      (A:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace) hu.unit using 1
    exact hu.unit_spec
  exact hi.comp (f:=cubicThetaEnergyPencil) (x:=z) (cubicThetaEnergyPencil_analytic z)

theorem cubicThetaEnergyInverse_meromorphic {z : ℂ} (hz : z.im≠0 ∨ z.re<2) :
    MeromorphicAt (fun w => Ring.inverse (cubicThetaEnergyPencil w)) z := by
  by_cases hr : z.im≠0 ∨ z.re<1
  · exact (cubicThetaEnergyInverse_analytic hr).meromorphicAt
  · have him : z.im=0 := not_not.mp (not_or.mp hr).1
    have hre : 1≤z.re := le_of_not_gt (not_or.mp hr).2
    have hlt : z.re<2 := hz.resolve_left (fun h => h him)
    have he : (z.re:ℂ)=z := Complex.ext rfl (by simpa only [Complex.ofReal_im] using him.symm)
    rw [← he]
    exact cubicThetaEnergyInverse_meromorphic_real (by linarith) hlt

lemma cubicThetaEnergyPencil_eventually_unit {z : ℂ} (hz : z.im≠0 ∨ z.re<2) :
    ∀ᶠ w : ℂ in 𝓝[≠] z, IsUnit (cubicThetaEnergyPencil w) := by
  by_cases hr : z.im≠0 ∨ z.re<1
  · have hn : {A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace | IsUnit A} ∈
        𝓝 (cubicThetaEnergyPencil z) :=
      (Units.isOpen (R:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace)).mem_nhds
        (cubicThetaEnergyPencil_unit hr)
    exact nhdsWithin_le_nhds ((cubicThetaEnergyPencil_analytic z).continuousAt.eventually hn)
  · have him : z.im=0 := not_not.mp (not_or.mp hr).1
    have hre : 1≤z.re := le_of_not_gt (not_or.mp hr).2
    have hlt : z.re<2 := hz.resolve_left (fun h => h him)
    have he : (z.re:ℂ)=z := Complex.ext rfl (by simpa only [Complex.ofReal_im] using him.symm)
    rw [← he]
    exact cubicThetaEnergyPencil_unit_near_real (by linarith) hlt

end CubicFirstMoment

end

end OAI
