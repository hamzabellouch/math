import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAnnularL2

namespace OAI

/-! The actual compact forcing is an entire global L2-valued family,
via the bounded transport from its fixed radial profile space. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def cubicThetaForcingL2 (s : ℂ) : CubicThetaGlobalL2 :=
  cubicThetaGlobalMass (cubicThetaForcingTest s)

lemma cubicThetaForcingL2_profile (s : ℂ) :
    cubicThetaForcingL2 s=cubicThetaAnnularL2 (cubicThetaForcingProfile s) := by
  apply Lp.ext
  filter_upwards [(cubicThetaSectionRepresentative_memLp (cubicThetaForcingTest s)).coeFn_toLp,
    (cubicThetaAnnularRepresentative_memLp (cubicThetaForcingProfile s)).coeFn_toLp]
    with q h₁ h₂
  change (cubicThetaForcingL2 s) q=_ at h₁
  change (cubicThetaAnnularL2 (cubicThetaForcingProfile s)) q=_ at h₂
  rw [h₁,h₂]
  exact (cubicThetaAnnularSeries_forcing s (cubicThetaBorelSection q)).symm

theorem cubicThetaForcingL2_analytic (s : ℂ) : AnalyticAt ℂ cubicThetaForcingL2 s := by
  have h := cubicThetaAnnularL2.analyticAt (cubicThetaForcingProfile s) |>.comp
    (f:=cubicThetaForcingProfile) (x:=s) (cubicThetaForcingProfile_analytic s)
  have he : cubicThetaForcingL2=cubicThetaAnnularL2 ∘ cubicThetaForcingProfile :=
    funext cubicThetaForcingL2_profile
  rwa [he]

end CubicFirstMoment

end

end OAI
