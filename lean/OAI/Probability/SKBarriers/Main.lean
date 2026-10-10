import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyRegularity
import OAI.Probability.SKBarriers.Scalar.RegularAlgebra
import OAI.Probability.SKBarriers.Calculus.ParameterWeakGrowth
import OAI.Probability.SKBarriers.Calculus.ParameterRecursion
import OAI.Probability.SKBarriers.Calculus.ParameterProduct
import OAI.Probability.SKBarriers.Calculus.ParameterAverage
import OAI.Probability.SKBarriers.Calculus.ParameterFieldMap
import OAI.Probability.SKBarriers.SpinGlass.SpinPressureCurve
import OAI.Probability.SKBarriers.Coverage.EnergyGap
import OAI.Probability.SKBarriers.Dynamics.ClockAsymptotic
import OAI.Probability.SKBarriers.Dynamics.ConflictPacking
import OAI.Probability.SKBarriers.Locking.TentError
import OAI.Probability.SKBarriers.Scalar.ScalarTemperature
import OAI.Probability.SKBarriers.SpinGlass.FiniteSampling
import OAI.Probability.SKBarriers.Parisi.CDFTimeContinuity
import OAI.Probability.SKBarriers.Hierarchy.TimeChainExactPenalty
import OAI.Probability.SKBarriers.Hierarchy.TimeChainOnAnalytic
import OAI.Probability.SKBarriers.Parisi.CDFSupportGap
import OAI.Probability.SKBarriers.Locking.NarrowTimeAnalytic
import OAI.Probability.SKBarriers.Locking.NarrowBlockPenalty
import OAI.Probability.SKBarriers.Replicas.TripleTimeAnalytic
import OAI.Probability.SKBarriers.Dynamics.ForbiddenInterval
import OAI.Probability.SKBarriers.Locking.LockingScales
import OAI.Probability.SKBarriers.Dynamics.ForbiddenMain

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK

theorem main (β : ℝ) (hβ : 1<β) :
    Tendsto (continuousBadMass β) atTop (𝓝 1) ∧
      Tendsto (discreteBadMass β) atTop (𝓝 1) := by
  have hβ0 : 0<β := zero_lt_one.trans hβ
  obtain ⟨q,hq,hq1,Hcov⟩ := Analytic.stretched_uniform_coverage hβ
  obtain ⟨b,hb,hb1,Hb⟩ := Analytic.signed_small_scale hβ0 hq hq1.le zero_lt_one
  obtain ⟨b',hb',hb'b,Hb'⟩ := Analytic.signed_small_scale hβ0 hb hb1.le hb
  obtain ⟨t,ht,ht1,htpack,htb,htb',htq⟩ := Analytic.choose_dynamics_scale hq hb hb'
  obtain ⟨μ,hμ,hmin,h0,hH,hA,hstrict,hS⟩ := Analytic.exists_scalarCDFParisi_minimizer_locking_data hβ0.ne'
  by_cases hΓ : ∀r∈Ioo (t/2) (3*t),Analytic.scalarCDFOverlap β (cdf (μ : Measure ℝ)) r=r
  · have Hnarrow := Analytic.narrow_annulus_locking hβ0 ht ht1 μ hμ hmin h0 hS hΓ
    have Hstatic := Analytic.lockingUnion_annealed_bound β μ t q b b' Hb Hb' Hnarrow
    exact Analytic.identity_main_of_static_locking β μ ht hb htpack htb htb' (by linarith only [htq,ht]) Hcov Hstatic
  · have Hcont := Analytic.scalarCDFOverlap_continuousOn β (cdf (μ : Measure ℝ))
      (fun x => ⟨cdf_nonneg _ _,cdf_le_one _ _⟩) (Analytic.supported_probability_cdf_one μ hμ)
    obtain ⟨a₀,a₁,d,ha₀,ha,ha₁,hd,Hd⟩ := Analytic.exists_forbidden_interval Hcont (half_pos ht).le ht1.le hΓ
    have ha₀0 : 0<a₀ := (half_pos ht).trans ha₀
    have Hstatic := Analytic.pairStrip_annealed_bound hβ0 μ hμ hmin ha₀0.le hd Hd
    exact Analytic.forbidden_main_of_static_gap β ha₀0 ha (ha₁.trans htq) Hcov Hstatic

end SK

end
end

end OAI
