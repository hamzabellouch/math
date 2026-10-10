import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.AECertificates
import OAI.Analysis.BiholderTransport.Calculus.TaylorPositivity
import OAI.Analysis.BiholderTransport.Calculus.LowerTaylorComposition
import OAI.Analysis.BiholderTransport.Coordinates.Endpoint
import OAI.Analysis.BiholderTransport.Calculus.TaylorAlgebra
import OAI.Analysis.BiholderTransport.Coordinates.Stationary
import OAI.Analysis.BiholderTransport.Coordinates.Add
import OAI.Analysis.BiholderTransport.Regularity.FirstActiveLimit
import OAI.Analysis.BiholderTransport.Regularity.CenterPoleStationary
import OAI.Analysis.BiholderTransport.Coordinates.ExpNonconjugateLimit
import OAI.Analysis.BiholderTransport.Regularity.CenterSequenceRegular
import OAI.Analysis.BiholderTransport.Regularity.MaximumReindex
import OAI.Analysis.BiholderTransport.Convexity.ChartJensenFirstLimit
import OAI.Analysis.BiholderTransport.Oscillation.ClassPower

namespace OAI

section

noncomputable section
open MeasureTheory Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport

theorem uniform_biHolder_transport
    {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ, Model n) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, Model n) ∞ (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ, Model n) x)]
    [IsRiemannianManifold 𝓘(ℝ, Model n) M]
    [MeasurableSpace M] [BorelSpace M]
    (hmtw : WeakMTW (n := n) (M := M))
    (lam cap : ℝ) (hlam : 0 < lam) (hcap : lam ≤ cap)
    (hclass : ∃ rho : M → ℝ, AdmissibleDensity (metricVolume n) lam cap rho) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧ 0 ≤ C ∧
      ∀ rho0 rho1 : M → ℝ,
        AdmissibleDensity (metricVolume n) lam cap rho0 →
        AdmissibleDensity (metricVolume n) lam cap rho1 →
        ∃ T : M ≃ₜ M,
          IsOptimalMap (metricVolume n) rho0 rho1 T ∧
          (∀ S : M → M, IsOptimalMap (metricVolume n) rho0 rho1 S →
            S =ᵐ[densityMeasure (metricVolume n) rho0] T) ∧
          BiHolderEstimate alpha C T := by
  classical
  let x0:M:=Classical.choice (inferInstance:Nonempty M)
  exact hmtw.transport_endpoint_of_class_power hlam x0
    (hmtw.class_power (by omega) hlam hcap x0 (densityDualClass_nonempty hlam hclass x0))

end WeakMTWTransport

end
end

end OAI
