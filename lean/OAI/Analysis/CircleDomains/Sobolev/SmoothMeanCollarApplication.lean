import OAI.Analysis.CircleDomains.Sobolev.SmoothCollarLowerBound
import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanPeriodData

namespace OAI

/-! Apply the physical collar estimate to the actual smoothed mean-period
data. The correction's continuity and the physical value formula come
from the construction; no separate smooth circuit is assumed. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_smooth_mean_collar_lower_bound
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    [NullSingletonClass (compactArcStartingAngleLaw K η : Measure UnitAddCircle)]
    (G U S M : Set Sphere) (hG : IsOpen G) (hS : IsOpen S) (b : Sphere)
    (π : Sphere → Sphere) (hπ : Continuous π) (hπU : ∀ x ∈ G, π x ∈ U)
    (F : C(Sphere, ℂ))
    {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H}
    (D : OrderedCollarLift C (F.comp ⟨π, hπ⟩))
    (O : Set ℂ) (hO : IsOpen O) (hCO : frontier (jordanInterior H) ⊆ O)
    (Φ : ℂ → ℝ) (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ O)
    {d : ℝ} (hd : 0 < d)
    (hgate : ∀ᵐ θ : UnitAddCircle ∂(compactArcStartingAngleLaw K η : Measure UnitAddCircle),
      d ≤ Φ (D.circuit 0 (D.angle.symm (unitCircleCut θ)))) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ σ > 0, σ < D.width ∧ ∀ ρ ∈ Ioc (0 : ℝ) σ,
      ∀ Q : SmoothMeanPeriodData hsch K hKS η F G U S M b π,
      (∀ x, |Q.error x| ≤ ε) →
      (∀ t, (D.circuit ρ t : Sphere) ∈ G ∧ π (D.circuit ρ t : Sphere) ∈ S) →
      (∀ t, ∀ᵐ α : K ∂(η : Measure K), F (π (D.circuit ρ t : Sphere)) ∉ range α.val) →
      d / 2 < |circleFormIntegral Φ Q.physical (C.curve ρ)| := by
  obtain ⟨ε, hε, hε1, σ, hσ, hσw, hbound⟩ :=
    D.exists_strict_mean_lower_bound hsch hsep K hK hKS η O hO hCO Φ hΦ hd hgate
  refine ⟨ε, hε, hε1, σ, hσ, hσw, ?_⟩
  intro ρ hρ Q herror hcurve hmiss
  let W : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' G ∩ (fun z : ℂ => π (z : Sphere)) ⁻¹' S
  have hW : IsOpen W := (hG.preimage OnePoint.continuous_coe).inter
    (hS.preimage (hπ.comp OnePoint.continuous_coe))
  have hρC : ρ ∈ Icc (0 : ℝ) C.width :=
    ⟨hρ.1.le, hρ.2.trans (hσw.le.trans D.width_le)⟩
  have hRc : Continuous (fun t => Q.error (π (D.circuit ρ t : Sphere))) := by
    apply Q.error_continuous.comp_continuous
      (hπ.comp (OnePoint.continuous_coe.comp (D.circuit_smooth hρC).continuous))
    intro t
    exact ⟨hπU _ (hcurve t).1, (hcurve t).2⟩
  exact hbound ρ hρ W hW Q.physical Q.physical_smooth hcurve hmiss
    (fun z => Q.error (π (z : Sphere))) hRc
    (fun t => Q.physical_value _ (hcurve t).1 (hcurve t).2)
    (fun t _ => herror _)

end CircleDomainRigidity

end

end OAI
