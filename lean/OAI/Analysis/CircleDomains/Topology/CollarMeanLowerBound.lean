import OAI.Analysis.CircleDomains.Topology.OrderedCollarLift
import OAI.Analysis.CircleDomains.Sobolev.SmoothMeanCircuit

namespace OAI

/-! The boundary lower bound on an actual smooth inward collar. The
orientation-normalized circuit is used to evaluate the mean, and its
absolute integral is then returned to the original positive circuit. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem OrderedCollarLift.mean_boundary_lower_bound
    {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F)
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    [NullSingletonClass (compactArcStartingAngleLaw K η : Measure UnitAddCircle)]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ σ > 0, σ < D.width ∧ ∀ ρ ∈ Ioc (0 : ℝ) σ,
      ∀ (O : Set ℂ), IsOpen O → ∀ (w : ℂ → UnitAddCircle), SmoothCircleOn w O →
      (∀ t, D.circuit ρ t ∈ O) →
      (∀ t, ∀ᵐ α : K ∂(η : Measure K), F (D.circuit ρ t : Sphere) ∉ range α.val) →
      ∀ (R : ℂ → ℝ), Continuous (R ∘ D.circuit ρ) →
      (∀ t, w (D.circuit ρ t) = diskMeanCircle hsch K hKS η (F (D.circuit ρ t : Sphere)) +
        (R (D.circuit ρ t) : UnitAddCircle)) →
      (∀ t ∈ Icc (0 : ℝ) 1, |R (D.circuit ρ t)| ≤ ε) →
      ∀ (Φ : ℂ → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) Φ O →
      ∀ c : ℝ, (∀ᵐ θ : UnitAddCircle ∂(compactArcStartingAngleLaw K η : Measure UnitAddCircle),
        c ≤ Φ (D.circuit ρ (D.angle.symm (unitCircleCut θ)))) →
      c ≤ |circleFormIntegral Φ w (C.curve ρ)| +
        (2 * ε) * ∫ t in (0 : ℝ)..1, |deriv (Φ ∘ D.circuit ρ) t| := by
  obtain ⟨δ, hδ, hbound⟩ := mean_circuit_integral_lower_bound hsch hsep K hK hKS η
    D.angle D.angle_zero D.angle_one hε
  obtain ⟨σ, hσ, hσw, hnear⟩ := D.approach δ hδ
  refine ⟨σ / 2, half_pos hσ, (half_lt_self hσ).trans hσw, ?_⟩
  intro ρ hρ O hO w hw hc hm R hR hv hRb Φ hΦ c hpositive
  have hρw : ρ ∈ Ioo (-D.width) D.width :=
    ⟨by linarith [D.width_pos, hρ.1], by linarith [hρ.2]⟩
  have hρC : ρ ∈ Icc (0 : ℝ) C.width :=
    ⟨hρ.1.le, hρw.2.le.trans D.width_le⟩
  have hp (t : ℝ) : diskRayProjection (D.lift (ρ, t)).val = F (D.circuit ρ t : Sphere) := by
    simpa only [abs_of_pos hρ.1, OrderedCollarLift.circuit, Function.comp_apply] using
      D.projects (ρ, t) ⟨hρw, mem_univ _⟩
  have hb := hbound (fun t => D.lift (ρ, t)) (D.continuous_slice hρw)
    (fun t => by simpa only [hp t] using hm t) (D.period ρ hρw)
    O hO w hw (D.circuit ρ) (D.circuit_smooth hρC) hc (D.circuit_periodic hρC).eq
    R hR (fun t => by simpa only [hp t] using hv t) hRb
    (hnear ρ ⟨by linarith [hρ.1], by linarith [hρ.2]⟩)
    Φ hΦ c hpositive
  calc
    c ≤ circleFormIntegral Φ w (D.circuit ρ) +
        (2 * ε) * ∫ t in (0 : ℝ)..1, |deriv (Φ ∘ D.circuit ρ) t| := hb
    _ ≤ |circleFormIntegral Φ w (D.circuit ρ)| +
        (2 * ε) * ∫ t in (0 : ℝ)..1, |deriv (Φ ∘ D.circuit ρ) t| :=
      add_le_add (le_abs_self _) le_rfl
    _ = _ := by rw [D.abs_circleFormIntegral hρC Φ w]

end CircleDomainRigidity

end

end OAI
