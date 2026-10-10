import OAI.Probability.SLE.Loewner.TargetContinuationPullback
import OAI.Probability.SLE.Mass.NormalizedDiskCompensator
import OAI.Probability.SLE.Angle.TargetPotentialMeasurability
import OAI.Probability.SLE.Mass.TargetDiscreteMassRecovery

namespace OAI

/-! The exact prescribed potential increments are the predictable
increments of the actual canonical disk mass on the normalized clock. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

theorem normalized_potentialDifference_eq_increment
    (hB : IsBrownianReal B P) (hκ : 0<κ) (hκ8 : κ<8)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (n i : ℕ) :
    (fun ω => Target.potentialDifference κ θ W (Target.normalizedDriver κ B hc h0 ω) n i) =ᵐ[P]
      condExp (compensatorMeshFiltration (Target.normalizedFiltration κ B
        (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r))) hc h0) n i) P
        (meshMassIncrement (C.normalizedDiskScalar θ hθ) n i) := by
  let b := Target.normalizedDriver κ B hc h0
  have hm (t : ℝ≥0) : Measurable (B t) := hBm.comp (measurable_const.prodMk measurable_id)
  let ℱ := Target.normalizedFiltration κ B hm hc h0
  let A := C.normalizedDiskScalar θ hθ
  let V (i : ℕ) (ω : Ω) := (Target.potential κ θ (b ω) (compensatorMeshTime n i)).toReal
  have hq := Target.potentialDifference_comp_eq_current_sub_condExp b
    (Target.normalizedDriver_measurable κ B hm hc h0)
    (Target.normalizedDriver_isBrownian κ hκ B hB hc h0) W
    (Target.normalizedDriver_law κ hκ B hB hm hc h0 W hW) κ θ n i
    (fun j => Target.measurable_potential κ θ (compensatorMeshTime n j))
    (fun j => normalized_potential_lintegral_ne_top (hBm := hBm)
      hB hκ hκ8 hc h0 F hw θ hθ (compensatorMeshTime n j))
  have hA : StronglyAdapted (compensatorMeshFiltration ℱ n)
      (fun j => A (compensatorMeshTime n j)) :=
    fun j => C.normalizedDiskScalar_stronglyAdapted hκ hc h0 θ hθ _
  have hV (j : ℕ) : V j =ᵐ[P]
      P[C.diskTerminalScalar θ hθ-A (compensatorMeshTime n j) |
        compensatorMeshFiltration ℱ n j] :=
    C.normalized_potential_condExp hκ hc h0 F hw θ hθ (compensatorMeshTime n j)
  exact hq.trans (remainingPotential_increment P (compensatorMeshFiltration ℱ n)
    (fun j => A (compensatorMeshTime n j)) V (C.diskTerminalScalar θ hθ) hA
    (fun j => C.normalizedDiskScalar_integrable θ hθ (compensatorMeshTime n j))
    ((C.compactWeightedMass_terminal_memLp _ _
      (Target.diskSourceHalfPlane_compact hθ)).integrable one_le_two) hV i)

theorem normalized_discreteMass_tendstoInMeasure
    (hB : IsBrownianReal B P) (hκ : 0<κ) (hκ8 : κ<8)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    TendstoInMeasure P
      (fun n ω => Target.discreteMass κ θ W (Target.normalizedDriver κ B hc h0 ω) ℓ n) atTop
      (fun ω => massAtExtendedTime (fun t => C.normalizedDiskScalar θ hθ t ω)
        (C.diskTerminalScalar θ hθ ω)
        (Target.levelTime κ θ (Target.normalizedDriver κ B hc h0 ω) ℓ)) := by
  exact target_discreteMass_tendstoInMeasure P κ θ W (Target.normalizedDriver κ B hc h0) ℓ
    (compensatorMeshFiltration (Target.normalizedFiltration κ B
      (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r))) hc h0))
    (C.normalizedDiskScalar θ hθ) (C.diskTerminalScalar θ hθ)
    (C.normalizedDiskScalar_measurable θ hθ)
    (fun n i => C.normalizedDiskScalar_stronglyAdapted hκ hc h0 θ hθ _)
    (C.compactWeightedMass_terminal_memLp _ _ (Target.diskSourceHalfPlane_compact hθ))
    (C.normalizedDiskScalar_paths hκ θ hθ)
    (normalized_levelTime_measurable (hBm := hBm) hκ hc h0 F hw θ ℓ hℓ)
    (C.normalized_potentialDifference_eq_increment hB hκ hκ8 hc h0 F hw W hW θ hθ)

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
