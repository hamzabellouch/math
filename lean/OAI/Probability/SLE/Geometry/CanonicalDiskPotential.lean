import OAI.Probability.SLE.Angle.TargetDiskMass
import OAI.Probability.SLE.Geometry.CanonicalCompactPotential

namespace OAI

/-! The source-prescribed disk potential is the remaining canonical disk
mass, with exactly the source's Brownian clock normalization. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

def diskScalar (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (t : ℝ≥0) (ω : Ω) : ℝ :=
  compactWeightedMass (Target.diskMassWeight κ θ hθ) (Target.diskSourceHalfPlane θ) (C.process t ω)

def diskTerminalScalar (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (ω : Ω) : ℝ :=
  compactWeightedMass (Target.diskMassWeight κ θ hθ) (Target.diskSourceHalfPlane θ)
    (C.rational.terminal ω)

theorem target_potential_condExp [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hc : ∀ ω, Continuous (fun t => B t ω))
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (b : Ω → Target.Driver)
    (hU : ∀ ω (s : ℝ), 0 ≤ s → Real.sqrt κ*B s.toNNReal ω=Target.driverValue (b ω) (κ*s))
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (t : ℝ≥0) :
    (fun ω => (Target.potential κ θ (b ω) (κ*t)).toReal) =ᵐ[P]
      P[C.diskTerminalScalar θ hθ-C.diskScalar θ hθ t |
        (Filtration.natural B (fun r =>
          (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) t] := by
  have he (ω : Ω) : (Target.potential κ θ (b ω) (κ*t)).toReal =
      compactWeightedMass (Target.diskMassWeight κ θ hθ) (Target.diskSourceHalfPlane θ)
        (halfPlaneGreenMeasure κ B γ G t ω) := by
    exact Target.potential_toReal_eq_compactWeightedMass κ hκ (b ω) _ ((hc ω).const_mul _)
      (γ ω) (G ω) (F ω) (hw ω) (hU ω) θ hθ t
  have heAE : (fun ω => (Target.potential κ θ (b ω) (κ*t)).toReal) =ᵐ[P]
      (fun ω => compactWeightedMass (Target.diskMassWeight κ θ hθ)
        (Target.diskSourceHalfPlane θ) (halfPlaneGreenMeasure κ B γ G t ω)) :=
    Eventually.of_forall he
  exact heAE.trans (C.compact_potential_condExp hc F hw _ _
    (Target.diskSourceHalfPlane_compact hθ) t)

include hBm in
theorem target_potential_lintegral_ne_top
    (hB : IsBrownianReal B P) (hκ : 0 < κ) (hκ8 : κ<8)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (b : Ω → Target.Driver)
    (hU : ∀ ω (s : ℝ), 0 ≤ s → Real.sqrt κ*B s.toNNReal ω=Target.driverValue (b ω) (κ*s))
    (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi) (t : ℝ≥0) :
    (∫⁻ ω, Target.potential κ θ (b ω) (κ*t) ∂P) ≠ ∞ := by
  have he (ω : Ω) := Target.potential_eq_weighted_green κ hκ (b ω) _ ((hc ω).const_mul _)
    (γ ω) (G ω) (F ω) (hw ω) (hU ω) θ hθ t
  simp_rw [he]
  apply compactWeightedMass_kernel_lintegral_ne_top P κ (halfPlaneGreenMeasure κ B γ G t)
    (halfPlaneGreenMeasure_measurable hBm hc κ γ G F hw t)
    (by simpa only [Measure.restrict_univ] using
      halfPlaneGreenMeasure_mean_le hB hBm hc h0 hκ hκ8 γ G F hw t univ)
    _ _ (Target.diskSourceHalfPlane_compact hθ)

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
