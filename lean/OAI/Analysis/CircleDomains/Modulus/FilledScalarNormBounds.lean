import OAI.Analysis.CircleDomains.Sobolev.FilledScalarL2
import OAI.Analysis.CircleDomains.Sobolev.SphericalGradientEnergyNorm

namespace OAI

/-! Uniform norm bounds for the actual bounded scalar fillings and their
two L² differential components. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem HoleFilling.filled_norm_bound {i : Fin m} {n : ℕ} (F : R.HoleFilling i n)
    {μ : Measure ℂ} [IsFiniteMeasure μ] :
    ‖(F.filled_memLp (p := 2) (μ := μ)).toLp F.filled‖ ≤
      (measureUnivNNReal μ : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹ := by
  have h := F.filled_memLp (p := 2) (μ := μ)
  have hb : ∀ᵐ z ∂μ, ‖h.toLp F.filled z‖ ≤ (1 : ℝ) := by
    filter_upwards [h.coeFn_toLp] with z hz
    rw [hz, Real.norm_eq_abs, abs_of_nonneg (F.filled_mem z).1]
    exact (F.filled_mem z).2
  simpa only [mul_one] using Lp.norm_le_of_ae_bound zero_le_one hb

 theorem eventually_filled_partial_norm_bounds (i : Fin m) :
    ∀ᶠ n in atTop, ∀ F : R.HoleFilling i n,
      ∃ h₁ : MemLp (fun z => fderiv ℝ F.filled z 1) 2 volume,
      ∃ h₂ : MemLp (fun z => fderiv ℝ F.filled z Complex.I) 2 volume,
      ‖h₁.toLp (fun z => fderiv ℝ F.filled z 1)‖ ≤ Real.sqrt
        ((∫ x in realChartDomain d.physicalDomain,
          gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x) + 1) ∧
      ‖h₂.toLp (fun z => fderiv ℝ F.filled z Complex.I)‖ ≤ Real.sqrt
        ((∫ x in realChartDomain d.physicalDomain,
          gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x) + 1) := by
  filter_upwards [R.eventually_filled_global_energy i, R.eventually_filled_partials_memLp i]
    with n he hp F
  obtain ⟨h₁, h₂⟩ := hp F
  have heps : modelError n ≤ 1 := by
    rw [modelError]
    apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hsq₁ : (∫ z, (fderiv ℝ F.filled z 1) ^ 2) ≤ ∫ z, euclideanGradientEnergy F.filled z :=
    integral_mono h₁.integrable_sq (he F).1 (fun z => le_add_of_nonneg_right (sq_nonneg _))
  have hsq₂ : (∫ z, (fderiv ℝ F.filled z Complex.I) ^ 2) ≤ ∫ z, euclideanGradientEnergy F.filled z :=
    integral_mono h₂.integrable_sq (he F).1 (fun z => le_add_of_nonneg_left (sq_nonneg _))
  refine ⟨h₁, h₂, ?_, ?_⟩
  · apply Real.le_sqrt_of_sq_le
    rw [Lp.norm_toLp, ← integral_sq_eq_eLpNorm_toReal_sq h₁]
    exact hsq₁.trans ((he F).2.le.trans (add_le_add le_rfl heps))
  · apply Real.le_sqrt_of_sq_le
    rw [Lp.norm_toLp, ← integral_sq_eq_eLpNorm_toReal_sq h₂]
    exact hsq₂.trans ((he F).2.le.trans (add_le_add le_rfl heps))

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
