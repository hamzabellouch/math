import OAI.Geometry.RCD.Sobolev.LocalEnergyMeasure
import OAI.Geometry.RCD.Coordinates.NormalizedLawCompression

namespace OAI

/-! # The exact normalized domination of a local energy measure -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem normalized_local_energy_le (w : SobolevSpace μ hQ) {A U : Set X}
    (hAU : A⊆U) [IsFiniteMeasure (μ.restrict U)] (hfin : μ U≠⊤)
    (hpos : 0<μ.real U) (r M : ℝ) (hM : 0≤M)
    (hb : ∀ᵐ x ∂μ.restrict A, r^2*localGamma μ hQ w w x≤M) :
    (localEnergyMeasure μ hQ w A (r^2/μ.real U) : Measure X)≤
      ENNReal.ofReal M • (normalizedProbabilityLaw (μ.restrict U) : Measure X) := by
  have hμ : μ.restrict U≠0 := by
    intro he
    have hh := congrArg (fun ν : Measure X => ν.real univ) he
    simp only [Measure.real,Measure.restrict_apply_univ,Measure.coe_zero,Pi.zero_apply,
      ENNReal.toReal_zero] at hh
    exact hpos.ne' hh
  rw [normalizedProbabilityLaw_measure _ hμ,Measure.restrict_apply_univ,smul_smul]
  have he : ENNReal.ofReal (M/μ.real U)=ENNReal.ofReal M*(μ U)⁻¹ := by
    rw [div_eq_mul_inv,ENNReal.ofReal_mul hM,ENNReal.ofReal_inv_of_pos hpos,
      show ENNReal.ofReal (μ.real U)=μ U from ENNReal.ofReal_toReal hfin]
  rw [← he]
  have hbound := localEnergyMeasure_le μ hQ w A (r^2/μ.real U) (M/μ.real U) (by
    filter_upwards [hb] with x hx
    calc (r^2/μ.real U)*localGamma μ hQ w w x=(r^2*localGamma μ hQ w w x)/μ.real U := by ring
      _ ≤ M/μ.real U := div_le_div_of_nonneg_right hx hpos.le)
  apply hbound.trans
  intro B
  simpa only [Measure.smul_apply,smul_eq_mul] using
    mul_le_mul' (le_refl (ENNReal.ofReal (M/μ.real U))) ((Measure.restrict_mono hAU le_rfl) B)

end RegularPointCoordinates

end

end OAI
