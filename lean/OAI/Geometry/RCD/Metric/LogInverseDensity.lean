import OAI.Geometry.RCD.Transport.BoltzmannSupportBounds

namespace OAI

/-! # The expected logarithm of the inverse density is normalized entropy -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem log_inverse_density_integral (μ ν : Measure X) [SigmaFinite μ]
    [IsFiniteMeasure ν] (ha : ν ≪ μ)
    (he : Integrable (fun x => (ν.rnDeriv μ x).toReal*Real.log (ν.rnDeriv μ x).toReal) μ)
    (N : ℝ) :
    Integrable (fun x => Real.log ((ν.rnDeriv μ x)^(-(1/N))).toReal) ν ∧
      (∫ x, Real.log ((ν.rnDeriv μ x)^(-(1/N))).toReal ∂ν)=
        -(boltzmannEntropy μ ν)/N := by
  have hi : Integrable (fun x => Real.log (ν.rnDeriv μ x).toReal) ν :=
    (integrable_toReal_rnDeriv_mul_iff ha).mp he
  have heq : (fun x => Real.log ((ν.rnDeriv μ x)^(-(1/N))).toReal) =ᵐ[ν]
      fun x => (-(1/N))*Real.log (ν.rnDeriv μ x).toReal := by
    filter_upwards [Measure.rnDeriv_pos ha,ha.ae_le (Measure.rnDeriv_lt_top ν μ)] with x hx ht
    rw [←ENNReal.toReal_rpow,Real.log_rpow (ENNReal.toReal_pos hx.ne' ht.ne)]
  refine ⟨(hi.const_mul _).congr heq.symm,?_⟩
  rw [integral_congr_ae heq,integral_const_mul]
  have hlog : (∫ x, Real.log (ν.rnDeriv μ x).toReal ∂ν)=boltzmannEntropy μ ν := by
    exact (integral_rnDeriv_smul (f:=fun x => Real.log (ν.rnDeriv μ x).toReal) ha).symm
  rw [hlog]
  ring

end RegularPointCoordinates

end

end OAI
