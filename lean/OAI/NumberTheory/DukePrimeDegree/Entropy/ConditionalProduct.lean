import OAI.NumberTheory.PrimePackets.ZeroSeparation

namespace OAI

/-!
# Product structure from equal normalized real conditionals

This is the finite-rectangle step of Einsiedler--Katok (2003), Lemma 8.2.
A common conditional measure, even if initially specified only up to a
scalar on each fiber, forces a genuine product measure after normalization.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Equal normalized conditionals on the real factor force a product. -/
theorem eq_prod_of_constant_real_conditionals {B : Type*} [MeasurableSpace B]
    (μ : Measure (B × ℝ)) [IsFiniteMeasure μ]
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (h : ∀ᵐ x ∂μ.fst, μ.condKernel x = ν) :
    μ = μ.fst.prod ν := by
  have h' : μ.condKernel =ᵐ[μ.fst] Kernel.const B ν := h
  calc
    μ = μ.fst ⊗ₘ μ.condKernel := (Measure.disintegrate μ μ.condKernel).symm
    _ = μ.fst ⊗ₘ Kernel.const B ν := Measure.compProd_congr h'
    _ = μ.fst.prod ν := Measure.compProd_const

/-- Projectively equal conditional measures become exactly equal after
normalizing their common model. The only scalar left is the marginal. -/
theorem eq_prod_of_projective_real_conditionals {B : Type*} [MeasurableSpace B]
    (μ : Measure (B × ℝ)) [IsFiniteMeasure μ]
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν univ ≠ 0)
    (h : ∀ᵐ x ∂μ.fst, ∃ c : ℝ≥0∞, μ.condKernel x = c • ν) :
    μ = μ.fst.prod (anchorNormalize ν univ) := by
  let : IsFiniteMeasure (anchorNormalize ν univ) := by
    constructor
    change (ν univ)⁻¹ * ν univ < ∞
    rw [ENNReal.inv_mul_cancel hν (measure_ne_top ν univ)]
    exact ENNReal.one_lt_top
  apply eq_prod_of_constant_real_conditionals μ (anchorNormalize ν univ)
  filter_upwards [h] with x hx
  obtain ⟨c, hc⟩ := hx
  have hmass : c * ν univ = 1 := by
    have H := congrArg (fun ρ : Measure ℝ => ρ univ) hc
    simpa only [Measure.smul_apply, smul_eq_mul, measure_univ] using H.symm
  have heq : c = (ν univ)⁻¹ := by
    calc
      c = c * (ν univ * (ν univ)⁻¹) := by
        rw [ENNReal.mul_inv_cancel hν (measure_ne_top ν univ), mul_one]
      _ = (c * ν univ) * (ν univ)⁻¹ := (mul_assoc _ _ _).symm
      _ = (ν univ)⁻¹ := by rw [hmass, one_mul]
  simpa only [heq, anchorNormalize] using hc

end DukePrimeDegree

end

end OAI
