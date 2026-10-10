import OAI.Geometry.RCD.Metric.FiniteSignedRadon
import OAI.Geometry.RCD.Metric.SignedSourceWeight

namespace OAI

/-! # Radon–Nikodym densities of weighted full signed sources -/

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [SigmaFinite μ]

omit [TopologicalSpace X] [BorelSpace X] [SigmaFinite μ] in
theorem signed_rnDeriv_toSignedMeasure (ν : Measure X) [IsFiniteMeasure ν] :
    ν.toSignedMeasure.rnDeriv μ =ᵐ[μ] fun x => (ν.rnDeriv μ x).toReal := by
  let j : JordanDecomposition X := ⟨ν,0,Measure.MutuallySingular.zero_right⟩
  have hj : ν.toSignedMeasure.toJordanDecomposition=j := by
    apply SignedMeasure.toJordanDecomposition_eq
    simp only [j,JordanDecomposition.toSignedMeasure,Measure.toSignedMeasure_zero,sub_zero]
  filter_upwards [Measure.rnDeriv_zero μ] with x hx
  change (ν.toSignedMeasure.toJordanDecomposition.posPart.rnDeriv μ x).toReal-
    (ν.toSignedMeasure.toJordanDecomposition.negPart.rnDeriv μ x).toReal = _
  rw [hj]
  change (ν.rnDeriv μ x).toReal-((0 : Measure X).rnDeriv μ x).toReal = _
  rw [hx]
  simp only [Pi.zero_apply,ENNReal.toReal_zero,sub_zero]

theorem signed_rnDeriv_bounded_density (ν : Measure X) [IsFiniteMeasure ν] (χ : X →ᵇ ℝ) :
    SignedMeasure.rnDeriv (ν.withDensityᵥ (χ : X → ℝ)) μ =ᵐ[μ]
      fun x => χ x*(ν.rnDeriv μ x).toReal := by
  have hχ : Integrable (χ : X → ℝ) ν := Integrable.of_bound χ.continuous.aestronglyMeasurable
    ‖χ‖ (Eventually.of_forall χ.norm_coe_le_norm)
  let νp := ν.withDensity (fun x => ENNReal.ofReal (χ x))
  let νn := ν.withDensity (fun x => ENNReal.ofReal (-χ x))
  let : IsFiniteMeasure νp := isFiniteMeasure_withDensity_ofReal hχ.2
  let : IsFiniteMeasure νn := isFiniteMeasure_withDensity_ofReal hχ.neg.2
  have hrep : ν.withDensityᵥ (χ : X → ℝ)=νp.toSignedMeasure-νn.toSignedMeasure :=
    withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hχ
  rw [hrep]
  have hp := Measure.rnDeriv_withDensity_left (μ := ν) (ν := μ)
    (f := fun x => ENNReal.ofReal (χ x)) (by fun_prop)
    (Eventually.of_forall fun x => ENNReal.ofReal_ne_top)
  have hn := Measure.rnDeriv_withDensity_left (μ := ν) (ν := μ)
    (f := fun x => ENNReal.ofReal (-χ x)) (by fun_prop)
    (Eventually.of_forall fun x => ENNReal.ofReal_ne_top)
  filter_upwards [SignedMeasure.rnDeriv_sub νp.toSignedMeasure νn.toSignedMeasure μ,
    signed_rnDeriv_toSignedMeasure μ νp,signed_rnDeriv_toSignedMeasure μ νn,hp,hn]
    with x hs hsp hsn hpr hnr
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hsp,hsn,hpr,hnr]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal']
  by_cases h0 : 0≤χ x
  · rw [max_eq_left h0,max_eq_right (neg_nonpos.mpr h0)]
    ring
  · rw [max_eq_right (le_of_not_ge h0),max_eq_left (le_of_lt (neg_pos.mpr (lt_of_not_ge h0)))]
    ring

theorem signed_rnDeriv_sourceWeight (ν : SignedMeasure X) (χ : X →ᵇ ℝ) :
    (signedSourceWeight ν χ).rnDeriv μ =ᵐ[μ] fun x => χ x*ν.rnDeriv μ x := by
  rw [signedSourceWeight]
  filter_upwards [SignedMeasure.rnDeriv_sub
    (ν.toJordanDecomposition.posPart.withDensityᵥ (χ : X → ℝ))
    (ν.toJordanDecomposition.negPart.withDensityᵥ (χ : X → ℝ)) μ,
    signed_rnDeriv_bounded_density μ ν.toJordanDecomposition.posPart χ,
    signed_rnDeriv_bounded_density μ ν.toJordanDecomposition.negPart χ] with x hs hp hn
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hp,hn]
  change _ = χ x*((ν.toJordanDecomposition.posPart.rnDeriv μ x).toReal-
    (ν.toJordanDecomposition.negPart.rnDeriv μ x).toReal)
  ring

end RegularPointCoordinates

end

end OAI
