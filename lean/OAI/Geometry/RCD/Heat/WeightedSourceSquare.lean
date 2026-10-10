import OAI.Geometry.RCD.Heat.HeatOffDiagonalL2

namespace OAI

/-! # The weighted source square, allowing a vanishing weight

The weight is merely integrable and nonnegative. Its square root realizes
the weighted pairing in the actual L² space.
-/

open MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem weighted_source_square {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {r s : X → ℝ} (hr : Integrable r μ)
    (hr0 : ∀ᵐ x ∂μ, 0≤r x) (hs : AEMeasurable s μ)
    (hrs : Integrable (fun x => r x*(s x)^2) μ) :
    Integrable (fun x => r x*s x) μ ∧
      (∫ x, r x*s x ∂μ)^2≤(∫ x, r x ∂μ)*(∫ x, r x*(s x)^2 ∂μ) := by
  let a := fun x => Real.sqrt (r x)
  let b := fun x => Real.sqrt (r x)*s x
  have ha : AEMeasurable a μ := hr.aemeasurable.sqrt
  have hb : AEMeasurable b μ := ha.mul hs
  have ha2 : (fun x => (a x)^2) =ᵐ[μ] r := by
    filter_upwards [hr0] with x hx
    exact Real.sq_sqrt hx
  have hb2 : (fun x => (b x)^2) =ᵐ[μ] fun x => r x*(s x)^2 := by
    filter_upwards [hr0] with x hx
    dsimp only [b]
    rw [mul_pow,Real.sq_sqrt hx]
  have ham : MemLp a 2 μ :=
    (memLp_two_iff_integrable_sq ha.aestronglyMeasurable).mpr (hr.congr ha2.symm)
  have hbm : MemLp b 2 μ :=
    (memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mpr (hrs.congr hb2.symm)
  have hab : (fun x => a x*b x) =ᵐ[μ] fun x => r x*s x := by
    filter_upwards [hr0] with x hx
    dsimp only [a,b]
    rw [←mul_assoc,←pow_two,Real.sq_sqrt hx]
  refine ⟨(ham.integrable_mul hbm).congr hab,?_⟩
  have h := integral_mul_sq_le_integral_sq μ a b ham hbm
  rw [integral_congr_ae hab,integral_congr_ae ha2,integral_congr_ae hb2,sq_abs] at h
  exact h

end RegularPointCoordinates

end

end OAI
