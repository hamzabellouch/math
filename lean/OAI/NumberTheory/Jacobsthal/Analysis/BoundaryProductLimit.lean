import OAI.NumberTheory.Jacobsthal.Estimates.ReferenceProductErrors

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter _root_.Erdos970.Filter
open scoped Topology
namespace ErdosContinuousAnomaly
open ErdosContinuousBoundary
open NumberTheoryLean.ReferenceAdmission NumberTheoryLean.ReferencePruning
open NumberTheoryLean.ReferenceProductsBasics NumberTheoryLean.ReferenceMertens
open NumberTheoryLean.ReferenceProductErrors

noncomputable def boundaryProduct (w : ℝ) : ℝ := survivorProduct (boundaryPrimes w)

theorem boundaryProduct_eq_referenceProduct (w : ℝ) :
    boundaryProduct w=referenceProduct w 2 true := by
  simp only [boundaryProduct,referenceProduct,availableProduct,availablePrimes_closed,boundaryPrimes]

theorem boundaryProduct_tendsto_half : Tendsto boundaryProduct atTop (𝓝 (1/2:ℝ)) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := reference_product_absolute
  have he : ∀ᶠ w : ℝ in atTop,
      ‖referenceProduct w 2 true-normalization w/2‖ ≤ boundaryPrimeError c (C/2) w := by
    filter_upwards [eventually_ge_atTop w₀] with w hw
    have hh := (h w hw).2.2 2 le_rfl true
    have hw1 : 1 < w := hw₀.trans_le hw
    have hs : Real.sqrt (Real.log w) ≤ Real.sqrt (2*Real.log w) := by
      apply Real.sqrt_le_sqrt
      nlinarith [Real.log_pos hw1]
    have hm : Real.exp (-c*Real.sqrt (2*Real.log w)) ≤ Real.exp (-c*Real.sqrt (Real.log w)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [Real.norm_eq_abs]
    exact hh.trans (mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ C/2))
  have hz : Tendsto (fun w : ℝ => referenceProduct w 2 true-normalization w/2) atTop (𝓝 0) :=
    squeeze_zero_norm' he (boundaryPrimeError_tendsto_zero hc (C/2))
  have hsum := hz.add (normalization_tendsto_one.div_const (2:ℝ))
  have hv : Tendsto (fun w : ℝ => referenceProduct w 2 true) atTop (𝓝 (1/2:ℝ)) := by
    simpa only [sub_add_cancel,zero_add] using! hsum
  exact hv.congr' (Eventually.of_forall fun w => (boundaryProduct_eq_referenceProduct w).symm)

end ErdosContinuousAnomaly

end

end Erdos970

end OAI
