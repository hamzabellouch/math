import OAI.Geometry.RCD.Heat.BoundedProductPowerRate
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace OAI

/-! # Global power differentiation with one integrable time envelope

All pointwise hypotheses hold on one common full-measure set, for every
time in the neighborhood. No exchange of uncountable null sets is used.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem dominated_product_power_hasDerivAt
    (F G dF dG : ℝ → X → ℝ) {s : Set ℝ} {t : ℝ} (hs : s ∈ 𝓝 t)
    (hFm : ∀ r ∈ s, AEStronglyMeasurable (F r) μ)
    (hGm : ∀ r ∈ s, AEStronglyMeasurable (G r) μ)
    (hdFm : AEStronglyMeasurable (dF t) μ) (hdGm : AEStronglyMeasurable (dG t) μ)
    (q : ℕ) (hi : Integrable (fun x => (F t x*G t x)^q) μ)
    {A B U V : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (_hV : 0 ≤ V)
    (H : X → ℝ) (hH : Integrable H μ)
    (hdata : ∀ᵐ x ∂μ, ∀ r ∈ s,
      F r x ∈ Icc 0 A ∧ G r x ∈ Icc 0 B ∧
      |dF r x| ≤ U ∧ |dG r x| ≤ V ∧ F r x+G r x ≤ H x ∧
      HasDerivAt (fun u => F u x) (dF r x) r ∧
      HasDerivAt (fun u => G u x) (dG r x) r) :
    HasDerivAt (fun r => ∫ x, (F r x*G r x)^q ∂μ)
      ((q:ℝ)*(∫ x, (F t x*G t x)^(q-1)*(dF t x*G t x+F t x*dG t x) ∂μ)) t := by
  let C := (q:ℝ)*(A*B)^(q-1)*max U V
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hst : t ∈ s := mem_of_mem_nhds hs
  have hm : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable (fun x => (F r x*G r x)^q) μ := by
    filter_upwards [hs] with r hr
    exact ((hFm r hr).mul (hGm r hr)).pow q
  have hdm : AEStronglyMeasurable (fun x =>
      (q:ℝ)*(F t x*G t x)^(q-1)*(dF t x*G t x+F t x*dG t x)) μ :=
    (((hFm t hst).mul (hGm t hst)).pow (q-1) |>.const_mul (q:ℝ)).mul
      ((hdFm.mul (hGm t hst)).add ((hFm t hst).mul hdGm))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm hi hdm
    (bound := fun x => C*H x) (by
      filter_upwards [hdata] with x hx
      intro r hr
      obtain ⟨hf,hg,hdf,hdg,hfg,_,_⟩ := hx r hr
      rw [Real.norm_eq_abs]
      exact (bounded_product_power_rate hf.1 hg.1 hf.2 hg.2 hdf hdg q).trans
        (mul_le_mul_of_nonneg_left hfg hC)) (hH.const_mul C) (by
      filter_upwards [hdata] with x hx
      intro r hr
      exact (((hx r hr).2.2.2.2.2.1).mul ((hx r hr).2.2.2.2.2.2)).pow q)
  simpa only [mul_assoc,integral_const_mul] using hd.2

end RegularPointCoordinates

end

end OAI
