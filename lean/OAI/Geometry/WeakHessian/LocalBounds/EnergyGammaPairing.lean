import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.WeightedEnergyClosure
import OAI.Geometry.WeakHessian.LocalBounds.EnergyIdentification

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile208
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma energy_tendsto_weakGradient (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    {un : ℕ → X → ℝ} {u : X → ℝ}
    (hn : ∀ n,Sobolev m (un n)) (hu : Sobolev m u)
    (ht : Tendsto (fun n => (cheegerEnergy m (fun x => un n x-u x)).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => (hn n).2.2.toLp (weakGradient m (un n))) atTop
      (𝓝 (hu.2.2.toLp (weakGradient m u))) := by
  have hd (n : ℕ) := (hn n).sub hfin hu
  have he (n : ℕ) : ‖(hd n).2.2.toLp (weakGradient m (fun x => un n x-u x))‖^2 =
      2*(cheegerEnergy m (fun x => un n x-u x)).toReal := by
    rw [norm_toLp_sq_eq_integral,identified_cheegerEnergy_toReal hID (hd n)]
    ring
  have hs : Tendsto (fun n => ‖(hd n).2.2.toLp (weakGradient m (fun x => un n x-u x))‖^2)
      atTop (𝓝 0) := by simpa only [he,mul_zero] using ht.const_mul 2
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] at hnorm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hnorm
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub ((hn n).2.2.toLp (weakGradient m (un n)))
      (hu.2.2.toLp (weakGradient m u)),(hn n).2.2.coeFn_toLp,
    hu.2.2.coeFn_toLp,(hd n).2.2.coeFn_toLp,
    weakGradient_dist_le hfin (hn n).2.1 hu.2.1,
    weakGradient_nonneg (m := m) (fun x => un n x-u x)] with x hs hn' hu' hd hab hp
  rw [hs,Pi.sub_apply,hn',hu',hd,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hp]
  exact hab

omit [ProperSpace X] [SigmaFinite m] in
lemma energy_tendsto_gamma_bounded_pairing (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ,Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2))
    {un : ℕ → X → ℝ} {u : X → ℝ}
    (hn : ∀ n,Sobolev m (un n)) (hu : Sobolev m u)
    (ht : Tendsto (fun n => (cheegerEnergy m (fun x => un n x-u x)).toReal) atTop (𝓝 0))
    {ξ : X → ℝ} (hξ : AEStronglyMeasurable ξ m) {B : ℝ} (hξb : ∀ᵐ x ∂m,|ξ x| ≤ B) :
    Tendsto (fun n => ∫ x,ξ x*gamma m (un n) (un n) x ∂m) atTop
      (𝓝 (∫ x,ξ x*gamma m u u x ∂m)) := by
  have hD := energy_tendsto_weakGradient hfin hID hn hu ht
  have hval := tendsto_integral_bounded_Lp_sq hξ hξb hD
  have hid (v : X → ℝ) (hv : MemLp (weakGradient m v) 2 m) :
      (∫ x,ξ x*gamma m v v x ∂m) = ∫ x,ξ x*(hv.toLp (weakGradient m v) x)^2 ∂m := by
    apply integral_congr_ae
    filter_upwards [gamma_self (m := m) v,hv.coeFn_toLp] with x hΓ hx
    rw [hΓ,hx]
  simpa only [hid _ hu.2.2,hid _ ((hn _).2.2)] using hval
end WeakHessian

end
end InlinedFile208

end OAI
