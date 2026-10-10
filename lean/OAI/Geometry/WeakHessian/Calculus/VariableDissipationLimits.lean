import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.BochnerConvex
import OAI.Geometry.WeakHessian.LocalBounds.EnergyIdentification

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma abs_integral_bounded_gamma_self_le_energy
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    {u q : X → ℝ} (hu : Sobolev m u)
    (hqm : AEStronglyMeasurable q m) {B : ℝ} (hqb : ∀ᵐ x ∂m, |q x| ≤ B) :
    |∫ x, q x * gamma m u u x ∂m| ≤ B * (2 * (cheegerEnergy m u).toReal) := by
  have hi := integrable_bounded_gamma hfin hu hu hqm hqb
  have hD : Integrable (fun x => (weakGradient m u x)^2) m := hu.2.2.integrable_sq
  calc
    _ ≤ ∫ x, |q x * gamma m u u x| ∂m := abs_integral_le_integral_abs
    _ ≤ ∫ x, B * (weakGradient m u x)^2 ∂m := by
      apply integral_mono_ae hi.abs (hD.const_mul B)
      filter_upwards [hqb, gamma_self (m := m) u] with x hx hΓ
      rw [hΓ, abs_mul, abs_of_nonneg (sq_nonneg (weakGradient m u x))]
      exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)
    _ = _ := by rw [integral_const_mul, identified_cheegerEnergy_toReal hID hu]; ring

omit [SigmaFinite m] in
lemma abs_weighted_heat_gamma_le
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {f ξ : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) {Cξ : ℝ} (hCξ : 0 ≤ Cξ)
    (hξb : ∀ᵐ x ∂m, |ξ x| ≤ Cξ)
    {k : X → ℝ} (hkm : AEStronglyMeasurable k m)
    {B : ℝ} (hB : 0 ≤ B) (hkb : ∀ᵐ x ∂m, |k x| ≤ B)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |∫ x, (cheegerHeat h s ξ x * k x) *
      gamma m (cheegerHeat h t f) (cheegerHeat h t f) x ∂m| ≤
      (Cξ * B) * (2 * (cheegerEnergy m (f : X → ℝ)).toReal) := by
  have hfd := (identified_sobolev_iff_energy hfin hID).mp hf
  have hht := cheegerHeat_energy_le h ht f
  have hft : Sobolev m (cheegerHeat h t f) :=
    (identified_sobolev_iff_energy hfin hID).mpr (hht.trans_lt hfd)
  have hq : AEStronglyMeasurable (fun x => cheegerHeat h s ξ x * k x) m :=
    (Lp.memLp _).aestronglyMeasurable.mul hkm
  have hqb : ∀ᵐ x ∂m, |cheegerHeat h s ξ x * k x| ≤ Cξ * B := by
    filter_upwards [cheegerHeat_bounded h hs hCξ ξ hξb, hkb] with x hx hk
    rw [abs_mul]
    exact mul_le_mul hx hk (abs_nonneg _) hCξ
  exact (abs_integral_bounded_gamma_self_le_energy hfin hID hft hq hqb).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfd.ne hht) (by norm_num))
      (mul_nonneg hCξ hB))

end WeakHessian

end
end

end OAI
