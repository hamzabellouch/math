import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.DriftHeatSobolev
import OAI.Geometry.WeakHessian.Transport.FormAction

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

omit [CompleteSpace X] [SigmaFinite m] in
lemma heat_gradient_integral_le
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {f : Lp ℝ 2 m}
    (hf : Sobolev m (f : X → ℝ)) {T : ℝ} (hT : 0 ≤ T) :
    (∫ x, (weakGradient m (cheegerHeat h T f) x)^2 ∂m) ≤
      ∫ x, (weakGradient m f x)^2 ∂m := by
  have hfd := (identified_sobolev_iff_energy hfin hID).mp hf
  have hE := cheegerHeat_energy_le h hT f
  have hfs := (identified_sobolev_iff_energy hfin hID).mpr (hE.trans_lt hfd)
  have H := ENNReal.toReal_mono hfd.ne hE
  rw [identified_cheegerEnergy_toReal hID hfs,identified_cheegerEnergy_toReal hID hf] at H
  linarith

omit [CompleteSpace X] [SigmaFinite m] in
lemma FormActionBound.heat_contraction_regularized
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (h : QuadraticCheegerEnergy m) {T c ε : ℝ} (hT : 0 ≤ T) (hc : 0 < c)
    (hε : 0 ≤ ε) {u v : Lp ℝ 2 m} {B : ℝ} (hB : 0 ≤ B)
    (hub : ∀ᵐ x ∂m, |u x| ≤ B)
    (hgrad : ∀ f : Lp ℝ 2 m, Sobolev m (f : X → ℝ) →
      c*(∫ x, u x*(weakGradient m (cheegerHeat h T f) x)^2 ∂m) ≤
        ∫ x, cheegerHeat h T u x*(weakGradient m f x)^2 ∂m)
    {A : ℝ} (hA : FormActionBound m (fun x => u x+ε) v A) :
    FormActionBound m (fun x => cheegerHeat h T u x+c*ε) (cheegerHeat h T v) (A/c) := by
  have hPS (f : Lp ℝ 2 m) (hf : Sobolev m (f : X → ℝ)) :
      Sobolev m (cheegerHeat h T f) := (identified_sobolev_iff_energy hfin hID).mpr
    ((cheegerHeat_energy_le h hT f).trans_lt ((identified_sobolev_iff_energy hfin hID).mp hf))
  apply hA.symmetric_contraction (cheegerHeat_symmetric h T) hPS hc
  intro f hf
  have hiu : Integrable (fun x => u x*(weakGradient m (cheegerHeat h T f) x)^2) m :=
    (hPS f hf).2.2.integrable_sq.bdd_mul (Lp.memLp u).aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hub)
  have hiv : Integrable (fun x => cheegerHeat h T u x*(weakGradient m f x)^2) m :=
    hf.2.2.integrable_sq.bdd_mul (Lp.memLp _).aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using cheegerHeat_bounded h hT hB u hub)
  have hleft : (∫ x, (u x+ε)*(weakGradient m (cheegerHeat h T f) x)^2 ∂m) =
      (∫ x, u x*(weakGradient m (cheegerHeat h T f) x)^2 ∂m) +
      ε*(∫ x, (weakGradient m (cheegerHeat h T f) x)^2 ∂m) := by
    simp_rw [add_mul]
    rw [integral_add hiu ((hPS f hf).2.2.integrable_sq.const_mul ε),integral_const_mul]
  have hright : (∫ x, (cheegerHeat h T u x+c*ε)*(weakGradient m f x)^2 ∂m) =
      (∫ x, cheegerHeat h T u x*(weakGradient m f x)^2 ∂m) +
      c*ε*(∫ x, (weakGradient m f x)^2 ∂m) := by
    simp_rw [add_mul]
    rw [integral_add hiv (hf.2.2.integrable_sq.const_mul (c*ε)),integral_const_mul]
  rw [hleft,hright]
  have hE := mul_le_mul_of_nonneg_left (heat_gradient_integral_le hfin hID h hf hT)
    (mul_nonneg hc.le hε)
  linarith [hgrad f hf]

theorem WeakHessianUpperBound.rcd_weighted_heat_formAction {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    {u v : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))}
    {B ε A T : ℝ} (hB : 0 ≤ B) (hub : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|u x| ≤ B)
    (hun : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ u x)
    (hε : 0 ≤ ε) (hT : 0 ≤ T)
    (hA : FormActionBound (exponentialMeasure m (fun x => a*F x)) (fun x => u x+ε) v A) :
    FormActionBound (exponentialMeasure m (fun x => a*F x))
      (fun x => cheegerHeat h T u x+Real.exp (2*(K-a*CG)*T)*ε)
      (cheegerHeat h T v) (A/Real.exp (2*(K-a*CG)*T)) := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) hVB).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hVB (f := f) hf
  apply hA.heat_contraction_regularized hnfin hID h hT (Real.exp_pos _) hε hB hub
  intro f hf
  have H := hHess.rcd_weighted_heat_gradient_sobolev hN hrcd hfull hfin o
    hF hFb hGb hGc ha h hf hB hub hun hT
  have hi1 : (∫ x, u x*gamma ν (cheegerHeat h T f) (cheegerHeat h T f) x ∂ν) =
      ∫ x, u x*(weakGradient ν (cheegerHeat h T f) x)^2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [gamma_self (m := ν) (cheegerHeat h T f)] with x hx
    rw [hx]
  have hi2 : (∫ x, cheegerHeat h T u x*gamma ν f f x ∂ν) =
      ∫ x, cheegerHeat h T u x*(weakGradient ν f x)^2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [gamma_self (m := ν) (f : X → ℝ)] with x hx
    rw [hx]
  change (∫ x, u x*gamma ν (cheegerHeat h T f) (cheegerHeat h T f) x ∂ν) ≤
    Real.exp (-(2*(K-a*CG))*T)*(∫ x, cheegerHeat h T u x*gamma ν f f x ∂ν) at H
  rw [hi1,hi2] at H
  have H' := mul_le_mul_of_nonneg_left H (Real.exp_pos (2*(K-a*CG)*T)).le
  have he : Real.exp (2*(K-a*CG)*T)*Real.exp (-(2*(K-a*CG))*T) = 1 := by
    rw [← Real.exp_add]
    rw [neg_mul,add_neg_cancel,Real.exp_zero]
  simpa only [← mul_assoc,he,one_mul] using H'

end WeakHessian

end
end

end OAI
