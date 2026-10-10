import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.GlobalCheegerEnergyMinimal
import OAI.Geometry.WeakHessian.Sobolev.Minimal

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open WeakHessianFunctional MeasureTheory
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma CurvatureDimension.global_cheegerEnergy_toReal {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (_ : QuadraticCheegerEnergy m)
    {f : X → ℝ} (hf : Sobolev m f) :
    (cheegerEnergy m f).toReal = (∫ x, (weakGradient m f x)^2 ∂m) / 2 := by
  rw [hcd.global_cheegerEnergy_eq_weakGradient hfinite o hf, ENNReal.toReal_ofReal (by positivity)]
  congr 1
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.2.2.coeFn_toLp] with x hx
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hx]

lemma CurvatureDimension.global_integral_gamma_eq {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m)
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) :
    (∫ x, gamma m f g x ∂m) =
      ((cheegerEnergy m (fun x => f x+g x)).toReal -
        (cheegerEnergy m (fun x => f x-g x)).toReal)/2 := by
  have hp := hf.add hfinite hg
  have hm := hf.sub hfinite hg
  simp only [gamma, integral_div, integral_sub hp.2.2.integrable_sq hm.2.2.integrable_sq,
    hcd.global_cheegerEnergy_toReal hfinite o h hp, hcd.global_cheegerEnergy_toReal hfinite o h hm]
  ring

lemma CurvatureDimension.global_integral_gamma_form {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m)
    (f g : (cheeger_closedQuadraticEnergy h).domain) :
    (∫ x, gamma m (f.val : X → ℝ) (g.val : X → ℝ) x ∂m) =
      2*(cheeger_closedQuadraticEnergy h).form f g := by
  have hf := (hcd.global_sobolev_iff_cheeger_lt_top hfinite o (Lp.memLp f.val)).mpr f.property
  have hg := (hcd.global_sobolev_iff_cheeger_lt_top hfinite o (Lp.memLp g.val)).mpr g.property
  rw [hcd.global_integral_gamma_eq hfinite o h hf hg]
  rw [ClosedQuadraticEnergy.form_apply]
  simp only [energyPolar, ClosedQuadraticEnergy.realEnergy, Submodule.coe_add,
    Submodule.coe_sub, cheegerEnergy_congr_ae (Lp.coeFn_add f.val g.val),
    cheegerEnergy_congr_ae (Lp.coeFn_sub f.val g.val)]
  change ((cheegerEnergy m (fun x => f.val x + g.val x)).toReal -
    (cheegerEnergy m (fun x => f.val x - g.val x)).toReal) / 2 =
    2 * (((cheegerEnergy m (fun x => f.val x + g.val x)).toReal -
      (cheegerEnergy m (fun x => f.val x - g.val x)).toReal) / 4)
  ring

lemma CurvatureDimension.global_formGenerator_of_isLaplacian {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m)
    (u A : Lp ℝ 2 m) (hu : IsLaplacian m (u : X → ℝ) (A : X → ℝ)) :
    (cheeger_closedQuadraticEnergy h).IsFormGenerator u A := by
  have huf := (hcd.global_sobolev_iff_cheeger_lt_top hfinite o (Lp.memLp u)).mp hu.1
  refine ⟨huf, fun v => ?_⟩
  rw [← hcd.global_integral_gamma_form hfinite o h ⟨u,huf⟩ v]
  have hv := (hcd.global_sobolev_iff_cheeger_lt_top hfinite o (Lp.memLp v.val)).mpr v.property
  rw [hu.2.2 v.val hv, L2.inner_def]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x => mul_comm (A x) (v.val x)

lemma CurvatureDimension.global_isLaplacian_of_formGenerator {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m)
    (u A : Lp ℝ 2 m) (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A) :
    IsLaplacian m (u : X → ℝ) (A : X → ℝ) := by
  refine ⟨(hcd.global_sobolev_iff_cheeger_lt_top hfinite o (Lp.memLp u)).mpr hu.1, Lp.memLp A, ?_⟩
  intro v hv
  let v' := hv.1.toLp v
  have hv' : cheegerEnergy m (v' : X → ℝ) < ∞ := by
    rw [cheegerEnergy_congr_ae hv.1.coeFn_toLp]
    exact (hcd.global_sobolev_iff_cheeger_lt_top hfinite o hv.1).mp hv
  have heq := hcd.global_integral_gamma_form hfinite o h ⟨u,hu.1⟩ ⟨v',hv'⟩
  have heq' := hu.2 ⟨v',hv'⟩
  calc
    (∫ x, gamma m (u : X → ℝ) v x ∂m) =
        ∫ x, gamma m (u : X → ℝ) (v' : X → ℝ) x ∂m :=
      integral_congr_ae (gamma_congr_ae Filter.EventuallyEq.rfl hv.1.coeFn_toLp.symm)
    _ = -⟪A,v'⟫_ℝ := heq.trans heq'
    _ = -(∫ x, A x * v x ∂m) := by
      rw [L2.inner_def]
      congr 1
      apply integral_congr_ae
      filter_upwards [hv.1.coeFn_toLp] with x hx
      change v' x * A x = A x * v x
      rw [show v' x = v x from hx]
      exact mul_comm _ _

lemma CurvatureDimension.global_isLaplacian_iff_formGenerator {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m)
    (u A : Lp ℝ 2 m) :
    IsLaplacian m (u : X → ℝ) (A : X → ℝ) ↔
      (cheeger_closedQuadraticEnergy h).IsFormGenerator u A :=
  ⟨hcd.global_formGenerator_of_isLaplacian hfinite o h u A, hcd.global_isLaplacian_of_formGenerator hfinite o h u A⟩

end WeakHessian

open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace

end
end InlinedFile0

end OAI
