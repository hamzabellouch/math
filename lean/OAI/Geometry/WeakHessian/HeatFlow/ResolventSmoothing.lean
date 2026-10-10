import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatIntegralSmoothing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile147
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] in
lemma RCD.cheeger_scaled_resolvent_lipschitz {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) (u : Lp ℝ 2 m)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ᵐ x ∂m,|u x| ≤ B) {τ : ℝ} (hτ : 0 < τ) :
    ∃ g : X → ℝ,LipschitzWith (Real.toNNReal (5*B*Real.exp (|K| *τ)/Real.sqrt τ)) g ∧
      g =ᵐ[m] ((cheeger_closedQuadraticEnergy h).scale hτ).resolvent u := by
  let Q := cheeger_closedQuadraticEnergy h
  let z := (Q.scale hτ).resolvent u
  let A := τ⁻¹ • (z-u)
  have hz : Q.IsFormGenerator z A := (Q.scaled_resolvent_iff hτ u z).mp rfl
  have hzb : ∀ᵐ x ∂m,|z x| ≤ B := cheeger_scaled_resolvent_bounded h hτ hB u hu
  have hAb : ∀ᵐ x ∂m,|A x| ≤ 2*B/τ := by
    filter_upwards [hzb,hu,Lp.coeFn_sub z u,Lp.coeFn_smul τ⁻¹ (z-u)] with x hx hy hs hm
    rw [show A x=τ⁻¹*(z-u) x from hm,hs,abs_mul,abs_inv,abs_of_pos hτ]
    calc
      _ ≤ τ⁻¹*(|z x|+|u x|) := mul_le_mul_of_nonneg_left (abs_sub _ _) (inv_nonneg.mpr hτ.le)
      _ ≤ τ⁻¹*(B+B) := mul_le_mul_of_nonneg_left (add_le_add hx hy) (inv_nonneg.mpr hτ.le)
      _ = _ := by ring
  obtain ⟨p,hp,hep⟩ := hrcd.cheegerHeat_bounded_lipschitz hN hfull hfin h o z hB hzb hτ
  obtain ⟨q,hq,heq⟩ := hrcd.cheegerHeat_integral_bounded_lipschitz hN hfull hfin h o A
    (by positivity : 0 ≤ 2*B/τ) hAb hτ
  have hi := cheegerHeat_integral_generator hfin h hz hτ.le
  have he : (fun x => p x-q x) =ᵐ[m] z := by
    filter_upwards [hep,heq,Lp.coeFn_sub (cheegerHeat h τ z) z] with x hx hy hs
    rw [hx,hy,hi,hs]
    change cheegerHeat h τ z x - (cheegerHeat h τ z x - z x) = z x
    ring
  refine ⟨fun x => p x-q x,?_,he⟩
  apply (hp.sub hq).weaken
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_add,Real.coe_toNNReal _ (by positivity : 0 ≤ B*Real.exp (|K| *τ)/Real.sqrt τ),
    Real.coe_toNNReal _ (by positivity : 0 ≤ 2*(2*B/τ)*Real.exp (|K| *τ)*Real.sqrt τ),
    Real.coe_toNNReal _ (by positivity : 0 ≤ 5*B*Real.exp (|K| *τ)/Real.sqrt τ)]
  have hs := Real.sq_sqrt hτ.le
  have hsp := Real.sqrt_pos.mpr hτ
  apply le_of_eq
  field_simp
  nlinarith [hs]

omit [CompleteSpace X] in
lemma RCD.cheeger_resolvent_lipschitz {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) (u : Lp ℝ 2 m)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ᵐ x ∂m,|u x| ≤ B) {τ : ℝ} (hτ : 0 < τ) :
    ∃ g : X → ℝ,LipschitzWith (Real.toNNReal (5*B*Real.exp (|K| *τ)*Real.sqrt τ)) g ∧
      g =ᵐ[m] (τ • ((cheeger_closedQuadraticEnergy h).scale hτ).resolvent u : Lp ℝ 2 m) := by
  obtain ⟨g,hg,he⟩ := hrcd.cheeger_scaled_resolvent_lipschitz hN hfull hfin h o u hB hu hτ
  refine ⟨fun x => τ*g x,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq,← mul_sub,abs_mul,abs_of_pos hτ]
    have H := hg.dist_le_mul x y
    simp only [Real.dist_eq,Real.coe_toNNReal _ (by positivity : 0 ≤ 5*B*Real.exp (|K| *τ)/Real.sqrt τ)] at H
    rw [Real.coe_toNNReal _ (by positivity)]
    have hs : τ*(5*B*Real.exp (|K| *τ)/Real.sqrt τ) = 5*B*Real.exp (|K| *τ)*Real.sqrt τ := by
      rw [← mul_div_assoc]
      apply (div_eq_iff (Real.sqrt_pos.mpr hτ).ne').mpr
      rw [mul_assoc (5*B*Real.exp (|K| *τ)),Real.mul_self_sqrt hτ.le]
      ring
    calc
      _ ≤ τ*((5*B*Real.exp (|K| *τ)/Real.sqrt τ)*dist x y) := mul_le_mul_of_nonneg_left H hτ.le
      _ = _ := by rw [← mul_assoc,hs]
  · filter_upwards [he,Lp.coeFn_smul τ (((cheeger_closedQuadraticEnergy h).scale hτ).resolvent u)] with x hx hy
    rw [hx,hy]
    rfl
end WeakHessian

end
end InlinedFile147

end OAI
