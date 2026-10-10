import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatBoundedRegularization

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile143
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma reversePoincare_sqrt_le (K : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.sqrt (1/(2*t*Real.exp (-2*|K| *t))) ≤ Real.exp (|K| *t)/Real.sqrt t := by
  have he : Real.exp (-2*|K| *t) = (Real.exp (|K| *t)^2)⁻¹ := by
    rw [show -2*|K| *t= -((|K| *t)+(|K| *t)) by ring,Real.exp_neg,Real.exp_add,pow_two]
  rw [he]
  have H : 1/(2*t*(Real.exp (|K| *t)^2)⁻¹) = Real.exp (|K| *t)^2/(2*t) := by field_simp
  rw [H,Real.sqrt_div (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.sqrt_pos.mpr ht)
    (Real.sqrt_le_sqrt (by linarith : t ≤ 2*t))

omit [CompleteSpace X] in
lemma RCD.cheegerHeat_bounded_lipschitz {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) (u : Lp ℝ 2 m)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ᵐ x ∂m,|u x| ≤ B) {t : ℝ} (ht : 0 < t) :
    ∃ g : X → ℝ,LipschitzWith (Real.toNNReal (B*Real.exp (|K| *t)/Real.sqrt t)) g ∧
      g =ᵐ[m] cheegerHeat h t u := by
  by_cases hb : B = 0
  · have huz : u = 0 := by
      apply Lp.ext
      filter_upwards [hu,Lp.coeFn_zero ℝ 2 m] with x hx he
      rw [he]
      apply abs_eq_zero.mp
      exact le_antisymm (by simpa [hb] using hx) (abs_nonneg _)
    refine ⟨fun _ => 0,?_,?_⟩
    · simp [hb]
    · rw [huz,map_zero]
      exact (Lp.coeFn_zero ℝ 2 m).symm
  have hp : 0 < B := lt_of_le_of_ne hB (Ne.symm hb)
  let v := B⁻¹ • u
  have hv : ∀ᵐ x ∂m,|v x| ≤ (1:ℝ) := by
    filter_upwards [hu,Lp.coeFn_smul B⁻¹ u] with x hx he
    rw [show v x=B⁻¹*u x from he,abs_mul,abs_inv,abs_of_pos hp]
    exact (inv_mul_le_iff₀ hp).mpr (by simpa using hx)
  obtain ⟨g,hg,he⟩ := hrcd.cheegerHeat_bounded_regularization hN hfull hfin h o v 1 (by simpa using hv) ht
  refine ⟨fun x => B*g x,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq,← mul_sub,abs_mul,abs_of_nonneg hB]
    have HG := hg.dist_le_mul x y
    simp only [Real.dist_eq,Real.coe_toNNReal _ (Real.sqrt_nonneg _),Nat.cast_one,one_pow] at HG
    rw [Real.coe_toNNReal _ (by positivity)]
    calc
      _ ≤ B*(Real.sqrt (1/(2*t*Real.exp (-2*|K| *t)))*dist x y) := mul_le_mul_of_nonneg_left HG hB
      _ = (B*Real.sqrt (1/(2*t*Real.exp (-2*|K| *t))))*dist x y := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (reversePoincare_sqrt_le K ht) hB) dist_nonneg
  · have hvU : B • cheegerHeat h t v = cheegerHeat h t u := by
      rw [← map_smul,show B • v=u by dsimp [v]; rw [smul_smul,mul_inv_cancel₀ hb,one_smul]]
    filter_upwards [he,Lp.coeFn_smul B (cheegerHeat h t v)] with x hx hy
    rw [hx]
    change (B • (cheegerHeat h t v : X → ℝ)) x = _
    rw [← hy,hvU]
end WeakHessian

end
end InlinedFile143

end OAI
