import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.DriftPerturbation
import OAI.Geometry.WeakHessian.LocalBounds.DriftFixedBase

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile151
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.drift_fixedPoint {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    (o : X) {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    {τ : ℝ} (hτ : 0 < τ) (hL2 : (L:ℝ)*Real.sqrt τ < 1)
    (hLinf : 5*(L:ℝ)*Real.exp (|K| *τ)*Real.sqrt τ ≤ 1/2)
    (u : Lp ℝ 2 m) {B : ℝ} (hB : 0 ≤ B) (hu : ∀ᵐ x ∂m,|u x| ≤ B) :
    ∃ w : Lp ℝ 2 m,w = u+hrcd.1.driftPerturbation hfin h o hV hτ w ∧
      ∀ᵐ x ∂m,|w x| ≤ 2*B := by
  let P := hrcd.1.driftPerturbation hfin h o hV hτ
  let F (w : Lp ℝ 2 m) := u+P w
  have hLip : LipschitzWith (Real.toNNReal ((L:ℝ)*Real.sqrt τ)) F := by
    apply LipschitzWith.of_dist_le_mul
    intro w z
    simp only [F,dist_add_left]
    exact (hrcd.1.driftPerturbation_lipschitz hfin h o hV hτ).dist_le_mul w z
  have hC : ContractingWith (Real.toNNReal ((L:ℝ)*Real.sqrt τ)) F :=
    ⟨by exact_mod_cast (show (↑(Real.toNNReal ((L:ℝ)*Real.sqrt τ)):ℝ) < 1 by rwa [Real.coe_toNNReal _ (by positivity)]),hLip⟩
  obtain ⟨w,hw,ht,-⟩ := hC.exists_fixedPoint 0 (by simp)
  have hb : ∀ n,∀ᵐ x ∂m,|(F^[n] 0 : Lp ℝ 2 m) x| ≤ 2*B := by
    intro n
    induction n with
    | zero =>
      filter_upwards [Lp.coeFn_zero ℝ 2 m] with x hx
      change |(0 : Lp ℝ 2 m) x| ≤ 2*B
      rw [hx]
      simpa only [Pi.zero_apply,abs_zero] using (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB)
    | succ n ihn =>
      have hbn := hrcd.driftPerturbation_bounded hfin h o hV hτ hN hfull (F^[n] 0)
        (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB) ihn
      filter_upwards [hu,hbn,Lp.coeFn_add u (P (F^[n] 0))] with x hx hy ha
      rw [Function.iterate_succ_apply']
      change |(u+P (F^[n] 0)) x| ≤ 2*B
      rw [ha]
      change |u x+P (F^[n] 0) x| ≤ 2*B
      calc
        _ ≤ |u x|+|P (F^[n] 0) x| := abs_add_le _ _
        _ ≤ B+5*(L:ℝ)*(2*B)*Real.exp (|K| *τ)*Real.sqrt τ := add_le_add hx hy
        _ ≤ 2*B := by
          have H := mul_le_mul_of_nonneg_left hLinf (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB)
          nlinarith only [H]
  exact ⟨w,hw.symm,ae_bounded_of_tendsto_L2 ht hb⟩

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma positive_small_drift_time (K : ℝ) (L : ℝ≥0) :
    ∃ τ : ℝ,0 < τ ∧ (L:ℝ)*Real.sqrt τ < 1 ∧
      5*(L:ℝ)*Real.exp (|K| *τ)*Real.sqrt τ ≤ 1/2 := by
  have h₁ : ContinuousAt (fun t : ℝ => (L:ℝ)*Real.sqrt t) 0 := by fun_prop
  have h₂ : ContinuousAt (fun t : ℝ => 5*(L:ℝ)*Real.exp (|K| *t)*Real.sqrt t) 0 := by fun_prop
  have e₁ : ∀ᶠ t in 𝓝 (0:ℝ),(L:ℝ)*Real.sqrt t < 1 := h₁.tendsto.eventually (gt_mem_nhds (by simp))
  have e₂ : ∀ᶠ t in 𝓝 (0:ℝ),5*(L:ℝ)*Real.exp (|K| *t)*Real.sqrt t < 1/2 := h₂.tendsto.eventually (gt_mem_nhds (by norm_num))
  have e := (e₁.and e₂).filter_mono (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  obtain ⟨t,ht,hs⟩ := (e.and self_mem_nhdsWithin).exists
  exact ⟨t,hs,ht.1,ht.2.le⟩
end WeakHessian

end
end InlinedFile151

end OAI
