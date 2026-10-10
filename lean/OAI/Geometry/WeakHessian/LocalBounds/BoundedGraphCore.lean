import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.FormGeneratorSymmetric

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile206
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

lemma cheeger_bounded_graph_core (h : QuadraticCheegerEnergy m)
    {f A : Lp ℝ 2 m} (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f A) :
    ∃ vs As : ℕ → Lp ℝ 2 m,
      (∀ n,(cheeger_closedQuadraticEnergy h).IsFormGenerator (vs n) (As n)) ∧
      (∀ n,∀ᵐ x ∂m,|vs n x| ≤ (n:ℝ)) ∧
      (∀ n,∀ᵐ x ∂m,|As n x| ≤ 2*(n:ℝ)) ∧
      Tendsto vs atTop (𝓝 f) ∧ Tendsto As atTop (𝓝 A) := by
  let Q := cheeger_closedQuadraticEnergy h
  let R := (Q.scale (show (0:ℝ)<1 from zero_lt_one)).resolventLinear
  let b := fun n => (realClip_lipschitz n).compLp (μ := m) (p := 2) (realClip_zero n) (f-A)
  let vs := fun n => R (b n)
  let As := fun n => vs n-b n
  have hb (n : ℕ) : ∀ᵐ x ∂m,|b n x| ≤ (n:ℝ) := by
    filter_upwards [(realClip_lipschitz n).coeFn_compLp (realClip_zero n) (f-A)] with x hx
    rw [show b n x = realClip n ((f-A) x) from hx]
    exact realClip_abs_le n _
  have hvs (n : ℕ) : ∀ᵐ x ∂m,|vs n x| ≤ (n:ℝ) :=
    cheeger_scaled_resolvent_bounded h zero_lt_one (Nat.cast_nonneg n) (b n) (hb n)
  have hAs (n : ℕ) : ∀ᵐ x ∂m,|As n x| ≤ 2*(n:ℝ) := by
    filter_upwards [Lp.coeFn_sub (vs n) (b n),hvs n,hb n] with x he hv hb
    change |(vs n-b n) x| ≤ _
    rw [he,Pi.sub_apply]
    exact (abs_sub _ _).trans (by linarith)
  have hg (n : ℕ) : Q.IsFormGenerator (vs n) (As n) := by
    have H := (Q.scaled_resolvent_iff zero_lt_one (b n) (vs n)).mp rfl
    simpa only [inv_one,one_smul] using H
  have he : R (f-A) = f := by
    apply (Q.scaled_resolvent_iff zero_lt_one (f-A) f).mpr
    simpa only [sub_sub_cancel,inv_one,one_smul] using hf
  have hvlim : Tendsto vs atTop (𝓝 f) := by
    have H := R.continuous.tendsto (f-A) |>.comp (realClip_tendsto_Lp (f-A))
    simpa only [he,Function.comp_def] using H
  refine ⟨vs,As,hg,hvs,hAs,hvlim,?_⟩
  simpa only [sub_sub_cancel] using hvlim.sub (realClip_tendsto_Lp (f-A))
end WeakHessian

end
end InlinedFile206

end OAI
