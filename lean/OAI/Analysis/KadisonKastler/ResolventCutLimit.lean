import OAI.Analysis.KadisonKastler.ResolventCutRegularization

namespace OAI

/-! # Strong convergence of continuous cut regularizations -/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventCutRegularization_tendsto_range (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (r : ℝ) (x : H) :
    Tendsto (fun n => resolventCutRegularization R r (modularRegularizationScale n)
      (resolventCutGenerator R r x)) atTop (𝓝 (resolventCutGenerator R r x)) := by
  have hz : Tendsto (fun n => resolventCutRegularization R r (modularRegularizationScale n)
      (resolventCutGenerator R r x) - resolventCutGenerator R r x) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (show Tendsto (fun n => modularRegularizationScale n * ‖x‖) atTop (𝓝 0) by
        simpa only [zero_mul] using modularRegularizationScale_tendsto.mul_const ‖x‖)
    have h := ((resolventCutRegularization R r (modularRegularizationScale n) - 1) *
      resolventCutGenerator R r).le_opNorm x
    have hb := mul_le_mul_of_nonneg_right
      (resolventCutRegularization_error R hR r (modularRegularizationScale_pos n))
      (norm_nonneg x)
    simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] using h.trans hb
  convert hz.add_const (resolventCutGenerator R r x) using 1 <;> simp

theorem resolventCutRegularization_tendsto (R : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (r : ℝ) (x : H) :
    Tendsto (fun n => resolventCutRegularization R r (modularRegularizationScale n) x)
      atTop (𝓝 (resolventLowerCut R r x)) := by
  let P := resolventLowerCut R r
  let B := resolventCutGenerator R r
  let A := fun n => resolventCutRegularization R r (modularRegularizationScale n)
  have hA (n : ℕ) : ‖A n‖ ≤ 1 :=
    resolventCutRegularization_contracts R r (modularRegularizationScale_pos n)
  have hAP (n : ℕ) : A n (P x) = A n x :=
    congrArg (fun T : H →L[ℂ] H => T x)
      (resolventCutRegularization_support R hR r (modularRegularizationScale_pos n))
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hx : P x ∈ closure (Set.range B) :=
    B.range.topologicalClosure.starProjection_apply_mem x
  obtain ⟨z, ⟨y, rfl⟩, hy⟩ := Metric.mem_closure_iff.mp hx (δ / 4) (by positivity)
  have ht := resolventCutRegularization_tendsto_range R hR r y
  filter_upwards [Metric.tendsto_nhds.mp ht (δ / 2) (by positivity)] with n hn
  have he : dist (A n x) (A n (B y)) ≤ dist (P x) (B y) := by
    rw [← hAP n, dist_eq_norm, ← map_sub]
    exact ((A n).le_opNorm _).trans
      (by simpa only [one_mul, dist_eq_norm] using
        mul_le_mul_of_nonneg_right (hA n) (norm_nonneg (P x - B y)))
  have hb := (dist_triangle (A n x) (A n (B y)) (P x)).trans
    (add_le_add le_rfl (dist_triangle (A n (B y)) (B y) (P x)))
  rw [dist_comm (B y) (P x)] at hb
  change dist (A n (B y)) (B y) < δ / 2 at hn
  linarith

end

end KadisonKastler

end OAI
