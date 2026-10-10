import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerDerivative
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences

namespace OAI

/-! Uniform C¹ subsequence extraction for the inner amplitudes. -/

open Set Filter Topology
open scoped BoundedContinuousFunction
namespace DefocusingNLS

/-- The exact bounds proved for inner profiles give compactness of their amplitude/derivative
pairs in the uniform topology. -/
theorem radial_inner_jet_subsequence (R : ℝ) (_hR : 1 ≤ R) (hR2 : R^2 ≤ 11)
    (H : ℕ → ℝ → ℝ) (hH : ∀ n, Differentiable ℝ (H n))
    (hDC : ∀ n, ContinuousOn (deriv (H n)) (Icc 0 R))
    (hB : ∀ n r, r ∈ Icc 0 R → ‖H n r‖ ≤ 1 ∧ ‖deriv (H n) r‖ ≤ r/24)
    (hL : ∀ n, LipschitzOnWith 1 (deriv (H n)) (Icc 0 R)) :
    ∃ J : (Icc (0 : ℝ) R) →ᵇ ℝ × ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun n (r : Icc (0 : ℝ) R) =>
        (H (φ n) r, deriv (H (φ n)) r)) J atTop := by
  have hR24 : R/24 ≤ 1 := by nlinarith [_hR,sq_nonneg (R-12)]
  have hA : ∀ n, LipschitzOnWith 1 (H n) (Icc 0 R) := by
    intro n
    apply (convex_Icc (0 : ℝ) R).lipschitzOnWith_of_nnnorm_deriv_le
      (fun r _ => hH n r)
    intro r hr
    change ‖deriv (H n) r‖₊ ≤ (1 : NNReal)
    have hb := (hB n r hr).2
    have hr24 : r/24 ≤ 1 := (div_le_div_of_nonneg_right hr.2 (by norm_num)).trans hR24
    exact_mod_cast hb.trans hr24
  let F : ℕ → (Icc (0 : ℝ) R) →ᵇ ℝ × ℝ := fun n =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun (r : Icc (0 : ℝ) R) => (H n r, deriv (H n) r),
        ((hH n).continuous.comp continuous_subtype_val).prodMk
          (continuousOn_iff_continuous_domRestrict.mp (hDC n))⟩
  have hFL : ∀ n, LipschitzWith 1 (F n) := by
    intro n
    change LipschitzWith 1 (fun (r : Icc (0 : ℝ) R) => (H n r, deriv (H n) r))
    simpa only [max_self,Set.domRestrict_apply] using (hA n).to_restrict.prodMk (hL n).to_restrict
  have hFB : ∀ n (r : Icc (0 : ℝ) R), ‖F n r‖ ≤ 1 := by
    intro n r
    change max ‖H n r‖ ‖deriv (H n) r‖ ≤ 1
    exact max_le (hB n r r.2).1
      ((hB n r r.2).2.trans ((div_le_div_of_nonneg_right r.2.2 (by norm_num)).trans hR24))
  have hEq : Equicontinuous ((↑) : range F → (Icc (0 : ℝ) R) → ℝ × ℝ) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ 1
    rintro ⟨f,n,rfl⟩
    exact hFL n
  have hC : IsCompact (closure (range F)) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ × ℝ) 1)
      (isCompact_closedBall _ _) (range F)
      (by
        rintro f r ⟨n,rfl⟩
        simpa only [Metric.mem_closedBall,dist_zero_right] using hFB n r) hEq
  obtain ⟨J,_,φ,hφ,hT⟩ := hC.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  refine ⟨J,φ,hφ,?_⟩
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hT

end DefocusingNLS

end OAI
