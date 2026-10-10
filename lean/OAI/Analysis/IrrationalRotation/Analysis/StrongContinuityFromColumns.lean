import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

open Set Filter Topology

namespace Invariant233.StrongContinuityFromColumns

theorem continuous_apply_of_dense {𝕜 X E F : Type*}
    [NontriviallyNormedField 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) {s : Set E} (hs : Dense s)
    (hcont : ∀ v ∈ s, Continuous (fun x => A x v)) (v : E) :
    Continuous (fun x => A x v) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hden : 0 < 3 * (C + 1) := by positivity
  obtain ⟨w, hw, hvw⟩ := hs.exists_dist_lt v (div_pos hε hden)
  have hvw' : C * dist v w < ε / 3 := by
    have hdist : 0 ≤ dist v w := dist_nonneg
    have hlt : dist v w * (3 * (C + 1)) < ε :=
      (lt_div_iff₀ hden).mp hvw
    nlinarith
  have hevent : ∀ᶠ y in 𝓝 x, dist (A y w) (A x w) < ε / 3 :=
    Metric.tendsto_nhds.mp (hcont w hw).continuousAt (ε / 3) (by positivity)
  filter_upwards [hevent] with y hy
  have hleft : dist (A y v) (A y w) ≤ C * dist v w := by
    calc
      dist (A y v) (A y w) ≤ ‖A y‖ * dist v w := (A y).lipschitzWith.dist_le_mul v w
      _ ≤ C * dist v w := mul_le_mul_of_nonneg_right (hbound y) dist_nonneg
  have hright : dist (A x w) (A x v) ≤ C * dist v w := by
    calc
      dist (A x w) (A x v) ≤ ‖A x‖ * dist w v := (A x).lipschitzWith.dist_le_mul w v
      _ ≤ C * dist w v := mul_le_mul_of_nonneg_right (hbound x) dist_nonneg
      _ = C * dist v w := by rw [dist_comm w v]
  have htri := dist_triangle4 (A y v) (A y w) (A x w) (A x v)
  linarith

theorem continuous_apply_of_dense_span {𝕜 X E F ι : Type*}
    [NontriviallyNormedField 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) (b : ι → E)
    (hb : (Submodule.span 𝕜 (Set.range b)).topologicalClosure = ⊤)
    (hcont : ∀ i, Continuous (fun x => A x (b i))) (v : E) :
    Continuous (fun x => A x v) := by
  apply continuous_apply_of_dense A hC hbound
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr hb) _ v
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      exact hcont i
  | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : X => (0 : F)))
  | add w z hw hz hwc hzc =>
      simpa only [map_add, Pi.add_def] using hwc.add hzc
  | smul c w hw hwc =>
      simpa only [map_smul, Pi.smul_def] using hwc.const_smul c

theorem continuous_apply_of_hilbertBasis {𝕜 X E F ι : Type*}
    [RCLike 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) (b : HilbertBasis ι 𝕜 E)
    (hcont : ∀ i, Continuous (fun x => A x (b i))) (v : E) :
    Continuous (fun x => A x v) :=
  continuous_apply_of_dense_span A hC hbound b b.dense_span hcont v

theorem continuousOn_apply_of_hilbertBasis {𝕜 X E F ι : Type*}
    [RCLike 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C) {Q : Set X}
    (hbound : ∀ x ∈ Q, ‖A x‖ ≤ C) (b : HilbertBasis ι 𝕜 E)
    (hcont : ∀ i, ContinuousOn (fun x => A x (b i)) Q) (v : E) :
    ContinuousOn (fun x => A x v) Q := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_apply_of_hilbertBasis (fun x : Q => A x) hC
    (fun x => hbound x x.property) b (fun i => (hcont i).domRestrict) v

end Invariant233.StrongContinuityFromColumns

end OAI
