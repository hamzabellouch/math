import Mathlib
import OAI.Analysis.SymmetricDomains.HolomorphicLocallyUniformLimit

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem analytic_comp_chart_inverse {n d m : ℕ} {W : Set (Affine n)}
    {D : Set (Affine d)} (hD : IsOpen D) (e : Biholomorph W D)
    {f : Affine n → Affine m} (hf : HolomorphicOnSubset W (fun x => f x)) :
    AnalyticOnNhd ℂ (f ∘ ambientExtend (fun x => (e.toHomeomorph.symm x).val)) D := by
  have hh := (hf.comp e.holomorphic_invFun).analyticOnNhd_extend hD
  intro x hx
  apply (hh x hx).congr
  filter_upwards [hD.mem_nhds hx] with y hy
  simp only [Function.comp_def,ambientExtend,dite_eq_left hy]

theorem chart_eventual_equicontinuity {n d m : ℕ} {W : Set (Affine n)}
    {D : Set (Affine d)} (hD : IsOpen D) (e : Biholomorph W D)
    {f : ℕ → Affine n → Affine m} {M : ℝ}
    (hf : ∀ᶠ j in atTop, HolomorphicOnSubset W (fun x => f j x) ∧
      ∀ y ∈ W, ‖f j y‖ ≤ M) (p : W) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set W, A ∈ 𝓝 p ∧ ∀ᶠ j in atTop,
      ∀ q ∈ A, dist (f j q.val) (f j p.val) < ε := by
  let z : Affine d := (e.toHomeomorph p).val
  obtain ⟨r,hr,hrD⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds (e.toHomeomorph p).property)
  let A : Set W := {q | (e.toHomeomorph q).val ∈ ball z r ∧
      (2*M/r)*dist (e.toHomeomorph q).val z < ε}
  have hcc : Continuous (fun q : W => (e.toHomeomorph q).val) :=
    continuous_subtype_val.comp e.toHomeomorph.continuous
  have hA : A ∈ 𝓝 p := by
    have hball : ∀ᶠ q : W in 𝓝 p, (e.toHomeomorph q).val ∈ ball z r :=
      hcc.continuousAt.preimage_mem_nhds (ball_mem_nhds z hr)
    have hsmall : ∀ᶠ q : W in 𝓝 p, (2*M/r)*dist (e.toHomeomorph q).val z < ε := by
      have ht : Tendsto (fun q : W => (2*M/r)*dist (e.toHomeomorph q).val z)
          (𝓝 p) (𝓝 0) := by
        simpa only [z,dist_self,mul_zero] using (hcc.dist (continuous_const : Continuous (fun _ : W => z))).const_mul (2*M/r) |>.tendsto p
      exact (tendsto_order.mp ht).2 ε hε
    exact hball.and hsmall
  refine ⟨A,hA,?_⟩
  filter_upwards [hf] with j hj q hq
  let g := ambientExtend (fun x : D => (e.toHomeomorph.symm x).val)
  have hg : ∀ x : D, g x = (e.toHomeomorph.symm x).val := ambientExtend_apply _
  have hgz : g z = p.val := by rw [hg (e.toHomeomorph p),e.toHomeomorph.symm_apply_apply]
  have hgq : g (e.toHomeomorph q).val = q.val := by
    rw [hg (e.toHomeomorph q),e.toHomeomorph.symm_apply_apply]
  have hbound : ∀ x ∈ ball z r, ‖f j (g x)‖ ≤ M := by
    intro x hx
    rw [hg ⟨x,hrD hx⟩]
    exact hj.2 _ (e.toHomeomorph.symm ⟨x,hrD hx⟩).property
  have hmap : MapsTo (f j ∘ g) (ball z r)
      (closedBall ((f j ∘ g) z) (2*M)) := by
    intro x hx
    rw [mem_closedBall,dist_eq_norm]
    dsimp only [Function.comp_def]
    exact (norm_sub_le _ _).trans (by linarith [hbound x hx,hbound z (mem_ball_self hr)])
  have hb := Complex.dist_le_div_mul_dist_of_mapsTo_ball
    ((analytic_comp_chart_inverse hD e hj.1).differentiableOn.mono hrD) hmap hq.1
  change dist (f j (g (e.toHomeomorph q).val)) (f j (g z)) ≤ _ at hb
  rw [hgq,hgz] at hb
  exact hb.trans_lt hq.2

theorem eventual_equicontinuity_of_open_subset {X Y : Type*}
    [TopologicalSpace X] [PseudoMetricSpace Y] {S V : Set X}
    (hVS : V ⊆ S) (hV : IsOpen ((Subtype.val : S → X) ⁻¹' V))
    {p : X} (hpV : p ∈ V) {f : ℕ → X → Y} {ε : ℝ}
    (h : ∃ A : Set V, A ∈ 𝓝 (⟨p,hpV⟩ : V) ∧
      ∀ᶠ j in atTop, ∀ q ∈ A, dist (f j q.val) (f j p) < ε) :
    ∃ A : Set S, A ∈ 𝓝 (⟨p,hVS hpV⟩ : S) ∧
      ∀ᶠ j in atTop, ∀ q ∈ A, dist (f j q.val) (f j p) < ε := by
  obtain ⟨A,hA,he⟩ := h
  refine ⟨Set.inclusion hVS '' A,?_,?_⟩
  · have hi := Topology.IsOpenEmbedding.inclusion hVS hV
    rw [← hi.map_nhds_eq ⟨p,hpV⟩]
    exact Filter.image_mem_map hA
  · filter_upwards [he] with j hj q hq
    obtain ⟨v,hv,rfl⟩ := hq
    exact hj v hv

end Release061

end

end OAI
