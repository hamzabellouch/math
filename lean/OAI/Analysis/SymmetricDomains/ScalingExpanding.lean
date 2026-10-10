import Mathlib
import OAI.Analysis.SymmetricDomains.ScalingEmbeddedCharts
import OAI.Analysis.SymmetricDomains.ExpandingBiholomorphismsCharts

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

theorem HolomorphicOnSubset.analyticOnNhd_of_open {n m : ℕ}
    {S : Set (Affine n)} (hS : IsOpen S) {f : Affine n → Affine m}
    (hf : HolomorphicOnSubset S (fun x => f x)) : AnalyticOnNhd ℂ f S := by
  intro x hx
  apply (hf.analyticOnNhd_extend hS x hx).congr
  filter_upwards [hS.mem_nhds hx] with y hy
  exact ambientExtend_apply _ ⟨y,hy⟩

theorem scaling_biholomorph_expanding {n m : ℕ}
    {S : Set (Affine n)} {O : Set (Affine m)} {y₀ : Affine m}
    (hy₀ : y₀ ∈ O) (hconn : IsPreconnected S) (hO : IsOpen O)
    (A : ℕ → Set (Affine n)) (B : ℕ → Set (Affine m))
    (hAS : ∀ j, A j ⊆ S)
    (hAo : ∀ j, IsOpen ((Subtype.val : S → Affine n) ⁻¹' A j))
    (hBo : ∀ j, IsOpen (B j)) (b : ∀ j, Biholomorph (A j) (B j))
    {f : ℕ → Affine n → Affine m} {g : ℕ → Affine m → Affine n}
    {F : Affine n → Affine m} {G : Affine m → Affine n}
    (hbf : ∀ j (x : A j), f j x.val = ((b j).toHomeomorph x).val)
    (hbg : ∀ j (y : B j), g j y.val = ((b j).toHomeomorph.symm y).val)
    (hf : TendstoLocallyUniformlyOn f F atTop S)
    (hg : TendstoLocallyUniformlyOn g G atTop (connectedComponentIn O y₀))
    (hcoverA : ∀ K : Set (Affine n), IsCompact K → K ⊆ S →
      ∀ᶠ j in atTop, K ⊆ A j)
    (hcoverB : ∀ K : Set (Affine m), IsCompact K → K ⊆ connectedComponentIn O y₀ →
      ∀ᶠ j in atTop, K ⊆ B j)
    (hGmap : MapsTo G (connectedComponentIn O y₀) S)
    (hexcluded : ∀ y ∉ O, ∃ a : ℕ → Affine m,
      Tendsto a atTop (𝓝 y) ∧ ∀ᶠ j in atTop, a j ∉ B j) :
    Nonempty (Biholomorph S (connectedComponentIn O y₀)) := by
  have hD := hO.connectedComponentIn (x := y₀)
  have hgj : ∀ j, AnalyticOnNhd ℂ (g j) (B j) := by
    intro j
    apply HolomorphicOnSubset.analyticOnNhd_of_open (hBo j)
    intro p
    obtain ⟨V,hVo,hpV,φ,hφ,he⟩ := (b j).holomorphic_invFun p
    refine ⟨V,hVo,hpV,φ,hφ,?_⟩
    intro q hq
    change φ q.val = g j q.val
    rw [hbg j q]
    exact he q hq
  have hGhol : AnalyticOnNhd ℂ G (connectedComponentIn O y₀) := by
    apply analyticOnNhd_of_differentiableOn_affine hD
    apply differentiableOn_of_locally_uniform_limit hD hg
    intro y hy
    obtain ⟨R,hR,hRD⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hy)
    have hclosed : closedBall y (R/2) ⊆ connectedComponentIn O y₀ :=
      (closedBall_subset_ball (by linarith)).trans hRD
    refine ⟨ball y (R/2),ball_mem_nhds y (half_pos hR),?_⟩
    filter_upwards [hcoverB _ (isCompact_closedBall _ _) hclosed] with j hj
    exact (hgj j).differentiableOn.mono (ball_subset_closedBall.trans hj)
  have hcoverAp : ∀ x ∈ S, ∀ᶠ j in atTop, x ∈ A j := by
    intro x hx
    exact (hcoverA {x} isCompact_singleton (singleton_subset_iff.mpr hx)).mono
      fun j hj => hj (mem_singleton x)
  have hcoverBp : ∀ y ∈ connectedComponentIn O y₀, ∀ᶠ j in atTop, y ∈ B j := by
    intro y hy
    exact (hcoverB {y} isCompact_singleton (singleton_subset_iff.mpr hy)).mono
      fun j hj => hj (mem_singleton y)
  refine scaling_biholomorph_embedded_charts (T := B) hy₀ hconn hO hf hg
    (expanding_biholomorphisms_charts A B hAS hAo hBo b f hbf hcoverA) hGhol ?_ hGmap ?_ ?_ ?_ ?_
  · intro K hK hKS
    filter_upwards [hcoverA K hK hKS] with j hj x hx
    rw [hbf j ⟨x,hj hx⟩]
    exact ((b j).toHomeomorph ⟨x,hj hx⟩).property
  · intro y hy
    filter_upwards [hcoverBp y hy] with j hj
    rw [hbg j ⟨y,hj⟩]
    exact hAS j ((b j).toHomeomorph.symm ⟨y,hj⟩).property
  · intro y hy
    filter_upwards [hcoverBp y hy] with j hj
    rw [hbg j ⟨y,hj⟩,hbf j ((b j).toHomeomorph.symm ⟨y,hj⟩),
      (b j).toHomeomorph.apply_symm_apply]
  · intro x hx
    filter_upwards [hcoverAp x hx] with j hj
    rw [hbf j ⟨x,hj⟩,hbg j ((b j).toHomeomorph ⟨x,hj⟩),
      (b j).toHomeomorph.symm_apply_apply]
  · exact hexcluded

end Release061

end

end OAI
