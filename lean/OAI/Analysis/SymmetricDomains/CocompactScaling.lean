import Mathlib
import OAI.Analysis.SymmetricDomains.ForwardLocalDataCompact

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

theorem cocompact_scaling_biholomorph {n m : ℕ} {Γ : Type*}
    {U : Set (Affine n)} [LocallyCompactSpace U]
    (hconn : IsPreconnected U) (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    {O : Set (Affine m)} {y₀ : Affine m} (hO : IsOpen O) (hy₀ : y₀ ∈ O)
    (A : ℕ → Set (Affine n)) (B : ℕ → Set (Affine m))
    (hAU : ∀ j, A j ⊆ U)
    (hAo : ∀ j, IsOpen ((Subtype.val : U → Affine n) ⁻¹' A j))
    (hBo : ∀ j, IsOpen (B j)) (b : ∀ j, Biholomorph (A j) (B j))
    (f : ℕ → Affine n → Affine m) (g : ℕ → Affine m → Affine n)
    (hbf : ∀ j (x : A j), f j x.val = ((b j).toHomeomorph x).val)
    (hbg : ∀ j (y : B j), g j y.val = ((b j).toHomeomorph.symm y).val)
    (hcoverA : ∀ C : Set (Affine n), IsCompact C → C ⊆ U → ∀ᶠ j in atTop, C ⊆ A j)
    (hcoverB : ∀ C : Set (Affine m), IsCompact C → C ⊆ connectedComponentIn O y₀ →
      ∀ᶠ j in atTop, C ⊆ B j)
    (hbound : ∀ C : Set (Affine n), IsCompact C → C ⊆ U →
      ∃ M : ℝ, 0 < M ∧ ∀ᶠ j in atTop, ∀ x ∈ C, ‖f j x‖ ≤ M)
    (hbase : ∃ C : Set U, IsCompact C ∧ ∀ᶠ j in atTop, g j y₀ ∈ Subtype.val '' C)
    (hexcluded : ∀ y ∉ O, ∃ a : ℕ → Affine m,
      Tendsto a atTop (𝓝 y) ∧ ∀ᶠ j in atTop, a j ∉ B j) :
    Nonempty (Biholomorph U (connectedComponentIn O y₀)) := by
  let : ContinuousConstSMul Γ U := ⟨fun γ => ((hhol γ).continuous).subtype_mk _⟩
  obtain ⟨K,hK,hrep⟩ := exists_compact_orbit_representatives (X := U) (Γ := Γ)
  have hS : IsSmooth U := smooth_of_expanding_biholomorphisms A B hAU hAo hBo b (by
    intro x hx
    exact (hcoverA {x} isCompact_singleton (singleton_subset_iff.mpr hx)).mono
      fun j hj => hj (mem_singleton x))
  obtain ⟨F,_hFa,φ,hφ,hfconv⟩ := hS.montel_expanding f
    (forward_local_data_of_compact_bounds A B b f hbf hcoverA hbound)
  have hD := hO.connectedComponentIn (x := y₀)
  have hgj : ∀ j, AnalyticOnNhd ℂ (g j) (B j) := by
    intro j
    apply HolomorphicOnSubset.analyticOnNhd_of_open (hBo j)
    convert (b j).holomorphic_invFun using 1
    funext y
    exact hbg j y
  obtain ⟨M,hM,hMU⟩ := hbounded.exists_pos_norm_le
  have hlocalg : ∀ x ∈ connectedComponentIn O y₀, ∃ r : ℝ, 0 < r ∧
      ∃ M : ℝ, 0 < M ∧ ball x r ⊆ connectedComponentIn O y₀ ∧
      ∀ᶠ j in atTop, DifferentiableOn ℂ (g (φ j)) (ball x r) ∧
        ∀ y ∈ ball x r, ‖g (φ j) y‖ ≤ M := by
    intro x hx
    obtain ⟨r,hr,hrD⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hx)
    have hclosed : closedBall x (r/2) ⊆ connectedComponentIn O y₀ :=
      (closedBall_subset_ball (by linarith)).trans hrD
    refine ⟨r/2,half_pos hr,M,hM,ball_subset_closedBall.trans hclosed,?_⟩
    filter_upwards [hφ.tendsto_atTop (hcoverB _ (isCompact_closedBall _ _) hclosed)] with j hj
    refine ⟨(hgj (φ j)).differentiableOn.mono (ball_subset_closedBall.trans hj),?_⟩
    intro y hy
    have hyB := hj (ball_subset_closedBall hy)
    rw [hbg (φ j) ⟨y,hyB⟩]
    exact hMU _ (hAU (φ j) ((b (φ j)).toHomeomorph.symm ⟨y,hyB⟩).property)
  obtain ⟨G,_hGa,ψ,hψ,hgconv⟩ := analytic_montel_expanding_domains hD
    (fun j => g (φ j)) hlocalg
  have hφψ : Tendsto (fun j => φ (ψ j)) atTop atTop :=
    hφ.tendsto_atTop.comp hψ.tendsto_atTop
  have hfconv' : TendstoLocallyUniformlyOn (fun j => f (φ (ψ j))) F atTop U := by
    intro V hV x hx
    obtain ⟨W,hW,he⟩ := hfconv V hV x hx
    exact ⟨W,hW,hψ.tendsto_atTop he⟩
  apply cocompact_scaling_biholomorph_of_limits hconn hbounded hhol K hK hrep hO hy₀
    (fun j => A (φ (ψ j))) (fun j => B (φ (ψ j)))
    (fun j => hAU (φ (ψ j))) (fun j => hAo (φ (ψ j))) (fun j => hBo (φ (ψ j)))
    (fun j => b (φ (ψ j))) (fun j => f (φ (ψ j))) (fun j => g (φ (ψ j)))
    (fun j => hbf (φ (ψ j))) (fun j => hbg (φ (ψ j))) F G hfconv' hgconv
  · intro C hC hCU
    exact hφψ (hcoverA C hC hCU)
  · intro C hC hCD
    exact hφψ (hcoverB C hC hCD)
  · obtain ⟨C,hC,he⟩ := hbase
    exact ⟨C,hC,hφψ he⟩
  · intro y hy
    obtain ⟨a,ha,he⟩ := hexcluded y hy
    exact ⟨fun j => a (φ (ψ j)),ha.comp hφψ,hφψ he⟩

end Release061

end

end OAI
