import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionComponentEnergy
import OAI.Probability.LatticeSurface.Dynamics.ProjectionComponentLimitSupport

namespace OAI

namespace ProjectionComparison

open Set Filter ClusterDisplacement

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

theorem transmission_component_tail (S : System V E) (W : Set V) (hW : S.pins⊆W)
    (b₀ b₁ h₀ h₁ : V → ℝ) (hh₀ : h₀∈feasible S b₀) (hh₁ : h₁∈feasible S b₁)
    (w : ℝ → FreeSpace S) (u₀ u₁ : ℝ → V → ℝ)
    (hlim₀ : TendstoUniformlyOn (fun n => pathMesh S b₀ h₀ hh₀ w (n+1)) u₀ atTop (Icc 0 1))
    (hlim₁ : TendstoUniformlyOn (fun n => pathMesh S b₁ h₁ hh₁ w (n+1)) u₁ atTop (Icc 0 1))
    (δ : ℝ) (hδ : 0<δ)
    (hcut₀ : ∀t∈Icc (0:ℝ) 1,∀e,S.cost e-(u₀ t (S.left e)-u₀ t (S.right e))≤δ →
      S.left e∉S.pins → S.right e∉S.pins → (S.left e∈W ↔ S.right e∈W))
    (hcut₁ : ∀t∈Icc (0:ℝ) 1,∀e,S.cost e-(u₁ t (S.left e)-u₁ t (S.right e))≤δ →
      S.left e∉S.pins → S.right e∉S.pins → (S.left e∈W ↔ S.right e∈W))
    (a : ℝ) (hb : ∀x∈S.pins,b₁ x-b₀ x≤a) :
    0≤energy (componentPathTail S W u₀ u₁ a 0)-energy (componentPathTail S W u₀ u₁ a 1) ∧
    ∀t∈Icc (0:ℝ) 1,∀x : {x : W // x.val∉S.pins},
      |componentPathTail S W u₀ u₁ a t x-componentPathTail S W u₀ u₁ a 0 x|≤
        5*(Fintype.card {x : W // x.val∉S.pins}+1:ℝ)*
          Real.sqrt (energy (componentPathTail S W u₀ u₁ a 0)-energy (componentPathTail S W u₀ u₁ a 1)) := by
  have hc₀ := pathMesh_cut_eventually S W b₀ h₀ hh₀ w u₀ hlim₀ δ hδ hcut₀
  have hc₁ := pathMesh_cut_eventually S W b₁ h₁ hh₁ w u₁ hlim₁ δ hδ hcut₁
  let F : ℕ → ℝ → {x : W // x.val∉S.pins} → ℝ := fun n t =>
    componentMeshTail S W b₀ b₁ h₀ h₁ hh₀ hh₁ (pathIncrement S w (n+1)) a ⌊t*((n+1:ℕ):ℝ)⌋₊
  have hF : ∀t∈Icc (0:ℝ) 1,∀x : {x : W // x.val∉S.pins},
      Tendsto (fun n => F n t x) atTop (nhds (componentPathTail S W u₀ u₁ a t x)) := by
    intro t ht x
    have h₀ := tendsto_pi_nhds.mp (hlim₀.tendsto_at ht) x.val.val
    have h₁ := tendsto_pi_nhds.mp (hlim₁.tendsto_at ht) x.val.val
    simpa only [F,componentMeshTail,meshTail,componentPathTail,pathMesh] using
      (((h₁.sub h₀).sub_const a).max (tendsto_const_nhds (x:=(0:ℝ))))
  have hEt : ∀t∈Icc (0:ℝ) 1,
      Tendsto (fun n => energy (F n t)) atTop (nhds (energy (componentPathTail S W u₀ u₁ a t))) := by
    intro t ht
    exact tendsto_finsetSum _ fun x hx => (hF t ht x).pow 2
  have ht₀ : (0:ℝ)∈Icc (0:ℝ) 1 := by constructor <;> norm_num
  have ht₁ : (1:ℝ)∈Icc (0:ℝ) 1 := by constructor <;> norm_num
  constructor
  · apply le_of_tendsto_of_tendsto tendsto_const_nhds ((hEt 0 ht₀).sub (hEt 1 ht₁))
    filter_upwards [hc₀,hc₁] with n hn₀ hn₁
    have he := component_mesh_loss_nonneg S W hW b₀ b₁ h₀ h₁ hh₀ hh₁
      (pathIncrement S w (n+1)) a hb (n+1) hn₀ hn₁
    simpa only [F,zero_mul,one_mul,Nat.floor_zero,Nat.floor_natCast] using he
  · intro t ht x
    have hleft := ((hF t ht x).sub (hF 0 ht₀ x)).abs
    have hright := ((hEt 0 ht₀).sub (hEt 1 ht₁)).sqrt.const_mul
      (5*(Fintype.card {x : W // x.val∉S.pins}+1:ℝ))
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [hc₀,hc₁] with n hn₀ hn₁
    have hk : ⌊t*((n+1:ℕ):ℝ)⌋₊ ≤ n+1 := Nat.floor_le_of_le
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (Nat.cast_nonneg (n+1)))
    have he := component_mesh_displacement S W hW b₀ b₁ h₀ h₁ hh₀ hh₁
      (pathIncrement S w (n+1)) a hb (n+1) hn₀ hn₁ ⌊t*((n+1:ℕ):ℝ)⌋₊ hk x
    simpa only [F,zero_mul,one_mul,Nat.floor_zero,Nat.floor_natCast] using he

end ProjectionComparison

end OAI
