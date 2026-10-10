import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionLimitSupport

namespace OAI

namespace ProjectionComparison

open Set Filter ClusterDisplacement

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

theorem common_projection_limit_tail (S : System V E) (b₀ b₁ h₀ h₁ : V → ℝ)
    (hh₀ : h₀∈feasible S b₀) (hh₁ : h₁∈feasible S b₁)
    (c₀ c₁ : FreeSpace S) (r : ℝ) (hr : 0 < r)
    (hball₀ : Metric.closedBall c₀ r⊆freeCarrier S b₀)
    (hball₁ : Metric.closedBall c₁ r⊆freeCarrier S b₁)
    (w : ℝ → FreeSpace S) (hw : ContinuousOn w (Icc 0 1))
    (hosc : ∀t∈Icc (0:ℝ) 1,‖w t-w 0‖ ≤ r/2)
    (a : ℝ) (hb : ∀x∈S.pins,b₁ x-b₀ x ≤ a) :
    ∃u₀ u₁ : ℝ → V → ℝ,
      ContinuousOn u₀ (Icc 0 1) ∧ ContinuousOn u₁ (Icc 0 1) ∧
      u₀ 0=h₀ ∧ u₁ 0=h₁ ∧
      (∀t∈Icc (0:ℝ) 1,u₀ t∈feasible S b₀ ∧ u₁ t∈feasible S b₁) ∧
      TendstoUniformlyOn (fun n => pathMesh S b₀ h₀ hh₀ w (n+1)) u₀ atTop (Icc 0 1) ∧
      TendstoUniformlyOn (fun n => pathMesh S b₁ h₁ hh₁ w (n+1)) u₁ atTop (Icc 0 1) ∧
      ∀t∈Icc (0:ℝ) 1,∀x:{x // x∉S.pins},
        |pathTail S u₀ u₁ a t x-pathTail S u₀ u₁ a 0 x| ≤
          5*(Fintype.card {x // x∉S.pins}+1:ℝ)*
            Real.sqrt (energy (pathTail S u₀ u₁ a 0)-energy (pathTail S u₀ u₁ a 1)) := by
  obtain ⟨u₀,hcont₀,hu₀₀,hmem₀,hlim₀⟩ := exists_projection_path S b₀ h₀ hh₀ c₀ r hr hball₀ w hw hosc
  obtain ⟨u₁,hcont₁,hu₁₀,hmem₁,hlim₁⟩ := exists_projection_path S b₁ h₁ hh₁ c₁ r hr hball₁ w hw hosc
  refine ⟨u₀,u₁,hcont₀,hcont₁,hu₀₀,hu₁₀,fun t ht => ⟨hmem₀ t ht,hmem₁ t ht⟩,hlim₀,hlim₁,?_⟩
  let F : ℕ → ℝ → {x // x∉S.pins} → ℝ := fun n t =>
    meshTail S b₀ b₁ h₀ h₁ hh₀ hh₁ (pathIncrement S w (n+1)) a ⌊t*((n+1:ℕ):ℝ)⌋₊
  have hF : ∀t∈Icc (0:ℝ) 1,∀x:{x // x∉S.pins},
      Tendsto (fun n => F n t x) atTop (nhds (pathTail S u₀ u₁ a t x)) := by
    intro t ht x
    have h₀ := tendsto_pi_nhds.mp (hlim₀.tendsto_at ht) x
    have h₁ := tendsto_pi_nhds.mp (hlim₁.tendsto_at ht) x
    simpa only [F,meshTail,pathTail,pathMesh] using (((h₁.sub h₀).sub_const a).max (tendsto_const_nhds (x:=(0:ℝ))))
  have hEt : ∀t∈Icc (0:ℝ) 1,
      Tendsto (fun n => energy (F n t)) atTop (nhds (energy (pathTail S u₀ u₁ a t))) := by
    intro t ht
    exact tendsto_finsetSum _ fun x hx => (hF t ht x).pow 2
  have ht₀ : (0:ℝ)∈Icc (0:ℝ) 1 := by constructor <;> norm_num
  have ht₁ : (1:ℝ)∈Icc (0:ℝ) 1 := by constructor <;> norm_num
  intro t ht x
  have hleft := ((hF t ht x).sub (hF 0 ht₀ x)).abs
  have hright := ((hEt 0 ht₀).sub (hEt 1 ht₁)).sqrt.const_mul
    (5*(Fintype.card {x // x∉S.pins}+1:ℝ))
  apply le_of_tendsto_of_tendsto hleft hright
  apply Eventually.of_forall
  intro n
  have hk : ⌊t*((n+1:ℕ):ℝ)⌋₊ ≤ n+1 := Nat.floor_le_of_le
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (Nat.cast_nonneg (n+1)))
  have hh := projection_mesh_tail_displacement S b₀ b₁ h₀ h₁ hh₀ hh₁
    (pathIncrement S w (n+1)) a hb (n+1) ⌊t*((n+1:ℕ):ℝ)⌋₊ hk x
  simpa only [F,zero_mul,one_mul,Nat.floor_zero,Nat.floor_natCast] using hh

end ProjectionComparison

end OAI
