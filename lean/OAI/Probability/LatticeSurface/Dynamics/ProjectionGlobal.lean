import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionTransmission
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodGlobal

namespace OAI

namespace ProjectionComparison

open Set Filter ClusterDisplacement

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype E] in
lemma exists_global_projection_path (S : System V E) (b h : V → ℝ) (hh : h∈feasible S b)
    (c : FreeSpace S) (r R : ℝ) (hr : 0 < r) (hball : Metric.closedBall c r⊆freeCarrier S b)
    (hR : ∀v∈freeCarrier S b,‖v-c‖≤R)
    (w : ℝ → FreeSpace S) (hw : ContinuousOn w (Icc 0 1)) :
    ∃u : ℝ → V → ℝ,ContinuousOn u (Icc 0 1) ∧ u 0=h ∧
      (∀t∈Icc (0:ℝ) 1,u t∈feasible S b) ∧
      TendstoUniformlyOn (fun n => pathMesh S b h hh w (n+1)) u atTop (Icc 0 1) := by
  obtain ⟨B,hB,he⟩ := exists_free_body S b ⟨h,hh⟩
  have hh' : freeCoordinates S h∈B.carrier := by
    rw [hB];change extendFree S b (freeCoordinates S h)∈feasible S b
    rwa [extendFree_coordinates S b h hh.2]
  obtain ⟨v,k,μ,hvcont,hkcont,hv₀,hk₀,hvbody,hv,hrest⟩ := ConvexSkorokhod.reflected_equation B
    (freeCoordinates S h) c r R hh' hr (by rwa [hB]) (by rwa [hB]) w hw
  let u := fun t => extendFree S b (v t)
  have hlim : TendstoUniformlyOn (fun n => pathMesh S b h hh w (n+1)) u atTop (Icc 0 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hv ε hε] with n hn t ht
    rw [pathMesh_eq_hilbert S b h hh B he]
    exact ((extendFree_lipschitz S b).dist_le_mul _ _).trans_lt (by simpa using hn t ht)
  refine ⟨u,(extendFree_continuous S b).comp_continuousOn hvcont,?_,fun t ht => ?_,hlim⟩
  · have hhlim := hlim.tendsto_at (show (0:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)
    have hhmesh : (fun n => pathMesh S b h hh w (n+1) 0)=fun _ : ℕ => h := by
      funext n;simp [pathMesh,recursion]
    rw [hhmesh] at hhlim
    exact tendsto_nhds_unique hhlim tendsto_const_nhds
  · have hmem := (hvbody t ht).1
    rwa [hB] at hmem

end ProjectionComparison

namespace ProjectionComparison

open Set Filter ClusterDisplacement

attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E]

theorem common_global_projection_cluster_tail (S : System V E) (b₀ b₁ h₀ h₁ : V → ℝ)
    (hh₀ : h₀∈feasible S b₀) (hh₁ : h₁∈feasible S b₁)
    (c₀ c₁ : FreeSpace S) (r R : ℝ) (hr : 0<r)
    (hball₀ : Metric.closedBall c₀ r⊆freeCarrier S b₀)
    (hball₁ : Metric.closedBall c₁ r⊆freeCarrier S b₁)
    (hR₀ : ∀v∈freeCarrier S b₀,‖v-c₀‖≤R)
    (hR₁ : ∀v∈freeCarrier S b₁,‖v-c₁‖≤R)
    (w : ℝ → FreeSpace S) (hw : ContinuousOn w (Icc 0 1))
    (a : ℝ) (hb : ∀x∈S.pins,b₁ x-b₀ x≤a) :
    ∃u₀ u₁ : ℝ → V → ℝ,
      ContinuousOn u₀ (Icc 0 1) ∧ ContinuousOn u₁ (Icc 0 1) ∧
      u₀ 0=h₀ ∧ u₁ 0=h₁ ∧
      (∀t∈Icc (0:ℝ) 1,u₀ t∈feasible S b₀ ∧ u₁ t∈feasible S b₁) ∧
      TendstoUniformlyOn (fun n => pathMesh S b₀ h₀ hh₀ w (n+1)) u₀ atTop (Icc 0 1) ∧
      TendstoUniformlyOn (fun n => pathMesh S b₁ h₁ hh₁ w (n+1)) u₁ atTop (Icc 0 1) ∧
      ∀δ>0,∀root : {x // x∉S.pins},
        let W := transmissionSet S u₀ u₁ δ root
        0≤energy (componentPathTail S W u₀ u₁ a 0)-energy (componentPathTail S W u₀ u₁ a 1) ∧
        ∀t∈Icc (0:ℝ) 1,∀x : {x : W // x.val∉S.pins},
          |componentPathTail S W u₀ u₁ a t x-componentPathTail S W u₀ u₁ a 0 x|≤
            5*(Fintype.card {x : W // x.val∉S.pins}+1:ℝ)*
              Real.sqrt (energy (componentPathTail S W u₀ u₁ a 0)-energy (componentPathTail S W u₀ u₁ a 1)) := by
  obtain ⟨u₀,hcont₀,hu₀₀,hmem₀,hlim₀⟩ := exists_global_projection_path S b₀ h₀ hh₀ c₀ r R hr hball₀ hR₀ w hw
  obtain ⟨u₁,hcont₁,hu₁₀,hmem₁,hlim₁⟩ := exists_global_projection_path S b₁ h₁ hh₁ c₁ r R hr hball₁ hR₁ w hw
  refine ⟨u₀,u₁,hcont₀,hcont₁,hu₀₀,hu₁₀,fun t ht => ⟨hmem₀ t ht,hmem₁ t ht⟩,hlim₀,hlim₁,?_⟩
  intro δ hδ root
  exact transmission_cluster_tail S b₀ b₁ h₀ h₁ hh₀ hh₁ w u₀ u₁ hlim₀ hlim₁ δ hδ root a hb

end ProjectionComparison

end OAI
