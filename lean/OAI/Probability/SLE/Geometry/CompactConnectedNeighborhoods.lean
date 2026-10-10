import OAI.Probability.SLE.Geometry.FiniteTraceTopology

namespace OAI

/-! Uniform small connected neighborhoods on compact locally connected
 metric spaces, specialized below to finite trace segments. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology NNReal

namespace SLEExactGauge

lemma compact_locallyConnected_uniform_connection {A : Type*} [MetricSpace A]
    [CompactSpace A] [LocallyConnectedSpace A] (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ x y : A, dist x y<δ →
      ∃ V : Set A, IsPreconnected V ∧ x∈V ∧ y∈V ∧
        ∀ u∈V, ∀ v∈V, dist u v<ε := by
  classical
  have hlocal (a : A) : ∃ V : Set A, V∈𝓝 a ∧ IsPreconnected V ∧
      V⊆ball a (ε/2) :=
    (locallyConnectedSpace_iff_connected_subsets.mp inferInstance) a _
      (ball_mem_nhds a (half_pos hε))
  choose V hV hc hs using hlocal
  obtain ⟨δ,hδ,hcover⟩ := Metric.uniformity_basis_dist.lebesgue_number_lemma_nhds
    (K := (univ : Set A)) isCompact_univ (fun a _ => hV a)
  refine ⟨δ,hδ,fun x y hxy => ?_⟩
  obtain ⟨a,ha⟩ := hcover x (mem_univ x)
  have hsub : ball x δ⊆V a := by
    intro z hz
    apply ha
    change dist x z<δ
    simpa only [mem_ball,dist_comm] using hz
  refine ⟨V a,hc a,hsub (mem_ball_self hδ),hsub (by simpa only [mem_ball,dist_comm] using hxy),?_⟩
  intro u hu v hv
  have hu' := mem_ball.mp (hs a hu)
  have hv' := mem_ball.mp (hs a hv)
  have := dist_triangle u a v
  rw [dist_comm a v] at this
  linarith

lemma finiteTrace_uniform_connection {γ : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (T : ℝ≥0) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ x∈γ '' Icc 0 T, ∀ y∈γ '' Icc 0 T, dist x y<δ →
      ∃ C : Set ℂ, C⊆γ '' Icc 0 T ∧ IsPreconnected C ∧ x∈C ∧ y∈C ∧
        ∀ u∈C, ∀ v∈C, dist u v<ε := by
  have : CompactSpace (γ '' Icc 0 T) := isCompact_iff_compactSpace.mp (finiteTrace_isCompact hγ T)
  have : LocallyConnectedSpace (γ '' Icc 0 T) := finiteTrace_locallyConnected hγ T
  obtain ⟨δ,hδ,hconn⟩ := compact_locallyConnected_uniform_connection
    (A := γ '' Icc 0 T) ε hε
  refine ⟨δ,hδ,fun x hx y hy hxy => ?_⟩
  obtain ⟨V,hV,hxV,hyV,hd⟩ := hconn ⟨x,hx⟩ ⟨y,hy⟩ hxy
  refine ⟨Subtype.val '' V,?_,hV.image _ continuous_subtype_val.continuousOn,
    ⟨⟨x,hx⟩,hxV,rfl⟩,⟨⟨y,hy⟩,hyV,rfl⟩,?_⟩
  · rintro _ ⟨z,_,rfl⟩
    exact z.property
  · rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩
    exact hd u hu v hv

end SLEExactGauge

end

end OAI
