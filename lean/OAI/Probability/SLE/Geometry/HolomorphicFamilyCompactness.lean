import OAI.Probability.SLE.Geometry.HolomorphicFamilyEquicontinuity

namespace OAI

/-! Sequential compactness of locally bounded holomorphic half-plane
families, with the ordinary compact-open topology. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

local instance halfPlaneFamilyLocallyCompact : LocallyCompactSpace upperHalfPlane :=
  isOpen_upperHalfPlane.locallyCompactSpace

local instance halfPlaneUniformOnT2 :
    T2Space (UniformOnFun upperHalfPlane ℂ {K | IsCompact K}) :=
  UniformOnFun.t2Space_of_covering (by
    apply eq_univ_iff_forall.mpr
    intro z
    exact mem_sUnion.mpr ⟨{z},isCompact_singleton,mem_singleton z⟩)

lemma holomorphic_halfPlane_family_subsequence
    (f : ℕ → ℂ → ℂ) (hf : ∀ n, DifferentiableOn ℂ (f n) upperHalfPlane)
    (hb : ∀ K : Set ℂ, IsCompact K → K⊆upperHalfPlane →
      ∃ C : ℝ, ∀ n, ∀ z∈K, ‖f n z‖≤C) :
    ∃ (g : C(upperHalfPlane,ℂ)) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n => (⟨fun z => f (φ n) z,(hf (φ n)).continuousOn.domRestrict⟩ :
        C(upperHalfPlane,ℂ))) atTop (𝓝 g) := by
  let F : ℕ → C(upperHalfPlane,ℂ) :=
    fun n => ⟨fun z => f n z,(hf n).continuousOn.domRestrict⟩
  have hEq := holomorphic_halfPlane_family_equicontinuous f hf hb
  have hES : Equicontinuous (fun (q : range F) (z : upperHalfPlane) => q.1 z) := by
    intro z
    apply Metric.equicontinuousAt_iff_right.mpr
    intro ε hε
    filter_upwards [Metric.equicontinuousAt_iff_right.mp (hEq z) ε hε] with w hw q
    obtain ⟨n,hn⟩ := q.property
    rw [← hn]
    change dist (f n z.1) (f n w.1)<ε
    exact hw n
  have hcompact : IsCompact (closure (range F)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun q : C(upperHalfPlane,ℂ) => (q : upperHalfPlane → ℂ))
      (𝔖 := {K : Set upperHalfPlane | IsCompact K})
      (fun _ h => h) ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K _
      exact hES.equicontinuousOn K
    · intro K _ z _
      obtain ⟨C,hC⟩ := hb {z.1} isCompact_singleton (singleton_subset_iff.mpr z.property)
      refine ⟨closedBall (0:ℂ) (max C 0),isCompact_closedBall _ _,?_⟩
      rintro _ ⟨n,rfl⟩
      rw [mem_closedBall,dist_zero_right]
      change ‖f n z.1‖ ≤ max C 0
      exact (hC n z.1 (mem_singleton z.1)).trans (le_max_left _ _)
  obtain ⟨g,_,φ,hφ,hconv⟩ := hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  exact ⟨g,φ,hφ,hconv⟩

end SLEExactGauge

end

end OAI
