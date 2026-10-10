import OAI.Geometry.Immersion.ClosedSurface.MetricModel

namespace OAI

/-! Arbitrarily small disjoint coordinate balls around a prescribed finite
set. Their closed supports remain inside the supplied chart neighborhoods. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem finite_point_chart_balls {M : Type*} [TopologicalSpace M] [T2Space M]
    (P : Finset M) (e : P → OpenPartialHomeomorph M Plane)
    (he : ∀ p, (p : M) ∈ (e p).source) (U : P → Set M)
    (hU : ∀ p, IsOpen (U p)) (hpU : ∀ p, (p : M) ∈ U p)
    {η : ℝ} (hη : 0 < η) :
    ∃ r : P → ℝ, (∀ p, 0 < r p ∧ r p < η ∧
      closedBall (e p p) (r p) ⊆ (e p).target ∩ (e p).symm ⁻¹' U p) ∧
      Pairwise (fun p q => Disjoint ((e p).symm '' closedBall (e p p) (r p))
        ((e q).symm '' closedBall (e q q) (r q))) := by
  classical
  obtain ⟨V,hV,hdisj⟩ := P.finite_toSet.t2_separation
  have hex (p : P) : ∃ r : ℝ, 0 < r ∧ r < η ∧
      closedBall (e p p) r ⊆ (e p).target ∩ (e p).symm ⁻¹' (U p ∩ V p) := by
    have ho := (e p).isOpen_inter_preimage_symm ((hU p).inter (hV p).2)
    have hp : e p p ∈ (e p).target ∩ (e p).symm ⁻¹' (U p ∩ V p) := by
      refine ⟨(e p).map_source (he p),?_⟩
      change (e p).symm (e p p) ∈ U p ∩ V p
      rw [(e p).left_inv (he p)]
      exact ⟨hpU p,(hV p).1⟩
    obtain ⟨r,hr,hrsub⟩ := nhds_basis_closedBall.mem_iff.mp (ho.mem_nhds hp)
    refine ⟨min r (η/2),lt_min hr (half_pos hη),?_,?_⟩
    · exact (min_le_right r (η/2)).trans_lt (half_lt_self hη)
    · exact (closedBall_subset_closedBall (min_le_left r (η/2))).trans hrsub
  choose r hr hrη hrsub using hex
  refine ⟨r,fun p => ⟨hr p,hrη p,?_⟩,?_⟩
  · intro x hx
    exact ⟨(hrsub p hx).1,(hrsub p hx).2.1⟩
  · intro p q hpq
    apply Set.disjoint_left.mpr
    rintro x ⟨y,hy,rfl⟩ ⟨z,hz,heq⟩
    have hpV := (hrsub p hy).2.2
    have hqV := (hrsub q hz).2.2
    exact Set.disjoint_left.mp (hdisj p.property q.property
      (fun hpq' => hpq (Subtype.ext hpq'))) hpV (heq ▸ hqV)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
