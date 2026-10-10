import OAI.Geometry.SurfaceImmersion.Whitney.RegularCrosscapRepresentatives

namespace OAI

/-! Disjoint coordinate neighborhoods for the finite crosscap set. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem finite_crosscap_chart_balls {M : Type*} [TopologicalSpace M] [T2Space M]
    (P : Finset M) (e : P → OpenPartialHomeomorph M Base)
    (he : ∀ p, (p : M) ∈ (e p).source) (O : P → Set Base)
    (hO : ∀ p, IsOpen (O p)) (hpO : ∀ p, e p p ∈ O p) :
    ∃ r : P → ℝ, (∀ p, 0 < r p ∧
      closedBall (e p p) (r p) ⊆ (e p).target ∩ O p) ∧
      Pairwise (fun p q => Disjoint ((e p).symm '' closedBall (e p p) (r p))
        ((e q).symm '' closedBall (e q q) (r q))) := by
  classical
  obtain ⟨V,hV,hdisj⟩ := P.finite_toSet.t2_separation
  have hex (p : P) : ∃ r : ℝ, 0 < r ∧
      closedBall (e p p) r ⊆ ((e p).target ∩ O p) ∩ (e p).symm ⁻¹' V p := by
    have ho : IsOpen (((e p).target ∩ O p) ∩ (e p).symm ⁻¹' V p) := by
      have hv := (e p).isOpen_inter_preimage_symm (hV p).2
      have heq : ((e p).target ∩ O p) ∩ (e p).symm ⁻¹' V p =
          ((e p).target ∩ (e p).symm ⁻¹' V p) ∩ O p := by
        ext x
        simp only [mem_inter_iff,mem_preimage]
        tauto
      rw [heq]
      exact hv.inter (hO p)
    have hp : e p p ∈ ((e p).target ∩ O p) ∩ (e p).symm ⁻¹' V p := by
      refine ⟨⟨(e p).map_source (he p),hpO p⟩,?_⟩
      change (e p).symm (e p p) ∈ V p
      rw [(e p).left_inv (he p)]
      exact (hV p).1
    exact nhds_basis_closedBall.mem_iff.mp (ho.mem_nhds hp)
  choose r hr hrsub using hex
  refine ⟨r,fun p => ⟨hr p,fun x hx => (hrsub p hx).1⟩,?_⟩
  intro p q hpq
  apply Set.disjoint_left.mpr
  rintro x ⟨y,hy,rfl⟩ ⟨z,hz,heq⟩
  have hpV := (hrsub p hy).2
  have hqV := (hrsub q hz).2
  exact Set.disjoint_left.mp (hdisj p.property q.property
    (fun hpq' => hpq (Subtype.ext hpq'))) hpV (heq ▸ hqV)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
