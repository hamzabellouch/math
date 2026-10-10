import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCompactArc

namespace OAI

/-! Transport a compact regular embedded model arc through actual smooth
surface coordinates, using only the target neighborhood containing the arc. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem smooth_arc_chart_transport (P : SmoothCompactArc 𝓘(ℝ,Base) Base)
    (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    (htarget : MapsTo P.curve (Icc P.start P.finish) c.target) :
    ∃ Q : SmoothCompactArc planeModel M,
      Q.start = P.start ∧ Q.finish = P.finish ∧ Q.curve = c.symm ∘ P.curve ∧
      ∀ t ∈ Q.domain, Q.curve t ∈ c.source ∧ c (Q.curve t) = P.curve t := by
  let U := P.domain ∩ P.curve ⁻¹' c.target
  have hU : IsOpen U := P.smooth.continuousOn.isOpen_inter_preimage P.domain_open c.open_target
  have hsub : Icc P.start P.finish ⊆ U := fun t ht => ⟨P.interval_subset ht,htarget ht⟩
  have hs : ContMDiffOn 𝓘(ℝ) planeModel ∞ (c.symm ∘ P.curve) U :=
    hci.comp (P.smooth.mono inter_subset_left) (fun _ ht => ht.2)
  have hdif : c.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨hci.mdifferentiableOn (by simp),hcs.mdifferentiableOn (by simp)⟩
  have hr : ∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) planeModel (c.symm ∘ P.curve) t) := by
    intro t ht
    rw [mfderiv_comp t ((hci.contMDiffAt (c.open_target.mem_nhds ht.2)).mdifferentiableAt (by simp))
      ((P.smooth.contMDiffAt (P.domain_open.mem_nhds ht.1)).mdifferentiableAt (by simp))]
    exact (hdif.mfderiv_injective ht.2).comp (P.regular t ht.1)
  have hi : (Icc P.start P.finish).InjOn (c.symm ∘ P.curve) := by
    intro t ht u hu he
    exact P.injective ht hu (c.symm.injOn (htarget ht) (htarget hu) he)
  let Q : SmoothCompactArc planeModel M :=
    ⟨c.symm ∘ P.curve,P.start,P.finish,P.start_lt_finish,U,hU,hsub,hs,hr,hi⟩
  refine ⟨Q,rfl,rfl,rfl,?_⟩
  intro t ht
  exact ⟨c.map_target ht.2,c.right_inv ht.2⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
