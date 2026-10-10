import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPeriodicAnsatz
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasWeightedBounds

namespace OAI

/-! The same compactly supported local increment controls the derivatives
of its actual global restoration. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial LocalPeriodicExpansion WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem single_map_restore_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : JetPolynomial.Base → Space), ContDiff ℝ ∞ f →
      ∀ (s C : ℝ), 0 < s → s ≤ 1 → 0 ≤ C →
      WeightedEstimates.WeightedBound univ s m C f →
      A.WeightedBound s m (D*C) (restore (i : M) (A.outer i) f) := by
  classical
  obtain ⟨D,hD,hd⟩ := A.restoration_bound (V := Space) m
  refine ⟨D,hD,?_⟩
  intro f hf s C hs hs1 hC hb
  have hh := hd (fun j => if j = i then f else 0) s C hs hs1 hC
    (by intro j; split_ifs; exact hf; exact contDiff_const)
    (by
      intro j
      split_ifs
      · exact hb
      · exact (weightedBound_zero _ s m).mono_const hC)
  have he : (∑ j : A.centers, restore (j : M) (A.outer j) (if j = i then f else 0)) =
      restore (i : M) (A.outer i) f := by
    funext p
    rw [Finset.sum_apply,Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji,restore]
    · exact fun hi => False.elim (hi (Finset.mem_univ _))
  rw [he] at hh
  exact hh

theorem periodicAtlasAnsatz_increment_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
    ∀ (S : TopologicalSpace.Opens JetPolynomial.Base) (U : ℕ → Family S Space)
      (K : Set JetPolynomial.Base), IsClosed K → K ⊆ S →
      (∀ j p, p ∉ K → (U j).val p = 0) →
    ∀ (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C →
      WeightedEstimates.WeightedBound S s m C
        (finiteAnsatz (A.vectorChartRead i G) U ℓ L z-A.vectorChartRead i G) →
      A.WeightedBound s m (D*C) (A.periodicAtlasAnsatz i G U ℓ L z-G) := by
  obtain ⟨D,hD,hd⟩ := A.single_map_restore_bound i m
  refine ⟨D,hD,?_⟩
  intro G hG S U K hK hKS hzero ℓ L z s C hs hs1 hC hb
  let f := finiteAnsatz (A.vectorChartRead i G) U ℓ L z-A.vectorChartRead i G
  have hf : ContDiff ℝ ∞ f :=
    (finiteAnsatz_smooth_global (A.vectorChartRead_smooth i hG) U hK hKS
      (fun j p _ hp => hzero j p hp) ℓ L z).sub (A.vectorChartRead_smooth i hG)
  have hsupport : tsupport f ⊆ S :=
    (finiteAnsatz_tsupport_sub (A.vectorChartRead i G) U hK hzero ℓ L z).trans hKS
  have hglobal := hb.extend_support S.isOpen hsupport hC
  have hout := hd f hf s C hs hs1 hC hglobal
  have he : A.periodicAtlasAnsatz i G U ℓ L z-G = restore (i : M) (A.outer i) f := by
    funext p
    exact add_sub_cancel_left _ _
  rw [he]
  exact hout

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
