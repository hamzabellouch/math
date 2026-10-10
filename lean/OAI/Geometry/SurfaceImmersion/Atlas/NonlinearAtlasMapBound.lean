import OAI.Geometry.SurfaceImmersion.Atlas.NonlinearAtlasAnsatz

namespace OAI

/-! Fixed coordinate transport of the actual periodic map increment. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial LocalPeriodicExpansion WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem phaseAtlasAnsatz_increment_bound (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
    ∀ (S : TopologicalSpace.Opens JetPolynomial.Base) (U : ℕ → Family S Space)
      (K : Set JetPolynomial.Base), IsClosed K → K ⊆ S →
      (∀ j x, x ∉ K → (U j).val x = 0) →
    ∀ (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C →
      WeightedEstimates.WeightedBound S s m C
        (finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z-A.vectorChartRead i F ∘ e.symm) →
      A.WeightedBound s m (D*C) (A.phaseAtlasAnsatz i F e χ U ℓ L z-F) := by
  obtain ⟨Dt,hDt,ht⟩ := supportedChartPullback_bound (V := Space) e he hχ hc m
  obtain ⟨Dr,hDr,hr⟩ := A.single_map_restore_bound i m
  refine ⟨Dr*Dt,mul_nonneg hDr hDt,?_⟩
  intro F hF S U K hK hKS hzero ℓ L z s C hs hs1 hC hb
  let f := finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z-A.vectorChartRead i F ∘ e.symm
  have hbase := (A.vectorChartRead_smooth i hF).comp hi
  have hf : ContDiff ℝ ∞ f :=
    (finiteAnsatz_smooth_global hbase U hK hKS (fun j x _ hx => hzero j x hx) ℓ L z).sub hbase
  have hsp : tsupport f ⊆ S := (finiteAnsatz_tsupport_sub _ U hK hzero ℓ L z).trans hKS
  have hglobal := hb.extend_support S.isOpen hsp hC
  have hpull := ht f s C hs hs1 hC hf hglobal
  have hrest := hr (supportedChartPullback e χ f) (supportedChartPullback_smooth e he hχ hf)
    s (Dt*C) hs hs1 (mul_nonneg hDt hC) hpull
  have heq : A.phaseAtlasAnsatz i F e χ U ℓ L z-F =
      restore (i : M) (A.outer i) (supportedChartPullback e χ f) := by
    funext p
    exact add_sub_cancel_left _ _
  rw [heq]
  simpa only [mul_assoc] using hrest

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
