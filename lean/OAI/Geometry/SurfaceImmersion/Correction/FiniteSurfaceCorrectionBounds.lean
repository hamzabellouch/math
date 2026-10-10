import OAI.Geometry.SurfaceImmersion.Correction.FiniteSurfaceCorrection
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasSphericalTensorBound
import OAI.Geometry.SurfaceImmersion.Geometry.SingleEuclideanRestoreBound
import OAI.Geometry.SurfaceImmersion.Atlas.DisjointAtlasBounds
import OAI.Geometry.SurfaceImmersion.Geometry.ScaledQuadraticBudgets

namespace OAI

/-! The total finite-point correction is arbitrarily small in C1 and
uniformly bounded in C2, independently of the finite set. -/
noncomputable section
open Set Metric Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem finite_surface_correction_budgets {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hunit : ∀ p, ‖F p‖ = 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (P : Finset M) (c : P → A.centers) (r : P → ℝ) (η : ℝ),
      0 < η → η ≤ 1 → (∀ p, A.weight (c p) p ≠ 0) →
      (∀ p, 0 < r p ∧ r p ≤ η) →
      (∀ p, closedBall (chartAt Plane (c p : M) p) (r p) ⊆ (chartAt Plane (c p : M)).target) →
      (Pairwise fun p q : P => Disjoint
        ((chartAt Plane (c p : M)).symm '' closedBall (chartAt Plane (c p : M) p) (r p))
        ((chartAt Plane (c q : M)).symm '' closedBall (chartAt Plane (c q : M) q) (r q))) →
      A.WeightedBound 1 1 (D*η) (A.finiteSurfaceQuadratic P c r F) ∧
      A.WeightedBound 1 2 D (A.finiteSurfaceQuadratic P c r F) := by
  classical
  obtain ⟨K,hK,hKB⟩ := A.uniform_spherical_correction_tensor hF hunit
  obtain ⟨C,hC,hCB⟩ := scaled_quadratic_C1_C2_budgets K hK
  obtain ⟨D₁,hD₁,h₁⟩ := A.single_euclidean_restore_bound 1
  obtain ⟨D₂,hD₂,h₂⟩ := A.single_euclidean_restore_bound 2
  refine ⟨(D₁+D₂)*C,by positivity,?_⟩
  intro P c r η hη hη1 hc hr ht hd
  let q (p : P) := scaledQuadraticCutoff
    (sphericalSecondFormCLM (A.euclideanChartRead (c p) F) (chartAt Plane (c p : M) p))
    (chartAt Plane (c p : M) p) (r p)
  let Q (p : P) := euclideanRestore (c p : M) (A.outer (c p)) (q p)
  have hQs (p : P) : ContMDiff planeModel spaceModel ∞ (Q p) :=
    euclideanRestore_smooth _ (A.outer_smooth _) (by simpa only [chart_source]
      using (A.outer_support (c p))) (scaledQuadraticCutoff_smooth _ _ _)
  have hQd : (↑(Finset.univ : Finset P) : Set P).Pairwise
      fun p q => Disjoint (tsupport (Q p)) (tsupport (Q q)) := by
    intro p _ q _ hpq
    exact (hd hpq).mono
      (euclideanRestore_tsupport _ _ (isCompact_closedBall _ _) (ht p)
        (scaledQuadraticCutoff_tsupport _ _ (hr p).1))
      (euclideanRestore_tsupport _ _ (isCompact_closedBall _ _) (ht q)
        (scaledQuadraticCutoff_tsupport _ _ (hr q).1))
  have hbud (p : P) := hCB _ (hKB (c p) p (hc p)) (chartAt Plane (c p : M) p) (r p) (hr p).1 ((hr p).2.trans hη1)
  have hsum : A.finiteSurfaceQuadratic P c r F = ∑ p : P, Q p := by
    funext x
    simp only [Finset.sum_apply]
    rfl
  rw [hsum]
  constructor
  · apply A.disjoint_weighted_sum_bound Finset.univ Q (fun p _ => hQs p) hQd
      (mul_nonneg (mul_nonneg (add_nonneg hD₁ hD₂) hC) hη.le)
    intro p _ i
    apply (h₁ (c p) (q p) (C*r p) (mul_nonneg hC (hr p).1.le)
      (scaledQuadraticCutoff_smooth _ _ _) (hbud p).1 i).mono_const
    calc
      D₁*(C*r p) ≤ D₁*(C*η) := by gcongr; exact (hr p).2
      _ ≤ ((D₁+D₂)*C)*η := by nlinarith [mul_nonneg hD₂ (mul_nonneg hC hη.le)]
  · apply A.disjoint_weighted_sum_bound Finset.univ Q (fun p _ => hQs p) hQd
      (mul_nonneg (add_nonneg hD₁ hD₂) hC)
    intro p _ i
    apply (h₂ (c p) (q p) C hC (scaledQuadraticCutoff_smooth _ _ _) (hbud p).2 i).mono_const
    nlinarith [mul_nonneg hD₂ hC]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
