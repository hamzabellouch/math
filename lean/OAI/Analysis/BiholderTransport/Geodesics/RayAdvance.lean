import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.CurveAdvance
import OAI.Analysis.BiholderTransport.Regularity.LipschitzSubAeDeriv

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology NNReal ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma lipschitz_spray_projection (z : TangentBundle 𝓘(ℝ,Model n) M) :
    LipschitzWith ‖z.2‖₊ (fun t => (sprayFlow t z).1) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  simpa only [Real.dist_eq,mul_comm,coe_nnnorm] using dist_sprayFlow_le z s t

lemma cTransform_ray_lipschitz [Nonempty M] {v : M → ℝ} (hv : Continuous v)
    (z : TangentBundle 𝓘(ℝ,Model n) M) :
    ∃ L, LipschitzWith L (fun t => cTransform v (sprayFlow t z).1) := by
  let C : ℝ≥0 := ⟨Metric.diam (univ:Set M),Metric.diam_nonneg⟩
  have hC : ∀ x y : M,dist x y ≤ C := fun x y =>
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
  exact ⟨C*‖z.2‖₊,(cTransform_lipschitz hv hC).comp (lipschitz_spray_projection z)⟩

lemma active_norm_deficit_deriv {v : M → ℝ} (hv : Continuous v)
    {z : TangentBundle 𝓘(ℝ,Model n) M} {t d D : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1/2) (hD : 0 ≤ D)
    (hd : HasDerivAt (fun s => cTransform v (sprayFlow s z).1) d t)
    (hgap : ∀ p∈activeLogs (n := n) v (sprayFlow t z).1,
      ‖p‖^2 ≤ (1-t)^2*‖z.2‖^2-D) :
    d-(1-t)*‖z.2‖^2 ≤ -D/2 := by
  obtain ⟨p,hp⟩ := nonempty_activeLogs (n := n) hv (sprayFlow t z).1
  have H := spray_deriv_le_active_norm hv hd hp
  have Hg := norm_deficit_advance (norm_nonneg p) (norm_nonneg z.2) ht ht1 hD (hgap p hp)
  linarith only [H,Hg]

lemma cost_norm_surplus_deriv {z : TangentBundle 𝓘(ℝ,Model n) M} {t d D : ℝ} {y : M}
    (ht : 0 ≤ t) (ht1 : t ≤ 1/2) (hD : 0 ≤ D)
    (hd : HasDerivAt (fun s => -cost (sprayFlow s z).1 y) d t)
    (hgap : dist (sprayFlow t z).1 y^2 ≤ (1-t)^2*‖z.2‖^2+D) :
    d-(1-t)*‖z.2‖^2 ≤ 2*D := by
  have H := spray_neg_cost_deriv_le hd
  have Hg := norm_surplus_advance dist_nonneg (norm_nonneg z.2) ht ht1 hD hgap
  linarith only [H,Hg]

end WeakMTWTransport

end

end OAI
