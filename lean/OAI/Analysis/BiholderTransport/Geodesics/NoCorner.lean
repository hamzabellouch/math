import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.SprayDistanceBound
import OAI.Analysis.BiholderTransport.Calculus.LocalCostGradient
import OAI.Analysis.BiholderTransport.Convexity.Fermat

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma cost_gradients_opposite {p y b : M}
    (htri : dist p b = dist p y + dist b y) (heq : dist p y = dist b y)
    (u v : TangentSpace 𝓘(ℝ,E) y)
    (hp : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun w => dist p w^2/2) y (innerSL ℝ u))
    (hb : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (fun w => dist b w^2/2) y (innerSL ℝ v)) :
    u + v = 0 := by
  have hmin : IsLocalMin (fun w => dist p w^2/2 + dist b w^2/2) y := by
    apply Filter.Eventually.of_forall
    intro w
    have h := dist_triangle p w b
    rw [htri,dist_comm w b] at h
    have h' : (dist p y+dist b y)^2 ≤ (dist p w+dist b w)^2 :=
      pow_le_pow_left₀ (add_nonneg dist_nonneg dist_nonneg) h 2
    nlinarith [sq_nonneg (dist p w-dist b w)]
  have hzero := isLocalMin_hasMFDerivAt_eq_zero hmin (hp.add hb)
  have hval := congrArg (fun L : TangentSpace 𝓘(ℝ,E) y →L[ℝ] ℝ => L (u+v)) hzero
  have hsq : ‖u+v‖^2 = 0 := by
    simpa only [_root_.add_apply,_root_.zero_apply,
      innerSL_apply_apply,←inner_add_left,real_inner_self_eq_norm_sq] using hval
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma sprayFlow_minimizing_prefix (z : TangentBundle 𝓘(ℝ,E) M) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t)
    (hmin : dist z.1 (sprayFlow t z).1 = t * ‖z.2‖) :
    dist z.1 (sprayFlow s z).1 = s * ‖z.2‖ := by
  have h0 := dist_sprayFlow_le z 0 s
  rw [sprayFlow_zero,zero_sub,abs_neg,abs_of_nonneg hs] at h0
  apply le_antisymm h0
  have h1 := dist_sprayFlow_le z s t
  rw [abs_of_nonpos (sub_nonpos.mpr hst)] at h1
  have h2 := dist_triangle z.1 (sprayFlow s z).1 (sprayFlow t z).1
  rw [hmin] at h2
  nlinarith

lemma sprayFlow_minimizer_gradient (z : TangentBundle 𝓘(ℝ,E) M) {t : ℝ} (ht : 0 < t)
    (hmin : dist z.1 (sprayFlow t z).1 = t * ‖z.2‖)
    (W : TangentSpace 𝓘(ℝ,E) (sprayFlow t z).1)
    (hW : ‖W‖ = dist z.1 (sprayFlow t z).1)
    (hD : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ)
      (fun x => dist z.1 x ^ 2 / 2) (sprayFlow t z).1 (innerSL ℝ W)) :
    W = t • (sprayFlow t z).2 := by
  have hcomp := hD.comp t (hasMFDerivAt_spray_projection ((sprayFlow_curve z).isMIntegralCurveAt t))
  have hd : HasDerivAt (fun s => dist z.1 (sprayFlow s z).1 ^ 2 / 2)
      (inner ℝ W (sprayFlow t z).2) t := by
    have hh : HasFDerivAt (fun s => dist z.1 (sprayFlow s z).1 ^ 2 / 2)
        ((innerSL ℝ W).comp ((1 : ℝ →L[ℝ] ℝ).smulRight (sprayFlow t z).2)) t := by
      convert! hcomp.hasFDerivAt
    convert! hh.hasDerivAt using 1
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self,one_smul,innerSL_apply_apply]
  have hp : HasDerivAt (fun s : ℝ => s^2 * (‖z.2‖^2 / 2)) (t * ‖z.2‖^2) t := by
    convert! ((hasDerivAt_id t).pow 2).mul_const (‖z.2‖^2/2) using 1
    simp only [id_eq]
    ring
  have heq : ∀ s ∈ Icc 0 t,
      dist z.1 (sprayFlow s z).1 ^ 2 / 2 = s^2 * (‖z.2‖^2 / 2) := by
    intro s hs
    rw [sprayFlow_minimizing_prefix z hs.1 hs.2 hmin,mul_pow]
    ring
  have hdin : HasDerivWithinAt (fun s => dist z.1 (sprayFlow s z).1 ^ 2 / 2)
      (t * ‖z.2‖^2) (Icc 0 t) t :=
    hp.hasDerivWithinAt.congr_of_mem heq ⟨ht.le,le_rfl⟩
  have hi : inner ℝ W (sprayFlow t z).2 = t*‖z.2‖^2 := by
    exact (hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc ht t ⟨ht.le,le_rfl⟩)).symm.trans
      (hdin.derivWithin (uniqueDiffOn_Icc ht t ⟨ht.le,le_rfl⟩))
  have hn := norm_sub_sq_real W (t • (sprayFlow t z).2)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht,sprayFlow_speed,real_inner_smul_right,hi,hW,hmin] at hn
  have hzero : ‖W - t • (sprayFlow t z).2‖ = 0 := by nlinarith [sq_nonneg ‖W - t • (sprayFlow t z).2‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

lemma exists_spray_local_extension (a : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : TangentBundle 𝓘(ℝ,E) M, z.1 = a → ‖z.2‖ = 1 →
      ∀ ε : ℝ, 0 < ε → ε < δ → ∀ b : M,
      dist (sprayFlow (-ε) z).1 z.1 = ε → dist z.1 b = ε →
      dist (sprayFlow (-ε) z).1 b = 2*ε → (sprayFlow ε z).1 = b := by
  obtain ⟨δ,hδ,H⟩ := exists_local_cost_gradient (E := E) a
  refine ⟨δ,hδ,?_⟩
  intro z hza hzn ε hε hεδ b hmin hzb hpb
  have hzball : z.1 ∈ Metric.ball a δ := by rw [hza]; exact Metric.mem_ball_self hδ
  have hpball : (sprayFlow (-ε) z).1 ∈ Metric.ball a δ := by
    rw [←hza,Metric.mem_ball,hmin]; exact hεδ
  have hbball : b ∈ Metric.ball a δ := by
    rw [←hza,Metric.mem_ball,dist_comm,hzb]; exact hεδ
  obtain ⟨q,hqy,hqn,_,hDq⟩ := H _ hpball _ hzball
  rcases q with ⟨y,u⟩
  change y=z.1 at hqy
  subst y
  obtain ⟨r,hry,hrn,hrback,hDr⟩ := H b hbball _ hzball
  rcases r with ⟨y,v⟩
  change y=z.1 at hry
  subst y
  have hflow : sprayFlow ε (sprayFlow (-ε) z) = z := by
    rw [←sprayFlow_add,add_neg_cancel,sprayFlow_zero]
  have hg := sprayFlow_minimizer_gradient (sprayFlow (-ε) z) hε
    (show dist (sprayFlow (-ε) z).1 (sprayFlow ε (sprayFlow (-ε) z)).1 =
      ε * ‖(sprayFlow (-ε) z).2‖ by rw [hflow,sprayFlow_speed,hzn,mul_one]; exact hmin)
  rw [hflow] at hg
  have hu : u = ε • z.2 := hg u hqn hDq
  have hop := cost_gradients_opposite
    (show dist (sprayFlow (-ε) z).1 b = dist (sprayFlow (-ε) z).1 z.1 + dist b z.1 by
      rw [hpb,hmin,dist_comm b z.1,hzb]; ring)
    (show dist (sprayFlow (-ε) z).1 z.1 = dist b z.1 by rw [hmin,dist_comm b z.1,hzb])
    u v hDq hDr
  have hv : v = (-ε) • z.2 := by
    rw [neg_smul,←hu]
    exact eq_neg_of_add_eq_zero_right hop
  have hr : (⟨z.1,v⟩ : TangentBundle 𝓘(ℝ,E) M) = tangentScale (-ε) z := by
    rw [hv]; cases z; rfl
  rw [hr,sprayFlow_scale,show (-ε)*(-1)=ε by ring] at hrback
  exact hrback

end WeakMTWTransport

end

end OAI
