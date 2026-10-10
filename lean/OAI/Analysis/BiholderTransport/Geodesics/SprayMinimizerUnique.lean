import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.MinimizingSubinterval

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
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma sprayFlow_minimizer_terminal_eq (z G : TangentBundle 𝓘(ℝ,E) M)
    (hG : G.1 = (sprayFlow 1 z).1)
    (hmin : dist z.1 (sprayFlow 1 z).1 = ‖z.2‖)
    (hGn : ‖G.2‖ = dist z.1 G.1)
    (hD : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ)
      (fun x => dist z.1 x^2/2) G.1 (innerSL ℝ G.2)) : sprayFlow 1 z = G := by
  rcases G with ⟨b,W⟩
  change b = (sprayFlow 1 z).1 at hG
  subst b
  have hmin' : dist z.1 (sprayFlow 1 z).1 = 1 * ‖z.2‖ := by rw [one_mul]; exact hmin
  have hh := sprayFlow_minimizer_gradient z zero_lt_one hmin' W hGn hD
  rw [one_smul] at hh
  rw [hh]

lemma sprayFlow_minimizer_unique_of_gradient (z w G : TangentBundle 𝓘(ℝ,E) M)
    (hbase : z.1=w.1)
    (hGz : G.1=(sprayFlow 1 z).1) (hGw : G.1=(sprayFlow 1 w).1)
    (hz : dist z.1 (sprayFlow 1 z).1 = ‖z.2‖)
    (hw : dist w.1 (sprayFlow 1 w).1 = ‖w.2‖)
    (hGn : ‖G.2‖ = dist z.1 G.1)
    (hD : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ)
      (fun x => dist z.1 x^2/2) G.1 (innerSL ℝ G.2)) : z=w := by
  have hez := sprayFlow_minimizer_terminal_eq z G hGz hz hGn hD
  have hDw : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ)
      (fun x => dist w.1 x^2/2) G.1 (innerSL ℝ G.2) := by rwa [←hbase]
  have hnw : ‖G.2‖ = dist w.1 G.1 := by rw [←hbase]; exact hGn
  have hew := sprayFlow_minimizer_terminal_eq w G hGw hw hnw hDw
  have hh := congrArg (sprayFlow (-1)) (hez.trans hew.symm)
  simpa only [←sprayFlow_add,neg_add_cancel,sprayFlow_zero] using hh

lemma exists_local_spray_minimizer_unique (a : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z w : TangentBundle 𝓘(ℝ,E) M,
      z.1 ∈ Metric.ball a δ → (sprayFlow 1 z).1 ∈ Metric.ball a δ →
      z.1=w.1 → (sprayFlow 1 z).1=(sprayFlow 1 w).1 →
      dist z.1 (sprayFlow 1 z).1 = ‖z.2‖ →
      dist w.1 (sprayFlow 1 w).1 = ‖w.2‖ → z=w := by
  obtain ⟨δ,hδ,H⟩ := exists_local_cost_gradient (E := E) a
  refine ⟨δ,hδ,?_⟩
  intro z w hz hf hbase hend hminz hminw
  obtain ⟨G,hG,hGn,_,hD⟩ := H _ hz _ hf
  apply sprayFlow_minimizer_unique_of_gradient z w G hbase hG (hG.trans hend) hminz hminw
  · exact hGn.trans (congrArg (dist z.1) hG.symm)
  · exact hD

omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [CompactSpace M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma tangentScale_injective {c : ℝ} (hc : c ≠ 0) :
    Function.Injective (tangentScale (M := M) (E := E) c) := by
  have hinv : Function.LeftInverse (tangentScale (M := M) (E := E) c⁻¹)
      (tangentScale c) := by
    rintro ⟨base,velocity⟩
    dsimp only [tangentScale]
    congr 1
    exact inv_smul_smul₀ hc velocity
  exact hinv.injective

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma sprayFlow_unit_minimizer_unique (z w : TangentBundle 𝓘(ℝ,E) M)
    (hbase : z.1=w.1) (hzn : ‖z.2‖=1) (hwn : ‖w.2‖=1)
    {t T : ℝ} (ht : 0<t) (htT : t<T)
    (hminz : dist z.1 (sprayFlow T z).1 = T)
    (hminw : dist w.1 (sprayFlow t w).1 = t)
    (hend : (sprayFlow t z).1=(sprayFlow t w).1) : z=w := by
  have hzmin : dist z.1 (sprayFlow T z).1 = T*‖z.2‖ := by rw [hzn,mul_one]; exact hminz
  have hwmin : dist w.1 (sprayFlow t w).1 = t*‖w.2‖ := by rw [hwn,mul_one]; exact hminw
  let a := (sprayFlow t z).1
  obtain ⟨δ,hδ,Hext⟩ := exists_spray_local_extension (E := E) a
  obtain ⟨η,hη,Huniq⟩ := exists_local_spray_minimizer_unique (E := E) a
  let ε : ℝ := min (δ/2) (min (η/2) (min (t/2) ((T-t)/2)))
  have hε : 0<ε := lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by linarith)))
  have hεδ : ε<δ := (min_le_left _ _).trans_lt (by linarith)
  have hεη : ε<η := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hεt : ε<t := (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)).trans_lt (by linarith)
  have hεT : t+ε<T := by
    have hh := (((min_le_right (δ/2) (min (η/2) (min (t/2) ((T-t)/2)))).trans (min_le_right _ _)).trans (min_le_right _ _))
    change ε ≤ (T-t)/2 at hh
    linarith
  let q := sprayFlow t z
  let r := sprayFlow t w
  let b := (sprayFlow (t+ε) z).1
  have hrbase : r.1=a := hend.symm
  have hrn : ‖r.2‖=1 := by rw [sprayFlow_speed]; exact hwn
  have hqnext : dist q.1 b = ε := by
    have hpref := sprayFlow_minimizing_prefix z (show 0≤t+ε by linarith) hεT.le hzmin
    have hh := sprayFlow_minimizing_subinterval z ht.le (show t≤t+ε by linarith) hpref
    rw [hzn,mul_one] at hh
    convert hh using 1
    ring
  have hrback : sprayFlow (-ε) r = sprayFlow (t-ε) w := by
    rw [←sprayFlow_add]; congr 1; ring
  have hback : dist (sprayFlow (-ε) r).1 r.1 = ε := by
    rw [hrback]
    have hh := sprayFlow_minimizing_subinterval w (s := t-ε) (by linarith) (by linarith) hwmin
    rw [hwn,mul_one] at hh
    convert hh using 1
    ring
  have hrnext : dist r.1 b = ε := by rw [hrbase]; exact hqnext
  have hlong : dist (sprayFlow (-ε) r).1 b = 2*ε := by
    apply le_antisymm
    · exact (dist_triangle _ r.1 _).trans (by rw [hback,hrnext]; linarith)
    · have hh := dist_triangle w.1 (sprayFlow (-ε) r).1 b
      have hpre := sprayFlow_minimizing_prefix w (s := t-ε) (by linarith) (by linarith) hwmin
      rw [hwn,mul_one] at hpre
      have hpost := sprayFlow_minimizing_prefix z (s := t+ε) (by linarith) hεT.le hzmin
      rw [hzn,mul_one] at hpost
      rw [hrback,hpre,←hbase] at hh
      change dist z.1 (sprayFlow (t+ε) z).1 ≤ _ at hh
      rw [hpost] at hh
      rw [hrback]
      linarith
  have hrext := Hext r hrbase hrn ε hε hεδ b hback hrnext hlong
  have hqext : (sprayFlow ε q).1 = b := by
    rw [←sprayFlow_add,add_comm]
  have hscale (u : TangentBundle 𝓘(ℝ,E) M) :
      (sprayFlow 1 (tangentScale ε u)).1 = (sprayFlow ε u).1 := by
    rw [sprayFlow_scale,mul_one]; rfl
  have hscalen (u : TangentBundle 𝓘(ℝ,E) M) : ‖(tangentScale ε u).2‖ = ε*‖u.2‖ := by
    change ‖ε • u.2‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hε]
  have hscaled := Huniq (tangentScale ε q) (tangentScale ε r)
    (Metric.mem_ball_self hη)
    (by rw [hscale,hqext,Metric.mem_ball,dist_comm]; exact hqnext.trans_lt hεη)
    hend (by rw [hscale,hscale,hqext,hrext])
    (by rw [hscale,hqext,hscalen,sprayFlow_speed,hzn,mul_one]; exact hqnext)
    (by rw [hscale,hrext,hscalen,hrn,mul_one]; exact hrnext)
  have hqr := tangentScale_injective hε.ne' hscaled
  have hh := congrArg (sprayFlow (-t)) hqr
  simpa only [q,r,←sprayFlow_add,neg_add_cancel,sprayFlow_zero] using hh

end WeakMTWTransport

end

end OAI
