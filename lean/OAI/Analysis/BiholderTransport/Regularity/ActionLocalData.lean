import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.UniformShort
import OAI.Analysis.BiholderTransport.Geodesics.ShortGradient

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

open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma exists_two_short_legs (x : M) (p : TangentSpace 𝓘(ℝ,E) x)
    {t T δ : ℝ} (ht : 0<t) (hT : t<T) (hδ : 0<δ) :
    ∃ ε : ℝ, 0<ε ∧ ε<t ∧ t+ε<T ∧
      (sprayFlow (t+ε) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 ∈
        Metric.ball (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 δ ∧
      ∀ᶠ v : TangentSpace 𝓘(ℝ,E) x in 𝓝 p,
        (sprayFlow (t-ε) (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1 ∈
          Metric.ball (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 δ ∧
        (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1 ∈
          Metric.ball (sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 δ ∧
        HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ)
          (fun b => dist b (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1^2/2)
          (sprayFlow (t-ε) (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1
          (innerSL ℝ ((-ε) • (sprayFlow (t-ε) (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).2)) ∧
        HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ)
          (fun q => dist (sprayFlow (t-ε) (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1 q^2/2)
          (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).1
          (innerSL ℝ (ε • (sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M)).2)) := by
  let a := sprayFlow t (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)
  obtain ⟨δs,hδs,Hs⟩ := exists_local_spray_cost_start_gradient (E := E) a.1
  obtain ⟨δe,hδe,He⟩ := exists_local_spray_cost_gradient (E := E) a.1
  let r := min δ (min δs δe)
  have hr : 0<r := lt_min hδ (lt_min hδs hδe)
  have hι : Continuous (fun u : ℝ × TangentSpace 𝓘(ℝ,E) x =>
      (⟨x,u.2⟩ : TangentBundle 𝓘(ℝ,E) M)) :=
    (contMDiff_fiber_embedding x).continuous.comp continuous_snd
  let F : ℝ × TangentSpace 𝓘(ℝ,E) x → TangentBundle 𝓘(ℝ,E) M :=
    fun u => sprayFlow (t-u.1) ⟨x,u.2⟩
  have hF : Continuous F := contMDiff_sprayFlow.continuous.comp
    ((continuous_const.sub continuous_fst).prodMk hι)
  have hF₀ : F (0,p)=a := by simp [F,a]
  have hpr : Continuous (fun z : TangentBundle 𝓘(ℝ,E) M => z.1) :=
    FiberBundle.continuous_proj E (fun b : M => TangentSpace 𝓘(ℝ,E) b)
  have hFin := (hpr.comp hF).continuousAt.preimage_mem_nhds
    (show Metric.ball a.1 r ∈ 𝓝 (F (0,p)).1 by rw [hF₀]; exact Metric.ball_mem_nhds _ hr)
  have hQ : Continuous (fun u : ℝ × TangentSpace 𝓘(ℝ,E) x =>
      (sprayFlow t (⟨x,u.2⟩ : TangentBundle 𝓘(ℝ,E) M)).1) :=
    hpr.comp ((contMDiff_spray_fiber x t).continuous.comp continuous_snd)
  have hQin := (hQ.continuousAt (x := (0,p))).preimage_mem_nhds (Metric.ball_mem_nhds a.1 hr)
  have hY : Continuous (fun u : ℝ × TangentSpace 𝓘(ℝ,E) x =>
      (sprayFlow (t+u.1) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1) :=
    hpr.comp (contMDiff_sprayFlow.continuous.comp
      ((continuous_const.add continuous_fst).prodMk continuous_const))
  have hYin := (hY.continuousAt (x := (0,p))).preimage_mem_nhds
    (show Metric.ball a.1 r ∈ 𝓝 (sprayFlow (t+(0:ℝ)) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 by
      simpa only [add_zero] using Metric.ball_mem_nhds a.1 hr)
  have htend : Tendsto (fun u : ℝ × TangentSpace 𝓘(ℝ,E) x => (u.1,F u)) (𝓝 (0,p)) (𝓝 (0,a)) := by
    simpa only [ContinuousAt,hF₀] using (continuous_fst.prodMk hF).continuousAt (x := (0,p))
  have hmin := htend.eventually (sprayFlow_uniformly_short_minimizing a)
  have hAll : ∀ᶠ u : ℝ × TangentSpace 𝓘(ℝ,E) x in 𝓝 (0,p),
      (F u).1 ∈ Metric.ball a.1 r ∧
      (sprayFlow t (⟨x,u.2⟩ : TangentBundle 𝓘(ℝ,E) M)).1 ∈ Metric.ball a.1 r ∧
      (sprayFlow (t+u.1) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,E) M)).1 ∈ Metric.ball a.1 r ∧
      dist (F u).1 (sprayFlow u.1 (F u)).1 = |u.1| *‖(F u).2‖ := by
    filter_upwards [hFin,hQin,hYin,hmin] with u h₁ h₂ h₃ h₄
    exact ⟨h₁,h₂,h₃,h₄⟩
  obtain ⟨A,hA,B,hB,hAB⟩ := mem_nhds_prod_iff.mp hAll
  obtain ⟨η,hη,hηA⟩ := Metric.mem_nhds_iff.mp hA
  let ε := min η (min t (T-t))/2
  have hε : 0<ε := div_pos (lt_min hη (lt_min ht (sub_pos.mpr hT))) (by norm_num)
  have hεη : ε<η := lt_of_lt_of_le (half_lt_self (lt_min hη (lt_min ht (sub_pos.mpr hT)))) (min_le_left _ _)
  have hεt : ε<t := lt_of_lt_of_le (half_lt_self (lt_min hη (lt_min ht (sub_pos.mpr hT))))
    ((min_le_right _ _).trans (min_le_left _ _))
  have hεT : ε<T-t := lt_of_lt_of_le (half_lt_self (lt_min hη (lt_min ht (sub_pos.mpr hT))))
    ((min_le_right _ _).trans (min_le_right _ _))
  have hεA : ε∈A := hηA (by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hε] using hεη)
  have hP := hAB (show (ε,p) ∈ A ×ˢ B from ⟨hεA,mem_of_mem_nhds hB⟩)
  have hsubδ : Metric.ball a.1 r ⊆ Metric.ball a.1 δ := Metric.ball_subset_ball (min_le_left _ _)
  have hsubs : Metric.ball a.1 r ⊆ Metric.ball a.1 δs :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hsube : Metric.ball a.1 r ⊆ Metric.ball a.1 δe :=
    Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε,hε,hεt,by linarith,hsubδ hP.2.2.1,?_⟩
  filter_upwards [hB] with v hv
  have H := hAB (show (ε,v) ∈ A ×ˢ B from ⟨hεA,hv⟩)
  have hflow : sprayFlow ε (F (ε,v)) = sprayFlow t (⟨x,v⟩ : TangentBundle 𝓘(ℝ,E) M) := by
    dsimp [F]
    have htime : ε + (t - ε) = t := by ring
    rw [← sprayFlow_add, htime]
  have hm : dist (F (ε,v)).1 (sprayFlow ε (F (ε,v))).1 = ε*‖(F (ε,v)).2‖ := by
    simpa only [abs_of_pos hε] using H.2.2.2
  have hs := Hs (F (ε,v)) ε hε (hsubs H.1) (by rw [hflow]; exact hsubs H.2.1) hm
  have he := He (F (ε,v)) ε hε (hsube H.1) (by rw [hflow]; exact hsube H.2.1) hm
  rw [hflow] at hs he
  exact ⟨hsubδ H.1,hsubδ H.2.1,hs,he⟩

end WeakMTWTransport

end

end OAI
