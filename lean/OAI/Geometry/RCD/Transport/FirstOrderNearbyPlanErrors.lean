import OAI.Geometry.RCD.Harmonic.FirstOrderUniformAffineMean
import OAI.Geometry.RCD.Coordinates.NearbyNormalizedPlan
import OAI.Geometry.RCD.Coordinates.DiagonalMeanSelection
import OAI.Geometry.RCD.Transport.CompressedSegmentIntegral

namespace OAI

/-! # Shrinking endpoint plans with simultaneous affine and spatial errors -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

def affineSpatialPathCost {n : ℕ} (F : Fin n → C(Time,X) → C(Time,ℝ))
    (E : X → ℝ) (γ : C(Time,X)) : ℝ :=
  (∑ i, ‖F i γ‖)+(∫ t in Icc (0:ℝ) 1, E (geodesicExtension γ t))

theorem NoncollapsedRCD.first_order_nearby_plan_errors {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (hK : K ≤ 0)
    (p x y : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1 ≤ K*(16*r k)^2)
    (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k))
    (hx : ∀ k, dist (x k) (p k) ≤ r k/48) (hy : ∀ k, dist (y k) (p k) ≤ r k/48)
    (E : ℕ → X → ℝ) (hE : ∀ k z, 0 ≤ E k z)
    (hEI : ∀ k, IntegrableOn (E k) (ball (p k) (4*r k)) (hausdorff n X))
    (hE0 : Tendsto (fun k => ((hausdorff n X).real (ball (p k) (4*r k)))⁻¹*
      ∫ z in ball (p k) (4*r k), E k z ∂hausdorff n X) atTop (𝓝 0)) :
    ∃ (δ : ℕ → ℝ) (π : ℕ → Measure C(Time,X))
      (F : ℕ → Fin n → C(Time,X) → C(Time,ℝ)),
      (∀ k, 0 < δ k ∧ δ k ≤ 1/2) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ k, IsProbabilityMeasure (π k)) ∧
      (∀ k, ∀ᵐ γ ∂π k, IsGeodesic γ) ∧
      (∀ k, IsOptimalCoupling ((π k).map (fun γ => γ 0))
        ((π k).map (fun γ => γ 1)) ((π k).map (fun γ => (γ 0,γ 1)))) ∧
      (∀ k, ∃ C : ℝ≥0∞, C≠∞ ∧ ∀ t : Time, (π k).map (fun γ => γ t) ≤ C • hausdorff n X) ∧
      (∀ k, ∀ᵐ γ ∂π k, dist (γ 0) (x k) < δ k*r k/24 ∧
        dist (γ 1) (y k) < δ k*r k/24 ∧ ∀ t : Time, dist (γ t) (p k) ≤ r k/8) ∧
      (∀ k, ∀ᵐ γ ∂π k, ∀ i (t : Time), F k i γ t=
        (v k (γ t) i-((1-(t:ℝ))*v k (γ 0) i+(t:ℝ)*v k (γ 1) i))/r k) ∧
      (∀ k, ∀ᵐ γ ∂π k, IntegrableOn (fun t => E k (geodesicExtension γ t)) (Icc (0:ℝ) 1)) ∧
      (∀ k, Integrable (affineSpatialPathCost (F k) (E k)) (π k)) ∧
      Tendsto (fun k => ∫ γ, affineSpatialPathCost (F k) (E k) γ ∂π k) atTop (𝓝 0) := by
  classical
  let μ := hausdorff n X
  let := hX.separable
  obtain ⟨D,hD,hplans⟩ := hX.nearby_normalized_plan hn hK
  let δ (m : ℕ) : ℝ := ((m:ℝ)+2)⁻¹
  have hδ (m : ℕ) : 0 < δ m ∧ δ m ≤ 1/2 := by
    constructor
    · dsimp only [δ]; positivity
    · rw [one_div]
      change ((m:ℝ)+2)⁻¹ ≤ (2:ℝ)⁻¹
      exact inv_anti₀ (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) m])
  choose π hπ hgeo hopt hcomp hends using fun m k =>
    hplans (hr k) (hcurv k) (hδ m).1 (hδ m).2 (hx k) (hy k)
  let (m k : ℕ) : IsProbabilityMeasure (π m k) := hπ m k
  let B (m : ℕ) := D/(δ m)^n
  have hB (m : ℕ) : 0 ≤ B m := div_nonneg hD.le (pow_pos (hδ m).1 n).le
  have hstart (m k : ℕ) : ∀ᵐ z ∂(π m k).map (fun γ => γ 0), dist z (p k) ≤ r k/12 := by
    apply (ae_map_iff (measurable_path_eval 0).aemeasurable isClosed_closedBall.measurableSet).mpr
    filter_upwards [hends m k] with γ he
    have hh := dist_triangle (γ 0) (x k) (p k)
    nlinarith [(hx k),(hδ m).2,hr k]
  have hfinish (m k : ℕ) : ∀ᵐ z ∂(π m k).map (fun γ => γ 1), dist z (p k) ≤ r k/12 := by
    apply (ae_map_iff (measurable_path_eval 1).aemeasurable isClosed_closedBall.measurableSet).mpr
    filter_upwards [hends m k] with γ he
    have hh := dist_triangle (γ 1) (y k) (p k)
    nlinarith [(hy k),(hδ m).2,hr k]
  choose F hFc hFeq hFI hF0 using fun m i =>
    hX.first_order_uniform_affine_mean hn hK p r ε hr hr0 hcurv hε hε1 hε0
      u v hsplit (π m) (hgeo m) (hopt m) (hB m) (hcomp m) (hstart m) (hfinish m) i
  have hstay (m k : ℕ) (t : Time) : ∀ᵐ z ∂(π m k).map (fun γ => γ t), z∈ball (p k) (4*r k) := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_ball).mpr
    filter_upwards [hends m k] with γ he
    exact (he.2.2 t).trans_lt (by linarith [hr k])
  have hEI' (m k : ℕ) := compressed_segment_integral μ (π m k) ENNReal.ofReal_ne_top
    (hcomp m k) (hstay m k) (hEI k) (Eventually.of_forall (fun z => hE k z))
  let cost (m k : ℕ) := affineSpatialPathCost (fun i => F m i k) (E k)
  have hI (m k : ℕ) : Integrable (cost m k) (π m k) :=
    (integrable_finsetSum _ (fun i _ => hFI m i k)).add (hEI' m k).1
  have hpos (m k : ℕ) (γ : C(Time,X)) : 0 ≤ cost m k γ :=
    add_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (integral_nonneg (fun _ => hE k _))
  have hEplan (m : ℕ) : Tendsto (fun k => ∫ γ,
      (∫ t in Icc (0:ℝ) 1, E k (geodesicExtension γ t)) ∂π m k) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => integral_nonneg (fun γ => integral_nonneg (fun _ => hE k _)))
      (g := fun k => B m*((μ.real (ball (p k) (4*r k)))⁻¹*∫ z in ball (p k) (4*r k), E k z ∂μ))
    · intro k
      have hm : 0 < μ.real (ball (p k) (4*r k)) := ENNReal.toReal_pos
        (hX.fullSupport _ _ (mul_pos (by norm_num) (hr k))).ne' (hX.finiteOnBounded _ isBounded_ball).ne
      have hb := (hEI' m k).2.2
      rw [ENNReal.toReal_ofReal (div_nonneg (hB m) hm.le)] at hb
      convert hb using 1
      ring
    · simpa only [mul_zero] using hE0.const_mul (B m)
  have hcost0 (m : ℕ) : Tendsto (fun k => ∫ γ, cost m k γ ∂π m k) atTop (𝓝 0) := by
    have hs := tendsto_finsetSum Finset.univ (fun i _ => hF0 m i)
    have hh := hs.add (hEplan m)
    simpa only [cost,affineSpatialPathCost,integral_add (integrable_finsetSum _ (fun i _ => hFI m i _))
      (hEI' m _).1,integral_finsetSum _ (fun i _ => hFI m i _),Finset.sum_const_zero,zero_add] using hh
  obtain ⟨d,hd,hcost⟩ := exists_vanishing_diagonal_cost (fun m k => ∫ γ, cost m k γ ∂π m k)
    (fun m k => integral_nonneg (hpos m k)) hcost0
  have hδ0 : Tendsto (fun k => δ (d k)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hd))
  refine ⟨fun k => δ (d k),fun k => π (d k) k,fun k i => F (d k) i k,
    fun k => hδ (d k),hδ0,fun k => hπ (d k) k,fun k => hgeo (d k) k,
    fun k => hopt (d k) k,?_,fun k => hends (d k) k,?_,fun k => (hEI' (d k) k).2.1,
    fun k => hI (d k) k,hcost⟩
  · intro k
    exact ⟨_,ENNReal.ofReal_ne_top,hcomp (d k) k⟩
  · intro k
    exact ae_all_iff.mpr (fun i => hFeq (d k) i k)

end RegularPointCoordinates

end

end OAI
