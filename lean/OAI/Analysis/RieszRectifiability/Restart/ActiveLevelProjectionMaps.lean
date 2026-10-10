import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveLevelWeightStability
import OAI.Analysis.RieszRectifiability.Projections.NonemptyAffineProjection
import OAI.Analysis.RieszRectifiability.Projections.FiniteProjectionAveraging
import OAI.Analysis.RieszRectifiability.Flatness.BilateralBetaWitnesses

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i))

def activeLevelProjectionMap : Ambient d → Ambient d :=
  finiteProjectionAverage (activeLevelIndex μ R hR k z Good t)
    (activeLevelWeight μ R hR k z Good t)
    (fun i => nonemptyAffineProjection (S i) (hS i).1)

theorem activeLevelProjectionMap_continuous :
    Continuous (activeLevelProjectionMap μ R hR k z Good t S hS) :=
  finiteProjectionAverage_continuous _ _ _
    (fun i hi => (activeLevelWeight_lipschitz μ R hR k z Good t i hi).continuous)
    (fun i _ => (nonemptyAffineProjection_lipschitz (S i) (hS i).1).continuous)

theorem activeLevelProjectionMap_eq_self_of_large_scale (x : Ambient d)
    (hx : 5 * latticeRadius R (k + t) ≤ cellRegionStoppingScale μ R hR k z Good x) :
    activeLevelProjectionMap μ R hR k z Good t S hS x = x := by
  apply finiteProjectionAverage_eq_self
  intro i hi
  by_contra hn
  have hiA := (mem_activeLevelIndex μ R hR k z Good t i).mp hi
  have hnear := (activeLevelWeight_ne_zero_iff μ R hR k z Good t i x).mp hn
  have hscale := cellRegionStoppingScale_le_center_radius μ R hR k z Good x i hiA.2
  have hrad : i.radius = latticeRadius R (k + t) := by
    simp only [SupportCellDescendant.radius, hiA.1]
  rw [hrad] at hscale
  linarith

theorem activeLevelProjectionMap_eq_weighted_sum (x : Ambient d)
    (hx : cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + t)) :
    activeLevelProjectionMap μ R hR k z Good t S hS x =
      ∑ i ∈ activeLevelIndex μ R hR k z Good t,
        activeLevelWeight μ R hR k z Good t i x • nonemptyAffineProjection (S i) (hS i).1 x :=
  finiteProjectionAverage_eq_weighted_sum _ _ _ x
    (activeLevelWeight_sum_eq_one μ R hR k z Good t x hx)

theorem activeLevelProjectionMap_support_displacement (ε : ℝ) (hε : 0 ≤ ε)
    (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (x : Ambient d) (hx : x ∈ μ.support) :
    dist (activeLevelProjectionMap μ R hR k z Good t S hS x) x ≤
      (1024 * ε) * latticeRadius R (k + t) := by
  apply finiteProjectionAverage_dist_self_le _ _ _ x _
    (mul_nonneg (mul_nonneg (by norm_num) hε) (latticeRadius_pos R hR (k + t)).le)
    (fun i _ => activeLevelWeight_nonneg μ R hR k z Good t i x)
    (activeLevelWeight_sum_le_one μ R hR k z Good t x)
  intro i hi hn
  have hiA := (mem_activeLevelIndex μ R hR k z Good t i).mp hi
  have hrad : i.radius = latticeRadius R (k + t) := by
    simp only [SupportCellDescendant.radius, hiA.1]
  have hnear := (activeLevelWeight_ne_zero_iff μ R hR k z Good t i x).mp hn
  have hr := i.radius_pos
  have hball : x ∈ ball i.center (1024 * i.radius) := by
    change dist x i.center < 1024 * i.radius
    rw [← hrad] at hnear
    linarith
  have hdist := (bilateralPlaneError_lt_pointwise μ ⟨x, hx⟩ i.center
    (1024 * i.radius) ε (by positivity) (S i) (hS i) (hfit i hi)).1 x hball hx
  rw [nonemptyAffineProjection_dist_self]
  calc
    _ ≤ ε * (1024 * i.radius) := hdist.le
    _ = _ := by rw [hrad]; ring

theorem exists_active_level_projection_maps (hnd : n ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
      (hT : ∀ i, IsAffineNPlane n (T i)),
      (∀ i, activeRegionCell
          (fun q => bilateralBeta n μ q.center (1024 * q.radius) < ε) i →
        bilateralPlaneError μ i.center (1024 * i.radius) (T i) < ε) ∧
      ∀ s : ℕ,
        Continuous (activeLevelProjectionMap μ R hR k z
          (fun q => bilateralBeta n μ q.center (1024 * q.radius) < ε) s T hT) ∧
        (∀ x ∈ μ.support,
          dist (activeLevelProjectionMap μ R hR k z
            (fun q => bilateralBeta n μ q.center (1024 * q.radius) < ε) s T hT x) x ≤
              (1024 * ε) * latticeRadius R (k + s)) ∧
        (∀ x, 5 * latticeRadius R (k + s) ≤ cellRegionStoppingScale μ R hR k z
            (fun q => bilateralBeta n μ q.center (1024 * q.radius) < ε) x →
          activeLevelProjectionMap μ R hR k z
            (fun q => bilateralBeta n μ q.center (1024 * q.radius) < ε) s T hT x = x) := by
  classical
  let G : SupportCellDescendant μ R hR k z → Prop :=
    fun q => bilateralBeta n μ q.center (1024 * q.radius) < ε
  obtain ⟨T₀, hT₀⟩ := exists_affine_n_plane hnd
  have hex (i : SupportCellDescendant μ R hR k z) :
      ∃ T : AffineSubspace ℝ (Ambient d), IsAffineNPlane n T ∧
        (activeRegionCell G i → bilateralPlaneError μ i.center (1024 * i.radius) T < ε) := by
    by_cases hi : activeRegionCell G i
    · obtain ⟨T, hT, hf⟩ := exists_bilateral_plane_error_lt hnd μ i.center
        (1024 * i.radius) ε (activeRegionCell_good G i hi)
      exact ⟨T, hT, fun _ => hf⟩
    · exact ⟨T₀, hT₀, fun h => (hi h).elim⟩
  choose T hT hfit using hex
  refine ⟨T, hT, hfit, ?_⟩
  intro s
  refine ⟨activeLevelProjectionMap_continuous μ R hR k z G s T hT, ?_, ?_⟩
  · intro x hx
    apply activeLevelProjectionMap_support_displacement μ R hR k z G s T hT ε hε.le
      (fun i hi => hfit i ((mem_activeLevelIndex μ R hR k z G s i).mp hi).2) x hx
  · intro x hx
    exact activeLevelProjectionMap_eq_self_of_large_scale μ R hR k z G s T hT x hx

end

end RieszRectifiability

end OAI
