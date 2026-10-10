import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveProjectionLocalGraph
import OAI.Analysis.RieszRectifiability.Surfaces.PerturbedBallCoverage

namespace OAI

/-!
# Disk coverage by active projections

Affine projection preserves tangential coordinates in the reference plane. The tangential part
of the active projection is therefore a small Lipschitz perturbation of the identity on a disk.
Its displacement bound gives coverage of a shrunken disk, and the quantitative smallness
condition yields coverage of the concentric half disk at the lattice scale.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry
open scoped NNReal

theorem nonemptyAffineProjection_tangential {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : (S : Set (Ambient d)).Nonempty)
    (x : Ambient d) :
    S.direction.orthogonalProjectionOnto (nonemptyAffineProjection S hS x) =
      S.direction.orthogonalProjectionOnto x := by
  let : Nonempty S := hS.to_subtype
  have h := orthogonalProjection_vsub_orthogonalProjection S x
  change S.direction.orthogonalProjectionOnto (x - (orthogonalProjection S x : Ambient d)) = 0 at h
  rw [map_sub] at h
  exact (sub_eq_zero.mp h).symm

theorem activeLevelProjectionMap_covers_shrunk_disk {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hsmall : activeProjectionError d ε ≤ 1 / 4)
    (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (q : SupportCellDescendant μ R hR k z)
    (hq : q ∈ activeLevelIndex μ R hR k z Good t)
    (a : (S q).direction) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (g : closedBall a ρ → Ambient d)
    (hg : LipschitzWith 2 g)
    (hcoordinates : ∀ u, (S q).direction.orthogonalProjectionOnto (g u) = u.val)
    (hlocal : ∀ u, g u ∈ closedBall q.center (3 * latticeRadius R (k + t))) :
    closedBall a (ρ - (262144 * ε) * latticeRadius R (k + t)) ⊆
      Set.range (fun u : closedBall a ρ =>
        (S q).direction.orthogonalProjectionOnto
          (activeLevelProjectionMap μ R hR k z Good t S hS (g u))) := by
  let P := (S q).direction
  let r := latticeRadius R (k + t)
  let η := activeProjectionError d ε
  let σ := activeLevelProjectionMap μ R hR k z Good t S hS
  let f : closedBall a ρ → P := fun u => P.orthogonalProjectionOnto (σ (g u))
  obtain ⟨hη, hεsmall⟩ := activeProjectionError_small_parameters d ε hε hsmall
  have hcoord (u : closedBall a ρ) : P.starProjection (g u) = (u.val : Ambient d) :=
    congrArg (fun v : P => (v : Ambient d)) (hcoordinates u)
  have hdisp : ∀ u : closedBall a ρ, dist (f u) u.val ≤ (262144 * ε) * r := by
    intro u
    have ht : P.orthogonalProjectionOnto (nonemptyAffineProjection (S q) (hS q).1 (g u)) = u.val := by
      rw [nonemptyAffineProjection_tangential, hcoordinates u]
    have hdist := activeLevelProjectionMap_reference_displacement μ R hR k z Good t S hS
      ε hε hεsmall hfit q hq (g u) (hlocal u)
    calc
      _ = dist (P.orthogonalProjectionOnto (σ (g u)))
          (P.orthogonalProjectionOnto (nonemptyAffineProjection (S q) (hS q).1 (g u))) := by rw [ht]
      _ ≤ dist (σ (g u)) (nonemptyAffineProjection (S q) (hS q).1 (g u)) := by
        change ‖P.starProjection (σ (g u)) -
          P.starProjection (nonemptyAffineProjection (S q) (hS q).1 (g u))‖ ≤ _
        rw [← map_sub]
        exact P.norm_starProjection_apply_le _
      _ ≤ _ := hdist
  have herr : LipschitzWith (Real.toNNReal (2 * η))
      (fun u : closedBall a ρ => f u - u.val) := by
    apply LipschitzWith.of_dist_le'
    intro u v
    have hself : P.starProjection (P.starProjection (g u - g v)) =
        P.starProjection (g u - g v) :=
      P.starProjection_eq_self_iff.mpr (P.orthogonalProjectionOnto (g u - g v)).property
    have heq : (f u - u.val) - (f v - v.val) =
        P.orthogonalProjectionOnto ((σ (g u) - σ (g v)) - P.starProjection (g u - g v)) := by
      apply Subtype.ext
      change (P.starProjection (σ (g u)) - (u.val : Ambient d)) -
        (P.starProjection (σ (g v)) - (v.val : Ambient d)) =
        P.starProjection ((σ (g u) - σ (g v)) - P.starProjection (g u - g v))
      rw [map_sub, hself, map_sub, map_sub, hcoord u, hcoord v]
      abel
    have hinc := activeLevelProjectionMap_reference_increment μ R hR k z Good t S hS
      ε hε hεsmall hfit q hq (g u) (g v) (hlocal u) (hlocal v)
    have hLip : dist (g u) (g v) ≤ 2 * dist u v := by
      simpa only [NNReal.coe_ofNat] using! hg.dist_le_mul u v
    rw [dist_eq_norm, heq]
    calc
      _ ≤ ‖(σ (g u) - σ (g v)) - P.starProjection (g u - g v)‖ :=
        P.norm_starProjection_apply_le _
      _ ≤ η * dist (g u) (g v) := hinc
      _ ≤ η * (2 * dist u v) := mul_le_mul_of_nonneg_left hLip hη
      _ = (2 * η) * dist u v := by ring
  have hcontract : Real.toNNReal (2 * η) < 1 := by
    have hreal : (Real.toNNReal (2 * η) : ℝ) < 1 := by
      rw [Real.coe_toNNReal _ (mul_nonneg (by norm_num) hη)]
      change η ≤ 1 / 4 at hsmall
      linarith
    exact_mod_cast hreal
  exact closedBall_covered_by_lipschitz_perturbation a ρ ((262144 * ε) * r)
    hρ (Real.toNNReal (2 * η)) hcontract f hdisp herr

theorem activeLevelProjectionMap_covers_half_disk {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hsmall : activeProjectionError d ε ≤ 1 / 4)
    (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (q : SupportCellDescendant μ R hR k z)
    (hq : q ∈ activeLevelIndex μ R hR k z Good t)
    (a : (S q).direction)
    (g : closedBall a (latticeRadius R (k + t)) → Ambient d)
    (hg : LipschitzWith 2 g)
    (hcoordinates : ∀ u, (S q).direction.orthogonalProjectionOnto (g u) = u.val)
    (hlocal : ∀ u, g u ∈ closedBall q.center (3 * latticeRadius R (k + t))) :
    closedBall a (latticeRadius R (k + t) / 2) ⊆
      Set.range (fun u : closedBall a (latticeRadius R (k + t)) =>
        (S q).direction.orthogonalProjectionOnto
          (activeLevelProjectionMap μ R hR k z Good t S hS (g u))) := by
  let r := latticeRadius R (k + t)
  have hr : 0 < r := latticeRadius_pos R hR (k + t)
  have hdelta : (262144 * ε) * r ≤ r / 2 := by
    have hpow : (1 : ℝ) ≤ (9 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right hpow hε.le
    have hbound : 262144 * ε ≤ 1 / 2 := by
      unfold activeProjectionError at hsmall
      nlinarith
    have h := mul_le_mul_of_nonneg_right hbound hr.le
    linarith
  have hcover := activeLevelProjectionMap_covers_shrunk_disk μ R hR k z Good t S hS
    ε hε hsmall hfit q hq a r hr.le g hg hcoordinates hlocal
  intro b hb
  apply hcover
  have hb' : dist b a ≤ r / 2 := hb
  change dist b a ≤ r - (262144 * ε) * r
  linarith

end

end RieszRectifiability

end OAI
