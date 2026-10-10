import OAI.Geometry.IsometricImmersion.Calculus.HessianJetBounds
import OAI.Geometry.IsometricImmersion.Coordinates.CoordinateFirstBounds

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Geometry

def riemannFirstBound (G d : ℝ) : ℝ :=
  2 * christoffelJetBound G d + 8 * (christoffelJetBound G d)^2
def curvatureNumeratorFirstBound (G d : ℝ) : ℝ := 4 * G * riemannFirstBound G d
def curvatureFirstBound (G d : ℝ) : ℝ :=
  curvatureNumeratorFirstBound G d / d +
    (curvatureNumeratorFirstBound G d + 16 * G^2 * (curvatureNumeratorFirstBound G d / d)) / d

theorem riemannFirstBound_nonneg {G d : ℝ} (hG : 0 ≤ G) (hd : 0 < d) :
    0 ≤ riemannFirstBound G d := by
  have hΓ := christoffelJetBound_nonneg hG hd
  dsimp [riemannFirstBound]; positivity

theorem curvatureFirstBound_nonneg {G d : ℝ} (hG : 0 ≤ G) (hd : 0 < d) :
    0 ≤ curvatureFirstBound G d := by
  have hR := riemannFirstBound_nonneg hG hd
  dsimp [curvatureFirstBound, curvatureNumeratorFirstBound]; positivity

variable {g : MetricField} {U : Set Coord} {G d : ℝ}

theorem riemann_coordinate_bound_one
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) (l k i j : Fin 2) :
    CoordinateBound (riemann g l k i j) U 1 (riemannFirstBound G d) := by
  have hΓ := christoffelJetBound_nonneg hG hd
  have hΓB (a b c : Fin 2) := christoffel_coordinate_bound hg hU hG hd hgB hdet a b c
  have hΓ1 (a b c : Fin 2) : CoordinateBound (christoffel g a b c) U 1 (christoffelJetBound G d) :=
    (hΓB a b c).mono (by norm_num) le_rfl
  have hΓd (a b c e : Fin 2) : CoordinateBound (coordPartial e (christoffel g a b c)) U 1
      (christoffelJetBound G d) :=
    ((hΓB a b c).mono (by norm_num : 2 ≤ 3) le_rfl).partial_bound e
  have hΓs (a b c : Fin 2) := christoffel_contDiffOn hg hU a b c
  have hm (m : Fin 2) := CoordinateBound.sub
    ((hΓs m j k).mul (hΓs l i m)) ((hΓs m i k).mul (hΓs l j m)) hU
    (CoordinateBound.mul_through_one (hΓs m j k) (hΓs l i m) hU hΓ hΓ (hΓ1 m j k) (hΓ1 l i m))
    (CoordinateBound.mul_through_one (hΓs m i k) (hΓs l j m) hU hΓ hΓ (hΓ1 m i k) (hΓ1 l j m))
  have hms (m : Fin 2) := ((hΓs m j k).mul (hΓs l i m)).sub ((hΓs m i k).mul (hΓs l j m))
  have hs := CoordinateBound.add (hms 0) (hms 1) hU (hm 0) (hm 1)
  have hdiff := CoordinateBound.sub (partial_contDiffOn (hΓs l j k) hU i)
    (partial_contDiffOn (hΓs l i k) hU j) hU (hΓd l j k i) (hΓd l i k j)
  have hb := CoordinateBound.add
    ((partial_contDiffOn (hΓs l j k) hU i).sub (partial_contDiffOn (hΓs l i k) hU j))
    ((hms 0).add (hms 1)) hU hdiff hs
  convert hb using 1 <;> first
    | (funext p; simp only [riemann, Fin.sum_univ_two])
    | (dsimp [riemannFirstBound]; ring)

theorem gaussianCurvature_coordinate_bound_one
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) :
    CoordinateBound (gaussianCurvature g) U 1 (curvatureFirstBound G d) := by
  have hR := riemannFirstBound_nonneg hG hd
  have hprod (l : Fin 2) := CoordinateBound.mul_through_one (hg.1 0 l)
    (riemann_contDiffOn hg hU l 1 0 1) hU hG hR
    ((hgB 0 l).mono (by norm_num) le_rfl)
    (riemann_coordinate_bound_one hg hU hG hd hgB hdet l 1 0 1)
  have hprodS (l : Fin 2) := (hg.1 0 l).mul (riemann_contDiffOn hg hU l 1 0 1)
  have hsum := CoordinateBound.add (hprodS 0) (hprodS 1) hU (hprod 0) (hprod 1)
  have hn : CoordinateBound (fun p => g p 0 0 * riemann g 0 1 0 1 p +
      g p 0 1 * riemann g 1 1 0 1 p) U 1 (curvatureNumeratorFirstBound G d) := by
    convert hsum using 1
    dsimp [curvatureNumeratorFirstBound]
    ring
  have hnb : 0 ≤ curvatureNumeratorFirstBound G d := by dsimp [curvatureNumeratorFirstBound]; positivity
  have hdb : CoordinateBound (fun p => (g p).det) U 1 (16 * G^2) :=
    (metricDet_coordinate_bound hg hU hG (fun i j => (hgB i j).mono (by norm_num) le_rfl)).mono
      (by norm_num) le_rfl
  have hb := CoordinateBound.div_through_one ((hprodS 0).add (hprodS 1))
    (metricDet_contDiffOn hg) hU hnb (by positivity : 0 ≤ 16 * G^2) hd hn hdb hdet
  convert hb using 1 <;> try rfl
  funext p
  simp only [gaussianCurvature, Fin.sum_univ_two]

end SmoothLocal.Geometry

end

end OAI
