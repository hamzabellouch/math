import OAI.Geometry.IsometricImmersion.Calculus.ClosedSquareJetBounds
import OAI.Geometry.IsometricImmersion.Immersions.HeightPFirstBounds

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.ODE

def heightDriftErrorBound (G Z d c : ℝ) : ℝ :=
  heightEnergyJetBound G Z / c^2 *
    (2 * christoffelJetBound G d + hessianJetBound G Z d / c) +
    ((202 / 100 : ℝ) * (G + Z)^2) / c

theorem heightDriftErrorBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightDriftErrorBound G Z d c := by
  have hE := heightEnergyJetBound_nonneg (Z := Z) hG
  have hΓ := christoffelJetBound_nonneg hG hd
  have hH := hessianJetBound_nonneg hG hZ hd
  dsimp [heightDriftErrorBound]; positivity

theorem exists_open_low_height_coefficients
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) :
    ∃ V : Set Coord, IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      (∀ p ∈ V, covHessian g z p 1 1 ≠ 0) ∧
      CoordinateBound (hessianQuotient g z) modelSquare 3 (heightQuotientJetBound G Z d c) ∧
      CoordinateBound (heightEnergy g z) modelSquare 3 (heightEnergyJetBound G Z) ∧
      CoordinateBound (darbouxG g z) modelSquare 3 (darbouxGJetBound G Z d c) ∧
      (∀ i : Fin 2, CoordinateBound (heightPFirst g z i) modelSquare 1 (heightPFirstBound G Z d c)) ∧
      (∀ k i j : Fin 2, CoordinateBound (christoffel g k i j) modelSquare 3 (christoffelJetBound G d)) := by
  obtain ⟨V, hV, hSV, hVU, hVne, _, hqB⟩ :=
    exists_open_quotient_domain_with_closed_low_bounds hg hU hSU hz hG hZ hd hc hgB hzB hdet hyy
  have hIU : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hgI : SmoothPositiveOn g (interior modelSquare) :=
    ⟨fun i j => (hg.1 i j).mono hIU, fun p hp => hg.2 p (hIU hp)⟩
  have hgV : SmoothPositiveOn g V :=
    ⟨fun i j => (hg.1 i j).mono hVU, fun p hp => hg.2 p (hVU hp)⟩
  have hgBI (i j : Fin 2) := (hgB i j).restrict_domain interior_subset
  have hzBI := hzB.restrict_domain interior_subset
  have hdI (p : Coord) (hp : p ∈ interior modelSquare) := hdet p (interior_subset hp)
  have hyyI (p : Coord) (hp : p ∈ interior modelSquare) := hyy p (interior_subset hp)
  refine ⟨V, hV, hSV, hVU, hVne, hqB, ?_, ?_, ?_, ?_⟩
  · apply CoordinateBound.of_modelSquare_interior (heightEnergy_contDiffOn hg hU hz) hU hSU
    exact heightEnergy_coordinate_bound hgI isOpen_interior (hz.mono hIU) hG hZ
      (fun i j => (hgBI i j).mono (by norm_num) le_rfl) (hzBI.mono (by norm_num) le_rfl)
  · apply CoordinateBound.of_modelSquare_interior
      (darbouxG_contDiffOn hgV hV (hz.mono hVU) hVne) hV hSV
    exact darbouxG_coordinate_bound hgI isOpen_interior (hz.mono hIU) hG hZ hd hc hgBI hzBI hdI hyyI
  · intro i
    apply CoordinateBound.of_modelSquare_interior
      (heightPFirst_contDiffOn hgV hV (hz.mono hVU) hVne i) hV hSV
    exact heightPFirst_coordinate_bound_one hgI isOpen_interior (hz.mono hIU) hG hZ hd hc hgBI hzBI hdI hyyI i
  · intro k i j
    apply CoordinateBound.of_modelSquare_interior (christoffel_contDiffOn hg hU k i j) hU hSU
    exact christoffel_coordinate_bound hgI isOpen_interior hG hd hgBI hdI k i j

theorem curvatureDriftError_bound_original_data
    {g : MetricField} {z : Coord → ℝ} {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hEB : CoordinateBound (heightEnergy g z) modelSquare 3 (heightEnergyJetBound G Z))
    (hHB : CoordinateBound (fun p => covHessian g z p 1 1) modelSquare 3 (hessianJetBound G Z d))
    (hΓB : ∀ k i j : Fin 2, CoordinateBound (christoffel g k i j) modelSquare 3 (christoffelJetBound G d))
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ) / 100)
    {p : Coord} (hp : p ∈ modelSquare) :
    |curvatureDriftError g z p| ≤ heightDriftErrorBound G Z d c := by
  have ht : |connectionTraceY g p| ≤ 2 * christoffelJetBound G d := by
    exact ((abs_add_le _ _).trans
      (add_le_add (hΓB 0 0 1 [] (by norm_num) p hp) (hΓB 1 1 1 [] (by norm_num) p hp))).trans
        (le_of_eq (by ring))
  exact curvatureDriftError_bound_from_low_data g z p c (heightEnergyJetBound G Z)
    (hessianJetBound G Z d) (2 * christoffelJetBound G d) (G + Z)
    hc (hyy p hp) (hEB [] (by norm_num) p hp) (hHB [1] (by norm_num) p hp) ht
    (fun i j => (hgB i j [] (by norm_num) p hp).trans (by linarith))
    (fun i => (hzB [i] (by norm_num) p hp).trans (by linarith)) (hsmall p hp)

end SmoothLocal.Geometry

end

end OAI
