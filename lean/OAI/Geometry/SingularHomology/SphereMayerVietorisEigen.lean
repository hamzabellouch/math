import OAI.Geometry.SingularHomology.SmallCoverMayerVietoris
import OAI.Dynamics.EntropyCounterexample.SphereOverlapDoubling
import OAI.Dynamics.EntropyCounterexample.SphereSquareEquator
import OAI.Geometry.SingularHomology.CircleHomologySupport

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340.SphereMayerVietorisEigen

open SphereCover SingularSmallChains SmallCoverMayerVietoris

lemma doubling_south_eq_chartSouthPole : SphereDoubling.south = chartSouthPole := by
  symm
  apply (SphereDoubling.eq_south_iff chartSouthPole).mpr
  simp [chartSouthPole, sphereOfComplex_val_two]

lemma mapsTo_northComplement :
    Set.MapsTo SphereDoubling.sphereMap northComplement northComplement := by
  intro x hx
  change SphereDoubling.sphereMap x ≠ chartNorthPole
  intro h
  apply hx
  change x = chartNorthPole
  rw [← doubling_north_eq_chartNorthPole] at h ⊢
  exact (SphereDoubling.sphereMap_eq_north_iff x).mp h

lemma mapsTo_southComplement :
    Set.MapsTo SphereDoubling.sphereMap southComplement southComplement := by
  intro x hx
  change SphereDoubling.sphereMap x ≠ chartSouthPole
  intro h
  apply hx
  change x = chartSouthPole
  rw [← doubling_south_eq_chartSouthPole] at h ⊢
  exact (SphereDoubling.sphereMap_eq_south_iff x).mp h

lemma restrictMap_eq_overlapSquare :
    (restrictMap SphereDoubling.sphereMap SphereDoubling.continuous_sphereMap
      (northComplement ∩ southComplement) (northComplement ∩ southComplement)
      (fun _ hx => ⟨mapsTo_northComplement hx.1, mapsTo_southComplement hx.2⟩) :
        SphereOverlapDoubling.Overlap → SphereOverlapDoubling.Overlap) =
      SphereOverlapDoubling.overlapSquare := by
  funext x
  apply Subtype.ext
  exact (SphereOverlapDoubling.overlapSquare_coe x).symm

abbrev coverFamily := binaryCover northComplement southComplement

lemma coverFamily_isOpen (b : Bool) : IsOpen (coverFamily b) := by
  cases b
  · exact isOpen_southComplement
  · exact isOpen_northComplement

lemma coverFamily_covers (x : StandardSphere2) : ∃ b, x ∈ coverFamily b := by
  have hx : x ∈ northComplement ∪ southComplement := by
    rw [SphereCover.cover]
    trivial
  rcases hx with hx | hx
  · exact ⟨true, hx⟩
  · exact ⟨false, hx⟩

lemma iUnion_coverFamily : (⋃ b, coverFamily b) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact coverFamily_covers x

def homologyEquivClock
    [QuasiIsoAt (inclusion coverFamily) 2] :
    RealSingularHomology 2 StandardSphere2 ≃ₗ[ℝ]
      RealSingularHomology 1 StandardClock :=
  (singularConnectingIsoOfQuasiIsoAt northComplement southComplement 1
    (by decide)).toLinearEquiv.trans (overlapHomologyEquivClock 1)

theorem exists_overlap_square_eigenvector :
    ∃ v : RealSingularHomology 1 SphereOverlapDoubling.Overlap, v ≠ 0 ∧
      realHomologyMap 1 SphereOverlapDoubling.overlapSquare
        SphereOverlapDoubling.continuous_overlapSquare v = (2 : ℝ) • v := by
  obtain ⟨w, hw, heigen⟩ := CircleHomology.exists_clock_doubling_eigenvector
  let e := overlapHomologyEquivClock 1
  refine ⟨e.symm w, ?_, ?_⟩
  · exact (map_ne_zero_iff e.symm e.symm.injective).2 hw
  · apply e.injective
    change overlapHomologyEquivClock 1
      (realHomologyMap 1 SphereOverlapDoubling.overlapSquare
        SphereOverlapDoubling.continuous_overlapSquare (e.symm w)) =
      e ((2 : ℝ) • e.symm w)
    rw [SphereOverlapDoubling.overlapHomologyEquivClock_intertwines]
    change realHomologyMap 1 CircleClockDoubling.clockDouble
      CircleClockDoubling.continuous_clockDouble (e (e.symm w)) =
      e ((2 : ℝ) • e.symm w)
    rw [e.apply_symm_apply, heigen, map_smul, e.apply_symm_apply]

end Problem340.SphereMayerVietorisEigen

end

end OAI
