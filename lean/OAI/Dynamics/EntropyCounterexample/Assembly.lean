import OAI.Dynamics.EntropyCounterexample.MapFinalReduction
import OAI.Geometry.SingularHomology.SphereSquareHomologyTransport
import OAI.Geometry.SingularHomology.FiniteCoverHomologyRawBase
import OAI.Geometry.SingularHomology.SphereMayerVietorisEigen
import OAI.Dynamics.EntropyCounterexample.SmallCoverNaturality
import OAI.Geometry.SingularHomology.SingularSmallComparison
import OAI.Geometry.SingularHomology.SingularSubdivisionEventuallySmall

namespace OAI
noncomputable section
open CategoryTheory
open Problem340 Problem340.SphereCover Problem340.SingularSmallChains
open Problem340.SmallCoverMayerVietoris Problem340.SphereMayerVietorisEigen
namespace Problem340.CounterexampleAssembly804

theorem sphereEigen : ∃ v : RealSingularHomology 2 StandardSphere2, v ≠ 0 ∧
    realHomologyMap 2 SphereDoubling.sphereMap SphereDoubling.continuous_sphereMap v =
      (2 : ℝ) • v := by
  let : QuasiIso (inclusion coverFamily) :=
    inclusion_quasiIso_of_natural_subdivision_zero coverFamily
      ActualSingularSubdivision.chainMap ActualSingularSubdivision.chainMap_app_zero
      (exists_actualSubdivision_pow_mem_range coverFamily coverFamily_isOpen
        (by rw [iUnion_coverFamily]))
  let e := (singularConnectingIsoOfQuasiIsoAt northComplement southComplement 1
    (by decide)).toLinearEquiv
  obtain ⟨w, hw, heigen⟩ := exists_overlap_square_eigenvector
  refine ⟨e.symm w, (map_ne_zero_iff e.symm e.symm.injective).2 hw, ?_⟩
  apply e.injective
  have h := singularConnectingIsoOfQuasiIsoAt_naturality_apply
    SphereDoubling.sphereMap SphereDoubling.continuous_sphereMap
    northComplement southComplement northComplement southComplement
    mapsTo_northComplement mapsTo_southComplement 1 (by decide) (e.symm w)
  have hh : e (realHomologyMap 2 SphereDoubling.sphereMap
      SphereDoubling.continuous_sphereMap (e.symm w)) =
      realHomologyMap 1 SphereOverlapDoubling.overlapSquare
        SphereOverlapDoubling.continuous_overlapSquare (e (e.symm w)) := by
    simpa only [e, CategoryTheory.Iso.toLinearEquiv_apply, intersectionMap, restrictMap_eq_overlapSquare] using h
  rw [hh, e.apply_symm_apply, heigen, map_smul, e.apply_symm_apply]

theorem exists_counterexample :
    ∃ q : ℕ, 0 < q ∧ ∃ f : CounterexampleManifold q → CounterexampleManifold q, ∃ hf : IsC1SelfMap q f, Dynamics.coverEntropy f (Set.univ : Set (CounterexampleManifold q)) = (0 : EReal) ∧ (∃ v : RealSingularHomology 2 (CounterexampleManifold q), v ≠ 0 ∧ realHomologyMap 2 f hf.1 v = (2 : ℝ) • v) ∧ 0 < Real.log (2 : ℝ) ∧ Real.log (2 : ℝ) ≤ Real.log (totalRealHomologySpectralRadius f hf.1) ∧ ¬ Function.Bijective f ∧ 5 ≤ 2 * q + 3 := by
  have hsphere : ∃ v : RealSingularHomology 2 (OnePoint ℂ), v ≠ 0 ∧
      realHomologyMap 2 rawSphereSquare continuous_rawSphereSquare v = (2 : ℝ) • v := by
    obtain ⟨v, hv, he⟩ := sphereEigen
    exact rawSphereSquare_eigenvector_of_standard 2 2 v hv he
  let G := CoordinateGoodCover.rawBaseGoodCover
  let : QuasiIso (inclusion G.carrier) :=
    inclusion_quasiIso_of_natural_subdivision_zero G.carrier
      ActualSingularSubdivision.chainMap ActualSingularSubdivision.chainMap_app_zero
      (exists_actualSubdivision_pow_mem_range G.carrier G.isOpen
        (by rw [G.iUnion_eq_univ]))
  exact Construction.exists_counterexample_of_sphere_and_base_homology hsphere
    FiniteCoverHomology.rawBase_homologyEigenvalueRadii_bddAbove

end Problem340.CounterexampleAssembly804

end

end OAI
