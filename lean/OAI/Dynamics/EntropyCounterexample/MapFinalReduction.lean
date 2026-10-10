import OAI.Geometry.SingularHomology.MapRealizedHomology
import OAI.Dynamics.EntropyCounterexample.RawSpectrumFactor
import OAI.Dynamics.EntropyCounterexample.MapC1Complete
import OAI.Dynamics.EntropyCounterexample.MapEntropyComplete

namespace OAI

noncomputable section

namespace Problem340.Construction

open PolynomialSpectrum

theorem concreteEntropy_eq_zero (L : ℝ) (hL : 2 < L) :
    concreteEntropy L hL = (0 : EReal) := by
  rw [← coverEntropy_realizedMap]
  exact coverEntropy_realizedMap_eq_zero L hL

theorem homologyEigenvalueRadii_eq_iUnion {X : Type} [TopologicalSpace X]
    (f : X → X) (hf : Continuous f) :
    homologyEigenvalueRadii f hf = ⋃ n, pairRadii (realHomologyMap n f hf) := by
  simp only [homologyEigenvalueRadii, pairRadii, Set.iUnion_ofPred]

theorem bddAbove_normalForm_of_rawBase
    (hB : BddAbove (homologyEigenvalueRadii rawBaseSquare continuous_rawBaseSquare)) :
    BddAbove (homologyEigenvalueRadii (@rawNormalForm 3) continuous_rawNormalForm) := by
  rw [homologyEigenvalueRadii_eq_iUnion] at hB ⊢
  apply bddAbove_homology_pairRadii_of_homotopy_factor
    (@rawNormalForm 3) rawFactorInclusion rawBaseProjection
    continuous_rawNormalForm continuous_rawFactorInclusion continuous_rawBaseProjection
    (ContinuousMap.Homotopy.refl _)
  exact hB

theorem exists_C1_zero_entropy_nonbijective_realizedMap :
    ∃ (L : ℝ) (hL : 2 < L), IsC1SelfMap 3 (realizedMap L hL) ∧
      Dynamics.coverEntropy (realizedMap L hL) Set.univ = (0 : EReal) ∧
      ¬ Function.Bijective (realizedMap L hL) := by
  obtain ⟨L, hL, hC1⟩ := exists_isC1SelfMap_realizedMap
  exact ⟨L, hL, hC1, coverEntropy_realizedMap_eq_zero L hL,
    realizedMap_not_bijective L hL⟩

theorem exists_counterexample_of_sphere_and_base_homology
    (hsphere : ∃ v : RealSingularHomology 2 Sphere, v ≠ 0 ∧
      realHomologyMap 2 rawSphereSquare continuous_rawSphereSquare v = (2 : ℝ) • v)
    (hbase : BddAbove
      (homologyEigenvalueRadii rawBaseSquare continuous_rawBaseSquare)) :
    ∃ q : ℕ, 0 < q ∧ ∃ f : CounterexampleManifold q → CounterexampleManifold q,
      ∃ hf : IsC1SelfMap q f,
        Dynamics.coverEntropy f (Set.univ : Set (CounterexampleManifold q)) = (0 : EReal) ∧
        (∃ v : RealSingularHomology 2 (CounterexampleManifold q),
          v ≠ 0 ∧ realHomologyMap 2 f hf.1 v = (2 : ℝ) • v) ∧
        0 < Real.log (2 : ℝ) ∧
        Real.log (2 : ℝ) ≤ Real.log (totalRealHomologySpectralRadius f hf.1) ∧
        ¬ Function.Bijective f ∧ 5 ≤ 2 * q + 3 := by
  obtain ⟨L, hL, hC1⟩ := exists_isC1SelfMap_realizedMap
  exact exists_counterexample_of_concrete_obligations L hL hC1
    (coverEntropy_realizedMap_eq_zero L hL) hsphere
    (bddAbove_normalForm_of_rawBase hbase)

end Problem340.Construction

end

end OAI
