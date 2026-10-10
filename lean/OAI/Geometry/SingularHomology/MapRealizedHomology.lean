import OAI.Geometry.SingularHomology.MapHomology
import OAI.Dynamics.EntropyCounterexample.RealizedConstruction
import OAI.Dynamics.EntropyCounterexample.HomotopySpectrum
import OAI.Dynamics.EntropyCounterexample.SpectralRadius

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem continuous_realizedMap_actual (L : ℝ) (hL : 2 < L) :
    Continuous (realizedMap L hL) :=
  continuous_realizedMap L hL (concreteMap_continuous_for_homotopy L hL)

theorem realizedMap_eigenvector_of_sphere (n : ℕ) (L : ℝ) (hL : 2 < L)
    (c : ℝ) (v : RealSingularHomology n Sphere) (hv : v ≠ 0)
    (heig : realHomologyMap n rawSphereSquare continuous_rawSphereSquare v = c • v) :
    ∃ w : RealSingularHomology n (CounterexampleManifold 3), w ≠ 0 ∧
      realHomologyMap n (realizedMap L hL) (continuous_realizedMap_actual L hL) w = c • w := by
  obtain ⟨w, hw, he⟩ := concreteMap_eigenvector_of_sphere n L hL c v hv heig
  exact realizedMap_eigenvector L hL (concreteMap_continuous_for_homotopy L hL)
    n c w hw he

theorem totalRealHomologySpectralRadius_realizedMap_eq_normalForm
    (L : ℝ) (hL : 2 < L) :
    totalRealHomologySpectralRadius (realizedMap L hL)
        (continuous_realizedMap_actual L hL) =
      totalRealHomologySpectralRadius (@rawNormalForm 3) continuous_rawNormalForm := by
  rw [totalRealHomologySpectralRadius_realizedMap]
  exact (totalRealHomologySpectralRadius_eq_of_homotopy continuous_rawNormalForm
    (concreteMap_continuous_for_homotopy L hL) (concreteMapHomotopy L hL)).symm

theorem homologyEigenvalueRadii_concreteMap_eq_normalForm (L : ℝ) (hL : 2 < L) :
    homologyEigenvalueRadii (concreteMap L hL) (concreteMap_continuous_for_homotopy L hL) =
      homologyEigenvalueRadii (@rawNormalForm 3) continuous_rawNormalForm :=
  (homologyRadiusSet_eq_of_homotopy continuous_rawNormalForm
    (concreteMap_continuous_for_homotopy L hL) (concreteMapHomotopy L hL)).symm

theorem log_two_le_realizedMap_radius_of_sphere (L : ℝ) (hL : 2 < L)
    (v : RealSingularHomology 2 Sphere) (hv : v ≠ 0)
    (heig : realHomologyMap 2 rawSphereSquare continuous_rawSphereSquare v = (2 : ℝ) • v)
    (hbounded : BddAbove
      (homologyEigenvalueRadii (@rawNormalForm 3) continuous_rawNormalForm)) :
    Real.log (2 : ℝ) ≤ Real.log (totalRealHomologySpectralRadius
      (realizedMap L hL) (continuous_realizedMap_actual L hL)) := by
  obtain ⟨w, hw, he⟩ := concreteMap_eigenvector_of_sphere 2 L hL 2 v hv heig
  have hb : BddAbove (homologyEigenvalueRadii (concreteMap L hL)
      (concreteMap_continuous_for_homotopy L hL)) := by
    rw [homologyEigenvalueRadii_concreteMap_eq_normalForm]
    exact hbounded
  rw [totalRealHomologySpectralRadius_realizedMap]
  exact log_two_le_log_totalRealHomologySpectralRadius
    (concreteMap_continuous_for_homotopy L hL) hb hw he

theorem exists_counterexample_of_concrete_obligations (L : ℝ) (hL : 2 < L)
    (hC1 : IsC1SelfMap 3 (realizedMap L hL))
    (hentropy : Dynamics.coverEntropy (realizedMap L hL) Set.univ = (0 : EReal))
    (hsphere : ∃ v : RealSingularHomology 2 Sphere, v ≠ 0 ∧
      realHomologyMap 2 rawSphereSquare continuous_rawSphereSquare v = (2 : ℝ) • v)
    (hbounded : BddAbove
      (homologyEigenvalueRadii (@rawNormalForm 3) continuous_rawNormalForm)) :
    ∃ q : ℕ, 0 < q ∧ ∃ f : CounterexampleManifold q → CounterexampleManifold q,
      ∃ hf : IsC1SelfMap q f,
        Dynamics.coverEntropy f (Set.univ : Set (CounterexampleManifold q)) = (0 : EReal) ∧
        (∃ v : RealSingularHomology 2 (CounterexampleManifold q),
          v ≠ 0 ∧ realHomologyMap 2 f hf.1 v = (2 : ℝ) • v) ∧
        0 < Real.log (2 : ℝ) ∧
        Real.log (2 : ℝ) ≤ Real.log (totalRealHomologySpectralRadius f hf.1) ∧
        ¬ Function.Bijective f ∧ 5 ≤ 2 * q + 3 := by
  obtain ⟨v, hv, he⟩ := hsphere
  refine ⟨3, by norm_num, realizedMap L hL, hC1, hentropy,
    realizedMap_eigenvector_of_sphere 2 L hL 2 v hv he,
    Real.log_pos (by norm_num), ?_, realizedMap_not_bijective L hL, by norm_num⟩
  exact log_two_le_realizedMap_radius_of_sphere L hL v hv he hbounded

end Problem340.Construction

end

end OAI
