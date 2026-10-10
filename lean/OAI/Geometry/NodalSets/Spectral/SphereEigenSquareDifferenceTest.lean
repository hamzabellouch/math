import OAI.Geometry.NodalSets.Elliptic.RealSquareDifferenceTest
import OAI.Geometry.NodalSets.Spectral.SphereEigenDifferentiatedEquation

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_eigen_square_difference_test (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) :
    ∃ C1 > 0, ∀ (mu : ℝ), mu ≠ 0 → ∀ (f : SphereWeightedL2 d),
      sphereL2Resolvent d f=mu • f →
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))),
        (∑ a, ∑ j, ‖H a j‖^2) ≤ C1*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        (∀ a j psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
          (∫ x in Yau.realCenteredCube 4 (1/2),
            (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x j) =
            -(∫ x in Yau.realCenteredCube 4 (1/2), H a j x*psi x)) ∧
        ∀ (k : Fin 4) (eta : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ eta → HasCompactSupport eta →
          tsupport eta ⊆ interior (Yau.realCenteredCube 4 (3/8)) →
          ∀ (i : Fin 4) (h : ℝ), |h| ≤ 1/8 →
          let Q := Yau.realCenteredCube 4 (1/2)
          let U := Q.indicator (sphereChartDerivativeMap d p k (sphereWeakSolution d f))
          let V := fun j ↦ Q.indicator (H k j)
          let A := fun j ↦ Q.indicator (fun x ↦ ∑ a, sphereChartPrincipalDensity d p x a j*H a k x)
          let G := fun j ↦ Q.indicator (Yau.realWeakGradientCommutator (sphereChartPrincipalDensity d p)
            (fun a ↦ sphereChartDerivativeMap d p a (sphereWeakSolution d f)) k j)
          let F := Q.indicator (sphereEigenForcingDerivative d p mu f k)
          let v := Yau.realSquareCutoff eta (Yau.realDifferenceQuotient i h U)
          let P := Yau.realSquareCutoffGradient eta (Yau.realDifferenceQuotient i h U)
            (fun j ↦ Yau.realDifferenceQuotient i h (V j))
          MemLp v 2 volume ∧ (∀ j, MemLp (P j) 2 volume) ∧
          (∀ j, Integrable (fun x ↦ Yau.realDifferenceQuotient i h (A j) x*P j x) ∧
            Integrable (fun x ↦ Yau.realDifferenceQuotient i h (G j) x*P j x)) ∧
          Integrable (fun x ↦ F x*Yau.realDifferenceQuotient i (-h) v x) ∧
          (∑ j, ∫ x, Yau.realDifferenceQuotient i h (A j) x*P j x) =
            -(∫ x, F x*Yau.realDifferenceQuotient i (-h) v x)-
              (∑ j, ∫ x, Yau.realDifferenceQuotient i h (G j) x*P j x) := by
  obtain ⟨C1,hC1,hall⟩ := sphere_eigen_differentiated_equation d p hrho
  refine ⟨C1,hC1,fun mu hmu f heigen ↦ ?_⟩
  obtain ⟨H,hbound,hweak,heq⟩ := hall mu hmu f heigen
  refine ⟨H,hbound,hweak,fun k eta he hc hs i h hh ↦ ?_⟩
  dsimp only
  let Q := Yau.realCenteredCube 4 (1/2)
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 (1/2)
  have hsub : Q ⊆ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num)
  let U : Yau.Jets.Coord → ℝ := Q.indicator (sphereChartDerivativeMap d p k (sphereWeakSolution d f))
  let V : Fin 4 → Yau.Jets.Coord → ℝ := fun j ↦ Q.indicator (H k j)
  let A : Fin 4 → Yau.Jets.Coord → ℝ := fun j ↦ Q.indicator
    (fun x ↦ ∑ a, sphereChartPrincipalDensity d p x a j*H a k x)
  let G : Fin 4 → Yau.Jets.Coord → ℝ := fun j ↦ Q.indicator
    (Yau.realWeakGradientCommutator (sphereChartPrincipalDensity d p)
      (fun a ↦ sphereChartDerivativeMap d p a (sphereWeakSolution d f)) k j)
  let F : Yau.Jets.Coord → ℝ := Q.indicator (sphereEigenForcingDerivative d p mu f k)
  have hU : MemLp U 2 volume := (memLp_indicator_iff_restrict hQ.measurableSet).mpr
    ((Lp.memLp _).mono_measure (Measure.restrict_mono hsub le_rfl))
  have hV (j : Fin 4) : MemLp (V j) 2 volume :=
    (memLp_indicator_iff_restrict hQ.measurableSet).mpr (Lp.memLp (H k j))
  have hA (j : Fin 4) : MemLp (A j) 2 volume := by
    apply (memLp_indicator_iff_restrict hQ.measurableSet).mpr
    apply memLp_finsetSum
    intro a _
    obtain ⟨_,_,hb⟩ := Yau.real_compact_multiplier_bound hQ _
      (sphereChartPrincipalDensity_smooth d p a j).continuous
    exact (hb (H a k) (Lp.memLp _)).1
  have hG (j : Fin 4) : MemLp (G j) 2 volume :=
    (memLp_indicator_iff_restrict hQ.measurableSet).mpr ((heq k).2.1 j j).1
  have hF : MemLp F 2 volume := (memLp_indicator_iff_restrict hQ.measurableSet).mpr (heq k).1
  have hzpair (a b : Yau.Jets.Coord → ℝ) :
      (∫ x, Q.indicator a x*b x) = ∫ x in Q, a x*b x := by
    simp only [← indicator_mul_left,integral_indicator hQ.measurableSet]
  have hW (j : Fin 4) (psi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ psi)
      (hpc : HasCompactSupport psi) (hps : tsupport psi ⊆ Q) :
      (∫ x, U x*Yau.coordPartial psi x j)=-(∫ x, V j x*psi x) := by
    change (∫ x, Q.indicator (fun y ↦ (sphereChartDerivativeMap d p k (sphereWeakSolution d f)) y) x*
      Yau.coordPartial psi x j)=-(∫ x, Q.indicator (fun y ↦ H k j y) x*psi x)
    rw [hzpair,hzpair]
    exact hweak k j psi hp hpc hps
  have hE (psi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ psi)
      (hpc : HasCompactSupport psi) (hps : tsupport psi ⊆ Q) :
      (∑ j, ∫ x, A j x*Yau.coordPartial psi x j) =
        (∫ x, F x*psi x)-(∑ j, ∫ x, G j x*Yau.coordPartial psi x j) := by
    have hx := (heq k).2.2 psi hp hpc hps
    have hsum (j : Fin 4) : (∫ x, A j x*Yau.coordPartial psi x j) = ∑ a, ∫ x in Q,
        sphereChartPrincipalDensity d p x a j*H a k x*Yau.coordPartial psi x j := by
      change (∫ x, Q.indicator (fun y ↦ ∑ a, sphereChartPrincipalDensity d p y a j*H a k y) x*
        Yau.coordPartial psi x j) = _
      rw [hzpair]
      simp only [Finset.sum_mul]
      exact integral_finsetSum Finset.univ (fun a _ ↦ hx.1 a j)
    simp only [hsum]
    rw [Finset.sum_comm]
    change (∑ a, ∑ j, ∫ x in Q, sphereChartPrincipalDensity d p x a j*H a k x*
      Yau.coordPartial psi x j) = (∫ x, Q.indicator (sphereEigenForcingDerivative d p mu f k) x*psi x)-
      (∑ j, ∫ x, Q.indicator (Yau.realWeakGradientCommutator (sphereChartPrincipalDensity d p)
        (fun a ↦ sphereChartDerivativeMap d p a (sphereWeakSolution d f)) k j) x*Yau.coordPartial psi x j)
    simp only [hzpair]
    exact hx.2.2.2
  exact Yau.real_square_cutoff_difference_test A G F hA hG hF (1/2) (3/8) (by norm_num)
    hE U V hU hV hW eta he hc hs i h (by linarith)

end
end Yau.Target

end OAI
