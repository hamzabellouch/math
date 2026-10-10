import OAI.Geometry.NodalSets.SmoothLimit.SphereFiniteWeakJetIteration
import OAI.Geometry.NodalSets.Spectral.SphereEigenInitialWeakJet

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_eigen_all_finite_weak_jets (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) (m : ℕ) :
    ∃ K > 0, ∀ (f : SphereWeightedL2 d), sphereL2Resolvent d f=mu • f →
      ∃ U : List (Fin 4) → Yau.Jets.Coord → ℝ,
        let Q := Yau.realCenteredCube 4 (1/16)
        let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
        U []=(fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)) ∧
        (∀ a, U [a]=(sphereChartDerivativeMap d p a (sphereWeakSolution d f) : Yau.Jets.Coord → ℝ)) ∧
        (∀ es, es.length ≤ m+4 → MemLp (U es) 2 (volume.restrict Q) ∧
          (∫ x in Q, (U es x)^2) ≤ K*E) ∧
        (∀ es, es.length ≤ m+3 → ∀ i psi,
          ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
          IntegrableOn (fun x ↦ U es x*Yau.coordPartial psi x i) Q ∧
          IntegrableOn (fun x ↦ U (i::es) x*psi x) Q ∧
          (∫ x in Q, U es x*Yau.coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) ∧
        ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
          (∑ a, ∑ j, ∫ x in Q, sphereChartPrincipalDensity d p x a j*U [a] x*Yau.coordPartial psi x j) =
            ∫ x in Q, sphereEigenForcingCoefficient d p mu x*U [] x*psi x := by
  let B := sphereEigenForcingCoefficient d p mu
  have hB : ContDiff ℝ ∞ B := contDiff_const.mul (roundCoordDensity_smooth.mul hrho)
  obtain ⟨A,hA,hinitial⟩ := sphere_eigen_initial_weak_jet d p hrho mu hmu
  obtain ⟨C,hC,hiter⟩ := sphere_finite_weak_jet_iteration d p B hB m
  refine ⟨C*A,mul_pos hC hA,fun f heigen ↦ ?_⟩
  obtain ⟨V,hzero,hone,hV,hvw,hve⟩ := hinitial f heigen
  let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  obtain ⟨U,hlo,hU,huw,hue⟩ := hiter V (fun es hh ↦ (hV es hh).1) hvw hve
    (A*E) (mul_nonneg hA.le hE) (fun es hh ↦ (hV es hh).2)
  let Q := Yau.realCenteredCube 4 (1/16)
  let L := Yau.realCenteredCube 4 (Yau.realWeakJetRadius m)
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 (1/16)
  have hL : IsCompact L := Yau.realCenteredCube_isCompact 4 (Yau.realWeakJetRadius m)
  have hsub : Q ⊆ L := Yau.realCenteredCube_mono (Yau.realWeakJetRadius_lower m).le
  refine ⟨U,(hlo [] (by simp)).trans hzero,fun a ↦ (hlo [a] (by simp)).trans (hone a),?_,?_,?_⟩
  · intro es hh
    have hb := hU es hh
    refine ⟨hb.1.mono_measure (Measure.restrict_mono hsub le_rfl),?_⟩
    have hm := integral_mono_measure (Measure.restrict_mono hsub le_rfl)
      (Filter.Eventually.of_forall (fun x ↦ sq_nonneg (U es x))) hb.1.integrable_sq
    simpa only [mul_assoc] using hm.trans hb.2
  · intro es hh i psi hp hc hs
    exact ((Yau.real_interior_weak_restrict hQ hL.measurableSet hsub (U es) (U (i::es))
      (hU es (by omega)).1 (hU (i::es) (by simp only [List.length_cons]; omega)).1 i
      (huw es hh i)).2.2 psi hp hc hs)
  · exact Yau.real_weak_equation_restrict hL.measurableSet hsub
      (sphereChartPrincipalDensity d p) (fun a ↦ U [a]) (fun x ↦ B x*U [] x) hue

end
end Yau.Target

end OAI
