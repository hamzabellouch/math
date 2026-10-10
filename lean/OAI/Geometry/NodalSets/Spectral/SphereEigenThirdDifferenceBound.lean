import OAI.Geometry.NodalSets.Charts.SphereInteriorDifferenceBound
import OAI.Geometry.NodalSets.Charts.SphereThirdFluxSymmetry
import OAI.Geometry.NodalSets.Spectral.SphereEigenSecondEquation
import OAI.Geometry.NodalSets.Spectral.SphereEigenSecondForcingBound

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_same_third_difference_bound (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) (C2 C3 : ℝ) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) :
    ∃ C > 0, ∀
    (f : SphereWeightedL2 d)
    (_ : sphereL2Resolvent d f=mu • f)
    (H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))))
    (J : Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4))))
    (_ : ∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
      (∫ x in Yau.realCenteredCube 4 (1/2),
        (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x k) =
        -(∫ x in Yau.realCenteredCube 4 (1/2), H a k x*psi x))
    (_ : ∀ a k l psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Yau.realCenteredCube 4 (1/4) →
      (∫ x in Yau.realCenteredCube 4 (1/4), H a k x*Yau.coordPartial psi x l) =
        -(∫ x in Yau.realCenteredCube 4 (1/4), J a k l x*psi x)),
      (∑ a, ∑ k, ‖H a k‖^2) ≤ C2*(‖f‖^2+‖sphereWeakSolution d f‖^2) →
      (∑ a, ∑ k, ∑ i, ‖J a k i‖^2) ≤ C3*(‖f‖^2+‖sphereWeakSolution d f‖^2) →
      ∀ (k l i : Fin 4) (h : ℝ), |h| ≤ 1/64 →
        (∀ a, MemLp (Yau.realDifferenceQuotient i h (J k l a)) 2
          (volume.restrict (Yau.realCenteredCube 4 (1/8)))) ∧
        (∑ a, ∫ x in Yau.realCenteredCube 4 (1/8),
          (Yau.realDifferenceQuotient i h (J k l a) x)^2) ≤ C*(‖f‖^2+‖sphereWeakSolution d f‖^2) := by
  obtain ⟨B,hB,hgain⟩ := sphere_interior_difference_bound d p (1/4) (1/8) (by norm_num) (by norm_num)
  obtain ⟨A,hA,hjet⟩ := sphere_same_interior_jet_bound d p C2 C3 hC2 hC3
  obtain ⟨M,hM,hforce⟩ := sphere_same_second_forcing_bound d p hrho mu C2 C3 hC2 hC3
  refine ⟨B*(A+M),by positivity,?_⟩
  intro f heigen H J hsecond hthird hH hJ k l i h hh
  let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hAM : 0 ≤ (A+M)*E := by positivity
  have hAE : A*E ≤ (A+M)*E := mul_le_mul_of_nonneg_right (by linarith) hE
  have hME : M*E ≤ (A+M)*E := mul_le_mul_of_nonneg_right (by linarith) hE
  have hdata := sphere_same_second_differentiated_equation d p hrho mu hmu f heigen H J hsecond hthird k l
  have hsym := sphere_same_third_flux_symmetric d p (sphereWeakSolution d f) H J hsecond hthird
  have hjets := hjet f H J hH hJ
  have hforcing := hforce f H J hH hJ
  have hg := hgain (H k l) (fun a ↦ J k l a) (fun a ↦ J a k l) _ _ _
    (hjets.2.2.1 k l).1 (fun a ↦ Lp.memLp _) (fun a ↦ Lp.memLp _)
    (fun j ↦ (hdata.2.2 j 0).1) (fun j i ↦ (hdata.2.2 j i).2.1) hdata.1
    (fun a ↦ hsym a k l) (hthird k l)
    (fun j i psi hp hc hs ↦ ((hdata.2.2 j i).2.2 psi hp hc hs).2.2)
    (fun psi hp hc hs ↦ (hdata.2.1 psi hp hc hs).2.2.2)
    ((A+M)*E) hAM ((hjets.2.2.1 k l).2.trans hAE)
    (fun a ↦ (hjets.2.2.2 k l a).2.trans hAE)
    ((hforcing k l 0 0).1.2.trans hME)
    (fun j ↦ (hforcing k l j 0).2.1.2.trans hME)
    (fun j i ↦ (hforcing k l j i).2.2.2.trans hME) i h (by norm_num; exact hh)
  exact ⟨hg.1,by simpa only [E,mul_assoc] using hg.2⟩

end
end Yau.Target

end OAI
