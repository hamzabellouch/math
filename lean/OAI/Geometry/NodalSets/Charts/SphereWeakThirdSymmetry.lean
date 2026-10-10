import OAI.Geometry.NodalSets.Charts.SphereWeakHessianSymmetry
import OAI.Geometry.NodalSets.Elliptic.RealBallCubeContainmentLemmas
import OAI.Geometry.NodalSets.Elliptic.RealWeakThirdSymmetry

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_same_third_derivatives_symmetric (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d)
    (H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))))
    (J : Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4))))
    (hsecond : ∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
      (∫ x in Yau.realCenteredCube 4 (1/2), (sphereChartDerivativeMap d p a z) x*Yau.coordPartial psi x k)=
        -(∫ x in Yau.realCenteredCube 4 (1/2), H a k x*psi x))
    (hthird : ∀ a k i psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Yau.realCenteredCube 4 (1/4) →
      (∫ x in Yau.realCenteredCube 4 (1/4), H a k x*Yau.coordPartial psi x i)=
        -(∫ x in Yau.realCenteredCube 4 (1/4), J a k i x*psi x)) :
    ∀ a k i,
      (J a k i : Yau.Jets.Coord → ℝ) =ᵐ[volume.restrict
        (interior (Yau.realCenteredCube 4 (1/4)))] J a i k ∧
      (J a k i : Yau.Jets.Coord → ℝ) =ᵐ[volume.restrict
        (interior (Yau.realCenteredCube 4 (1/4)))] J k a i := by
  let Q := Yau.realCenteredCube 4 (1/2)
  let Q0 := Yau.realCenteredCube 4 (1/4)
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 (1/2)
  have hQ0 : IsCompact Q0 := Yau.realCenteredCube_isCompact 4 (1/4)
  have hsub : Q0 ⊆ Q := Yau.realCenteredCube_mono (by norm_num)
  have hsub0 : Q ⊆ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num)
  have hfirst (a k : Fin 4) := Yau.real_interior_weak_restrict hQ0 hQ.measurableSet hsub
    (sphereChartDerivativeMap d p a z) (H a k)
    ((Lp.memLp _).mono_measure (Measure.restrict_mono hsub0 le_rfl)) (Lp.memLp _) k (hsecond a k)
  have hs : ∀ a k, (H a k : Yau.Jets.Coord → ℝ) =ᵐ[volume.restrict Q0] H k a := by
    intro a k
    have hsym := sphere_chart_weak_hessian_symmetric d p z H hsecond a k
    exact ae_mono (Measure.restrict_mono (Yau.realCenteredCube_subset_interior (by norm_num)) le_rfl) hsym
  intro a k i
  exact ⟨Yau.real_weak_third_last_symmetry hQ0 (fun a ↦ sphereChartDerivativeMap d p a z)
    (fun a k ↦ H a k) (fun a k i ↦ J a k i) (fun a k i ↦ Lp.memLp _)
    (fun a k psi hp hc hs ↦ ((hfirst a k).2.2 psi hp hc hs).2.2) hthird a k i,
    Yau.real_weak_third_first_symmetry hQ0 (fun a k ↦ H a k) (fun a k i ↦ J a k i)
      (fun a k i ↦ Lp.memLp _) hs hthird a k i⟩

end
end Yau.Target

end OAI
