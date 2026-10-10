import OAI.Geometry.NodalSets.Charts.SphereInteriorChartWeakDerivative
import OAI.Geometry.NodalSets.Elliptic.RealTwiceDifferentiatedEquation
import OAI.Geometry.NodalSets.Spectral.SphereEigenInteriorH3
import OAI.Geometry.NodalSets.Spectral.SphereInteriorResolventEquation

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_same_second_differentiated_equation (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) (f : SphereWeightedL2 d)
    (heigen : sphereL2Resolvent d f=mu • f)
    (H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))))
    (J : Fin 4 → Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/4))))
    (hsecond : ∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
      (∫ x in Yau.realCenteredCube 4 (1/2),
        (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x k) =
        -(∫ x in Yau.realCenteredCube 4 (1/2), H a k x*psi x))
    (hthird : ∀ a k l psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Yau.realCenteredCube 4 (1/4) →
      (∫ x in Yau.realCenteredCube 4 (1/4), H a k x*Yau.coordPartial psi x l) =
        -(∫ x in Yau.realCenteredCube 4 (1/4), J a k l x*psi x)) :
    let Q := Yau.realCenteredCube 4 (1/4)
    let C := sphereChartPrincipalDensity d p
    let B := sphereEigenForcingCoefficient d p mu
    let w := fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)
    let U := fun a ↦ (sphereChartDerivativeMap d p a (sphereWeakSolution d f) : Yau.Jets.Coord → ℝ)
    ∀ k l,
      MemLp (Yau.realSecondScalarForcing B w U (fun a b ↦ H a b) k l) 2 (volume.restrict Q) ∧
      (∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
        (∀ a j, IntegrableOn (fun x ↦ C x a j*J a k l x*Yau.coordPartial psi x j) Q) ∧
        IntegrableOn (fun x ↦ Yau.realSecondScalarForcing B w U (fun a b ↦ H a b) k l x*psi x) Q ∧
        (∀ j, IntegrableOn (fun x ↦ Yau.realSecondCommutator C U (fun a b ↦ H a b) k l j x*
          Yau.coordPartial psi x j) Q) ∧
        (∑ a, ∑ j, ∫ x in Q, C x a j*J a k l x*Yau.coordPartial psi x j) =
          (∫ x in Q, Yau.realSecondScalarForcing B w U (fun a b ↦ H a b) k l x*psi x)-
            ∑ j, ∫ x in Q, Yau.realSecondCommutator C U (fun a b ↦ H a b) k l j x*
              Yau.coordPartial psi x j) ∧
      ∀ j i,
        MemLp (Yau.realSecondCommutator C U (fun a b ↦ H a b) k l j) 2 (volume.restrict Q) ∧
        MemLp (Yau.realSecondCommutatorDerivative C U (fun a b ↦ H a b)
          (fun a b c ↦ J a b c) k l j i) 2 (volume.restrict Q) ∧
        ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
          IntegrableOn (fun x ↦ Yau.realSecondCommutator C U (fun a b ↦ H a b) k l j x*
            Yau.coordPartial psi x i) Q ∧
          IntegrableOn (fun x ↦ Yau.realSecondCommutatorDerivative C U (fun a b ↦ H a b)
            (fun a b c ↦ J a b c) k l j i x*psi x) Q ∧
          (∫ x in Q, Yau.realSecondCommutator C U (fun a b ↦ H a b) k l j x*Yau.coordPartial psi x i) =
            -(∫ x in Q, Yau.realSecondCommutatorDerivative C U (fun a b ↦ H a b)
              (fun a b c ↦ J a b c) k l j i x*psi x) := by
  let Q := Yau.realCenteredCube 4 (1/4)
  let C := sphereChartPrincipalDensity d p
  let B := sphereEigenForcingCoefficient d p mu
  let w := fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)
  let U := fun a ↦ (sphereChartDerivativeMap d p a (sphereWeakSolution d f) : Yau.Jets.Coord → ℝ)
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 (1/4)
  have hsub : Q ⊆ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num)
  have hsub2 : Q ⊆ Yau.realCenteredCube 4 (1/2) := Yau.realCenteredCube_mono (by norm_num)
  have hsub1 : Yau.realCenteredCube 4 (1/2) ⊆ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num)
  have hfirst (a : Fin 4) := sphere_resolvent_interior_first_pairing d p f hQ hsub a
  have hw : MemLp w 2 (volume.restrict Q) := (hfirst 0).1
  have hU (a : Fin 4) : MemLp (U a) 2 (volume.restrict Q) := (hfirst a).2.1
  have hH (a k : Fin 4) : MemLp (H a k) 2 (volume.restrict Q) :=
    (Lp.memLp _).mono_measure (Measure.restrict_mono hsub2 le_rfl)
  have hsec (a k : Fin 4) := Yau.real_interior_weak_restrict hQ
    (Yau.realCenteredCube_isCompact 4 (1/2)).measurableSet hsub2 (U a) (H a k)
    ((Lp.memLp _).mono_measure (Measure.restrict_mono hsub1 le_rfl)) (Lp.memLp _) k (hsecond a k)
  have hf : ∀ a psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, w x*Yau.coordPartial psi x a)=-(∫ x in Q, U a x*psi x) :=
    fun a psi hp hc hs ↦ ((hfirst a).2.2 psi hp hc hs).2.2
  have hh : ∀ a k psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∫ x in Q, U a x*Yau.coordPartial psi x k)=-(∫ x in Q, H a k x*psi x) :=
    fun a k psi hp hc hs ↦ ((hsec a k).2.2 psi hp hc hs).2.2
  have hB : ContDiff ℝ ∞ B := contDiff_const.mul (roundCoordDensity_smooth.mul hrho)
  have heq : ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
      (∑ a, ∑ j, ∫ x in Q, C x a j*U a x*Yau.coordPartial psi x j)=∫ x in Q, B x*w x*psi x := by
    intro psi hp hc hs
    have h := (sphere_resolvent_interior_equation d f p hQ hsub psi hp hc hs).2.2
    apply h.trans
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (sphere_eigen_resolvent_forcing_ae d p mu hmu f heigen)] with x hx
    exact congrArg (fun t : ℝ ↦ t*psi x) hx
  dsimp only
  intro k l
  refine ⟨(Yau.real_weak_second_scalar_forcing hQ B w U (fun a b ↦ H a b)
    hB hw hU hH hf hh k l).2.1,?_,?_⟩
  · exact fun psi hp hc hs ↦ Yau.real_twice_differentiated_equation hQ C B w U
      (fun a b ↦ H a b) (fun a b c ↦ J a b c) (sphereChartPrincipalDensity_smooth d p)
      hB hw hU hH (fun a b c ↦ Lp.memLp _) hf hh hthird heq k l psi hp hc hs
  · exact fun j i ↦ Yau.real_weak_second_commutator_H1 hQ C U (fun a b ↦ H a b)
      (fun a b c ↦ J a b c) (sphereChartPrincipalDensity_smooth d p)
      hU hH (fun a b c ↦ Lp.memLp _) hh hthird k l j i

end
end Yau.Target

end OAI
