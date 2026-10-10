import OAI.Geometry.NodalSets.Charts.SphereInteriorChartWeakDerivative
import OAI.Geometry.NodalSets.Charts.SphereInteriorJetBound
import OAI.Geometry.NodalSets.Elliptic.RealInteriorWeakRestrictionLemmas
import OAI.Geometry.NodalSets.Spectral.SphereEigenInteriorH4
import OAI.Geometry.NodalSets.Spectral.SphereInteriorResolventEquation

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
open scoped ContDiff
noncomputable section

theorem sphere_eigen_initial_weak_jet (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (mu : ℝ) (hmu : mu ≠ 0) :
    ∃ K > 0, ∀ (f : SphereWeightedL2 d), sphereL2Resolvent d f=mu • f →
      ∃ U : List (Fin 4) → Yau.Jets.Coord → ℝ,
        let Q := Yau.realCenteredCube 4 (1/8)
        let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
        U []=(fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)) ∧
        (∀ a, U [a]=(sphereChartDerivativeMap d p a (sphereWeakSolution d f) : Yau.Jets.Coord → ℝ)) ∧
        (∀ es, es.length ≤ 4 → MemLp (U es) 2 (volume.restrict Q) ∧
          (∫ x in Q, (U es x)^2) ≤ K*E) ∧
        (∀ es, es.length ≤ 3 → ∀ i psi,
          ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
          (∫ x in Q, U es x*Yau.coordPartial psi x i)=-(∫ x in Q, U (i::es) x*psi x)) ∧
        ∀ psi, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ Q →
          (∑ a, ∑ j, ∫ x in Q, sphereChartPrincipalDensity d p x a j*U [a] x*Yau.coordPartial psi x j) =
            ∫ x in Q, sphereEigenForcingCoefficient d p mu x*U [] x*psi x := by
  obtain ⟨C2,hC2,C3,hC3,C4,hC4,hfour⟩ := sphere_eigen_interior_fourth_weak_derivatives d p hrho mu hmu
  obtain ⟨A,hA,hjet⟩ := sphere_same_interior_jet_bound d p C2 C3 hC2.le hC3.le
  refine ⟨A+C4,by positivity,fun f heigen ↦ ?_⟩
  obtain ⟨H,J,L,hH,hsecond,hJ,hthird,hL,hfourth⟩ := hfour f heigen
  let Q := Yau.realCenteredCube 4 (1/8)
  let E := ‖f‖^2+‖sphereWeakSolution d f‖^2
  let w := fun x ↦ (sphereL2Resolvent d f) (sphereChartCoordMap p x)
  let U := fun a ↦ (sphereChartDerivativeMap d p a (sphereWeakSolution d f) : Yau.Jets.Coord → ℝ)
  let V := Yau.realWeakFourJet w U (fun a k ↦ H a k) (fun a k l ↦ J a k l) (fun a k l i ↦ L a k l i)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 (1/8)
  have hsub : Q ⊆ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num)
  have hsub2 : Q ⊆ Yau.realCenteredCube 4 (1/2) := Yau.realCenteredCube_mono (by norm_num)
  have hsub3 : Q ⊆ Yau.realCenteredCube 4 (1/4) := Yau.realCenteredCube_mono (by norm_num)
  obtain ⟨hbw,hbU,hbH,hbJ⟩ := hjet f H J hH hJ
  have hres (v : Yau.Jets.Coord → ℝ)
      (hv : MemLp v 2 (volume.restrict (Yau.realCenteredCube 4 (1/4))) ∧
        (∫ x in Yau.realCenteredCube 4 (1/4), (v x)^2) ≤ A*E) :
      MemLp v 2 (volume.restrict Q) ∧ (∫ x in Q, (v x)^2) ≤ (A+C4)*E := by
    refine ⟨hv.1.mono_measure (Measure.restrict_mono hsub3 le_rfl),?_⟩
    have hm := integral_mono_measure (Measure.restrict_mono hsub3 le_rfl)
      (Filter.Eventually.of_forall (fun x ↦ sq_nonneg (v x))) hv.1.integrable_sq
    exact hm.trans (hv.2.trans (mul_le_mul_of_nonneg_right (by linarith only [hC4]) hE))
  have hbL (a k l i : Fin 4) : MemLp (L a k l i) 2 (volume.restrict Q) ∧
      (∫ x in Q, (L a k l i x)^2) ≤ (A+C4)*E := by
    have hb := Yau.real_Lp_restricted_square_le le_rfl (L a k l i)
    have h1 := Finset.single_le_sum (f := fun b ↦ ‖L a k l b‖^2)
      (fun b _ ↦ sq_nonneg _) (Finset.mem_univ i)
    have h2 := Finset.single_le_sum (f := fun b ↦ ∑ c, ‖L a k b c‖^2)
      (fun b _ ↦ Finset.sum_nonneg (fun c _ ↦ sq_nonneg _)) (Finset.mem_univ l)
    have h3 := Finset.single_le_sum (f := fun b ↦ ∑ c, ∑ e, ‖L a b c e‖^2)
      (fun b _ ↦ Finset.sum_nonneg (fun c _ ↦ Finset.sum_nonneg (fun e _ ↦ sq_nonneg _))) (Finset.mem_univ k)
    have h4 := Finset.single_le_sum (f := fun b ↦ ∑ c, ∑ e, ∑ t, ‖L b c e t‖^2)
      (fun b _ ↦ Finset.sum_nonneg (fun c _ ↦ Finset.sum_nonneg
        (fun e _ ↦ Finset.sum_nonneg (fun t _ ↦ sq_nonneg _)))) (Finset.mem_univ a)
    exact ⟨hb.1,hb.2.trans (h1.trans (h2.trans (h3.trans (h4.trans
      (hL.trans (mul_le_mul_of_nonneg_right (by linarith only [hA]) hE))))))⟩
  have hp1 (a : Fin 4) := sphere_resolvent_interior_first_pairing d p f hQ hsub a
  have hp2 (a k : Fin 4) := Yau.real_interior_weak_restrict hQ
    (Yau.realCenteredCube_isCompact 4 (1/2)).measurableSet hsub2 (U a) (H a k)
    ((Lp.memLp _).mono_measure (Measure.restrict_mono
      (show Yau.realCenteredCube 4 (1/2) ⊆ realFinCube 4 from Yau.realCenteredCube_mono (by norm_num)) le_rfl))
    (Lp.memLp _) k (hsecond a k)
  have hp3 (a k l : Fin 4) := Yau.real_interior_weak_restrict hQ
    (Yau.realCenteredCube_isCompact 4 (1/4)).measurableSet hsub3 (H a k) (J a k l)
    (hbH a k).1 (Lp.memLp _) l (fun psi hp hc hs ↦ (hthird a k l psi hp hc hs).2.2)
  refine ⟨V,rfl,fun _ ↦ rfl,?_,?_,?_⟩
  · exact Yau.real_weak_four_jet_bounds w U _ _ _ ((A+C4)*E) (hres w hbw)
      (fun a ↦ hres (U a) (hbU a)) (fun a k ↦ hres _ (hbH a k))
      (fun a k l ↦ hres _ (hbJ a k l)) hbL
  · exact Yau.real_weak_four_jet_pairings w U _ _ _
      (fun i psi hp hc hs ↦ ((hp1 i).2.2 psi hp hc hs).2.2)
      (fun a i psi hp hc hs ↦ ((hp2 a i).2.2 psi hp hc hs).2.2)
      (fun a k i psi hp hc hs ↦ ((hp3 a k i).2.2 psi hp hc hs).2.2)
      (fun a k l i psi hp hc hs ↦ (hfourth a k l i psi hp hc hs).2.2)
  · intro psi hp hc hs
    have h := (sphere_resolvent_interior_equation d f p hQ hsub psi hp hc hs).2.2
    apply h.trans
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (sphere_eigen_resolvent_forcing_ae d p mu hmu f heigen)] with x hx
    exact congrArg (fun t : ℝ ↦ t*psi x) hx

end
end Yau.Target

end OAI
