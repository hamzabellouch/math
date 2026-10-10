import OAI.Geometry.NodalSets.Charts.SphereHessianDifferenceCoercivity
import OAI.Geometry.NodalSets.Elliptic.RealDivergenceEnergyAE
import OAI.Geometry.NodalSets.Elliptic.RealLocalWeakDifferenceBound
import OAI.Geometry.NodalSets.Elliptic.RealLocalizedDifferenceIdentity
import OAI.Geometry.NodalSets.Elliptic.RealSquareDifferenceEnergy
import OAI.Geometry.NodalSets.Spectral.SphereEigenSquareDifferenceTest

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphere_eigen_hessian_localized_energy (d : SphereEnergyData) (p : Base)
    (hrho : ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) :
    ∃ C1 > 0, ∃ m > 0, ∃ K > 0,
      ∀ (mu : ℝ), mu ≠ 0 → ∀ (f : SphereWeightedL2 d), sphereL2Resolvent d f=mu • f →
      ∃ H : Fin 4 → Fin 4 → Lp ℝ 2 (volume.restrict (Yau.realCenteredCube 4 (1/2))),
        (∑ a, ∑ j, ‖H a j‖^2) ≤ C1*(‖f‖^2+‖sphereWeakSolution d f‖^2) ∧
        (∀ a j psi, ContDiff ℝ ∞ psi → HasCompactSupport psi →
          tsupport psi ⊆ Yau.realCenteredCube 4 (1/2) →
          (∫ x in Yau.realCenteredCube 4 (1/2),
            (sphereChartDerivativeMap d p a (sphereWeakSolution d f)) x*Yau.coordPartial psi x j) =
            -(∫ x in Yau.realCenteredCube 4 (1/2), H a j x*psi x)) ∧
        ∀ (k : Fin 4) (eta chi : Yau.Jets.Coord → ℝ),
          ContDiff ℝ ∞ eta → HasCompactSupport eta → (∀ x, |eta x| ≤ 1) →
          tsupport eta ⊆ interior (Yau.realCenteredCube 4 (3/8)) →
          ContDiff ℝ ∞ chi → tsupport chi ⊆ Yau.realCenteredCube 4 (1/2) →
          ∀ (i : Fin 4) (h : ℝ), |h| ≤ 1/32 →
          (∀ x ∈ tsupport eta, x ∈ Yau.realCenteredCube 4 (1/2) ∧
            x+Pi.single i h ∈ Yau.realCenteredCube 4 (1/2) ∧ chi x=1 ∧ chi (x+Pi.single i h)=1) →
          let Q := Yau.realCenteredCube 4 (1/2)
          let U := Q.indicator (sphereChartDerivativeMap d p k (sphereWeakSolution d f))
          let V := fun a ↦ Q.indicator (H k a)
          let G := Yau.realWeakGradientCommutator (sphereChartPrincipalDensity d p)
            (fun a ↦ sphereChartDerivativeMap d p a (sphereWeakSolution d f)) k
          let DG := Yau.realWeakGradientCommutatorDerivative (sphereChartPrincipalDensity d p)
            (fun a ↦ sphereChartDerivativeMap d p a (sphereWeakSolution d f)) (fun a j ↦ H a j) k
          let F := Q.indicator (sphereEigenForcingDerivative d p mu f k)
          let q := Yau.realDifferenceQuotient i h U
          let T := fun a x ↦ eta x*Yau.realDifferenceQuotient i h (V a) x
          let W := fun a x ↦ eta x*V a x
          let R := fun a x ↦ Yau.coordPartial eta x a*q x
          (∀ a, MemLp (T a) 2 volume ∧ MemLp (W a) 2 volume ∧ MemLp (R a) 2 volume) ∧
          (∑ a, ∫ x, (T a x)^2) ≤ (4/m)*
            ((16/m)*((∫ x, (F x)^2)+
                (∑ j, ∫ x, (chi x*DG j i x+Yau.coordPartial chi x i*G j x)^2))+
              K*(∑ a, ∫ x, (W a x)^2)+(K+m)*(∑ a, ∫ x, (R a x)^2)) := by
  obtain ⟨C1,hC1,hall⟩ := sphere_eigen_square_difference_test d p hrho
  obtain ⟨m,hm,K,hK,hcoer⟩ := sphere_hessian_difference_coercivity d p
  refine ⟨C1,hC1,m,hm,K,hK,fun mu hmu f heigen ↦ ?_⟩
  obtain ⟨H,hbound,hweak,htests⟩ := hall mu hmu f heigen
  refine ⟨H,hbound,hweak,fun k eta chi he hc heb hs hchi hchis i h hh hend ↦ ?_⟩
  dsimp only
  let Q := Yau.realCenteredCube 4 (1/2)
  have hQ : IsCompact Q := Yau.realCenteredCube_isCompact 4 (1/2)
  have hsub : Q ⊆ realFinCube 4 := Yau.realCenteredCube_mono (by norm_num)
  let U := Q.indicator (sphereChartDerivativeMap d p k (sphereWeakSolution d f))
  let V := fun a ↦ Q.indicator (H k a)
  let A := fun j ↦ Q.indicator (fun x ↦ ∑ a, sphereChartPrincipalDensity d p x a j*H a k x)
  let G := Yau.realWeakGradientCommutator (sphereChartPrincipalDensity d p)
    (fun a ↦ sphereChartDerivativeMap d p a (sphereWeakSolution d f)) k
  let DG := Yau.realWeakGradientCommutatorDerivative (sphereChartPrincipalDensity d p)
    (fun a ↦ sphereChartDerivativeMap d p a (sphereWeakSolution d f)) (fun a j ↦ H a j) k
  let F := Q.indicator (sphereEigenForcingDerivative d p mu f k)
  let q := Yau.realDifferenceQuotient i h U
  let T := fun a x ↦ eta x*Yau.realDifferenceQuotient i h (V a) x
  let W := fun a x ↦ eta x*V a x
  let R := fun a x ↦ Yau.coordPartial eta x a*q x
  let P := Yau.realSquareCutoffGradient eta q (fun a ↦ Yau.realDifferenceQuotient i h (V a))
  let v := Yau.realSquareCutoff eta q
  let b := Yau.realDifferenceQuotient i (-h) v
  let L := fun j ↦ Yau.realDifferenceQuotient i h (fun x ↦ chi x*G j x)
  have hU : MemLp U 2 volume := (memLp_indicator_iff_restrict hQ.measurableSet).mpr
    ((Lp.memLp _).mono_measure (Measure.restrict_mono hsub le_rfl))
  have hV (j : Fin 4) : MemLp (V j) 2 volume :=
    (memLp_indicator_iff_restrict hQ.measurableSet).mpr (Lp.memLp (H k j))
  have hW (j : Fin 4) : MemLp (W j) 2 volume :=
    Yau.real_compact_localL2_product hc eta (V j) he.continuous Subset.rfl ((hV j).restrict _)
  have hzpair (a b : Yau.Jets.Coord → ℝ) :
      (∫ x, Q.indicator a x*b x) = ∫ x in Q, a x*b x := by
    simp only [← indicator_mul_left,integral_indicator hQ.measurableSet]
  have hUW (j : Fin 4) (psi : Yau.Jets.Coord → ℝ) (hp : ContDiff ℝ ∞ psi)
      (hpc : HasCompactSupport psi) (hps : tsupport psi ⊆ Q) :
      (∫ x, U x*Yau.coordPartial psi x j)=-(∫ x, V j x*psi x) := by
    change (∫ x, Q.indicator (fun y ↦ (sphereChartDerivativeMap d p k (sphereWeakSolution d f)) y) x*
      Yau.coordPartial psi x j)=-(∫ x, Q.indicator (fun y ↦ H k j y) x*psi x)
    rw [hzpair,hzpair]
    exact hweak k j psi hp hpc hps
  have htest := htests k eta he hc hs i h (by linarith)
  have henergy := Yau.real_square_difference_test_energy eta U V hU hV (1/2) (3/8)
    (by norm_num) he hc heb (hs.trans interior_subset) hUW i h (by linarith)
  have hcomm (j : Fin 4) := Yau.real_weak_gradient_commutator_H1 hQ
    (sphereChartPrincipalDensity d p)
    (fun a ↦ sphereChartDerivativeMap d p a (sphereWeakSolution d f)) (fun a l ↦ H a l)
    (sphereChartPrincipalDensity_smooth d p)
    (fun a ↦ (Lp.memLp _).mono_measure (Measure.restrict_mono hsub le_rfl))
    (fun a l ↦ Lp.memLp (H a l)) hweak k j i
  have hlocal (j : Fin 4) := Yau.real_local_weak_cutoff_difference_bound hQ (G j) (DG j i) chi
    (hcomm j).1 (hcomm j).2.1 hchi hchis i
    (fun psi hp hpc hps ↦ ((hcomm j).2.2 psi hp hpc hps).2.2) h
  have hF : MemLp F 2 volume := (memLp_indicator_iff_restrict hQ.measurableSet).mpr
    ((sphere_eigen_resolvent_forcing_H1 d p hrho mu hmu f heigen k).2.1.mono_measure
      (Measure.restrict_mono hsub le_rfl))
  have hsym := fun a l ↦ sphere_chart_weak_hessian_symmetric d p (sphereWeakSolution d f) H hweak a l
  have hlow := hcoer (fun a l ↦ H a l) hsym k i h hh eta q (hs.trans interior_subset)
  have heq : (∑ j, ∫ x, Yau.realDifferenceQuotient i h (A j) x*P j x) =
      -(∫ x, F x*b x)-(∑ j, ∫ x, L j x*P j x) := by
    have hl (j : Fin 4) := Yau.real_square_gradient_difference_pairing_localize Q (G j) chi eta q
      (fun a ↦ Yau.realDifferenceQuotient i h (V a)) i j h hend
    have hlsum : (∑ j, ∫ x, Yau.realDifferenceQuotient i h (Q.indicator (G j)) x*P j x) =
        (∑ j, ∫ x, L j x*P j x) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun v : Yau.Jets.Coord → ℝ ↦ ∫ x, v x) (hl j)
    rw [← hlsum]
    exact htest.2.2.2.2
  have habs := Yau.real_divergence_difference_energy_absorption_ae volume m K hm
    T W R (fun j ↦ Yau.realDifferenceQuotient i h (A j)) P L F b
    (fun j ↦ (henergy.1 j).1) hW (fun j ↦ (henergy.1 j).2.1)
    (fun j ↦ (henergy.1 j).2.2) (fun j ↦ (hlocal j).1)
    (fun j ↦ (htest.2.2.1 j).1) hF henergy.2.1 hlow henergy.2.2.2 henergy.2.2.1 heq
  refine ⟨fun j ↦ ⟨(henergy.1 j).1,hW j,(henergy.1 j).2.1⟩,habs.trans ?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ (hlocal j).2)
  gcongr

end
end Yau.Target

end OAI
