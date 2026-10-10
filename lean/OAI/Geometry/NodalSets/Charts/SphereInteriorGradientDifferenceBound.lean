import OAI.Geometry.NodalSets.Charts.SphereDifferenceTestLiteral
import OAI.Geometry.NodalSets.Charts.SphereSquareDifferenceTestBound
import OAI.Geometry.NodalSets.Charts.SphereWeightedGradientBound
import OAI.Geometry.NodalSets.Elliptic.RealDifferenceEnergyBound

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section
local instance sphereInteriorGradientDifferenceBoundMeasurable : MeasurableSpace Base := borel Base
local instance sphereInteriorGradientDifferenceBoundBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_resolvent_interior_gradient_difference_bound (d : SphereEnergyData) (p : Base) :
    ∃ C0 > 0, ∀ (f : SphereWeightedL2 d) (i : Fin 4) (h : ℝ), |h| ≤ 1/8 →
      (∀ j : Fin 4, MemLp
        (Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j (sphereWeakSolution d f))) 2
        (volume.restrict (Yau.realCenteredCube 4 (1/2)))) ∧
      (∑ j : Fin 4, ∫ x in Yau.realCenteredCube 4 (1/2),
        (Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j (sphereWeakSolution d f)) x)^2)
        ≤ C0*(‖f‖^2+‖sphereWeakSolution d f‖^2) := by
  obtain ⟨eta,theta,he,ht,hec,htc,hes,hts,heb,htb,ht1,he1⟩ := Yau.real_interior_difference_cutoffs
  have hes' : tsupport eta ⊆ realFinCube 4 := hes
  have hts' : tsupport theta ⊆ realFinCube 4 := hts.trans (Yau.realCenteredCube_mono (by norm_num))
  obtain ⟨m,hm,K,hK,hcoer⟩ := sphere_difference_pointwise_coercivity d p
  obtain ⟨CV,hCV,hVb⟩ := sphere_weighted_gradient_bound d p
  obtain ⟨CQ,hCQ,hQb⟩ := sphere_cutoff_uniform_H1_bound d p eta he hes'
  obtain ⟨CR,hCR,hRb⟩ := Yau.real_compact_gradient_multiplier_bound theta ht htc
  obtain ⟨CF,hCF,hFb⟩ := sphere_chart_forcingZero_uniform_bound d p
  let C0 : ℝ := (4/m)*((8/m)*CF+K*CV+(K+m)*(CR*CQ))
  refine ⟨C0,by dsimp [C0]; positivity,fun f i h hh ↦ ?_⟩
  let z := sphereWeakSolution d f
  let v := fun x ↦ eta x*(sphereEnergyL2Map d z) (sphereChartCoordMap p x)
  let q := Yau.realDifferenceQuotient i h v
  let T := fun j x ↦ theta x*Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z) x
  let V := fun j x ↦ theta x*(sphereChartDerivativeMap d p j z) x
  let R := fun j x ↦ Yau.coordPartial theta x j*q x
  let P := fun j x ↦ theta x*(T j x+2*R j x)
  let beta := fun x ↦ theta x*theta x
  let phi := fun x ↦ beta x*q x
  let b := Yau.realDifferenceQuotient i (-h) phi
  let D := fun j ↦ Yau.realDifferenceQuotient i h (sphereChartFluxZero d p z j)
  let F := sphereChartForcingZero d p f
  have hlocal := he1 i h hh
  have htest := sphere_square_difference_test_bound d p z eta theta he ht hes' hts' htb i h hlocal
  change (∀ j, MemLp (T j) 2 volume ∧ MemLp (R j) 2 volume ∧ MemLp (P j) 2 volume) ∧
    MemLp b 2 volume ∧ (∫ x, (b x)^2) ≤ 2*(∑ j, ∫ x, (T j x)^2)+8*(∑ j, ∫ x, (R j x)^2) at htest
  have hV := hVb z theta ht.continuous hts' htb
  have hq : MemLp q 2 volume := (sphere_chart_cutoff_difference_bound d p z eta he hes' i h).1
  have hRb' := hRb q hq
  have hRbound : (∑ j, ∫ x, (R j x)^2) ≤ (CR*CQ)*‖z‖^2 := by
    exact hRb'.2.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hQb z i h).2 hCR.le)
  have hbs : tsupport beta ⊆ Yau.realCenteredCube 4 (3/4) := tsupport_mul_subset_left.trans hts
  have hlit := sphere_resolvent_H1_difference_test_literal d f p z eta beta he (ht.mul ht)
    hes' (3/4) (by norm_num) hbs i h (by linarith)
  dsimp only at hlit
  have hDP (j : Fin 4) : Integrable (fun x ↦ D j x*P j x) := by
    apply (hlit.2.2.1 j).congr
    apply Filter.Eventually.of_forall
    intro x
    exact congrArg (fun t : ℝ ↦ D j x*t)
      (sphere_difference_square_test_derivative d p z eta theta ht i j h hlocal x)
  have heq : (∑ j, ∫ x, D j x*P j x)=-(∫ x, F x*b x) := by
    rw [← hlit.2.2.2.2]
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    exact (congrArg (fun t : ℝ ↦ D j x*t)
      (sphere_difference_square_test_derivative d p z eta theta ht i j h hlocal x)).symm
  have henergy := Yau.real_difference_energy_absorption volume m K hm T V R D P F b
    (fun j ↦ (htest.1 j).1) hV.1 (fun j ↦ (htest.1 j).2.1) hDP
    (sphereChartForcingZero_memLp d p f) htest.2.1
    (hcoer z eta theta ht hts i h hh hlocal) htest.2.2 heq
  have hnorm : ‖z‖^2 ≤ ‖f‖^2+‖z‖^2 := by nlinarith [sq_nonneg ‖f‖]
  have hglobal : (∑ j, ∫ x, (T j x)^2) ≤ C0*(‖f‖^2+‖z‖^2) := by
    apply henergy.trans
    have h1 := mul_le_mul_of_nonneg_left (hFb f) (show 0 ≤ 8/m by positivity)
    have h2 := mul_le_mul_of_nonneg_left (hV.2.trans (mul_le_mul_of_nonneg_left hnorm hCV.le)) hK.le
    have h3 := mul_le_mul_of_nonneg_left (hRbound.trans
      (mul_le_mul_of_nonneg_left hnorm (mul_nonneg hCR.le hCQ.le))) (add_nonneg hK.le hm.le)
    have ht' := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3)
      (show 0 ≤ 4/m by positivity)
    convert ht' using 1
    dsimp [C0,z]
    ring
  refine ⟨fun j ↦ sphere_chart_interior_difference_memLp d p z i j h hh,?_⟩
  apply le_trans (Finset.sum_le_sum (fun j _ ↦ ?_)) hglobal
  have hEq : (∫ x in Yau.realCenteredCube 4 (1/2),
      (Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z) x)^2) =
      ∫ x in Yau.realCenteredCube 4 (1/2), (T j x)^2 := by
    apply setIntegral_congr_fun (Yau.realCenteredCube_isCompact 4 (1/2)).measurableSet
    intro x hx
    dsimp [T]
    rw [(ht1 x hx).eq_of_nhds,one_mul]
  rw [hEq]
  have hmono := setIntegral_mono_set (s := Yau.realCenteredCube 4 (1/2)) (t := Set.univ) ((htest.1 j).1.integrable_sq.integrableOn (s := Set.univ))
    (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))
    (Filter.Eventually.of_forall (fun x _ ↦ Set.mem_univ x))
  simpa only [Measure.restrict_univ] using hmono

end
end Yau.Target

end OAI
