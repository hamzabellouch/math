import OAI.Geometry.NodalSets.Charts.SphereChartDifferenceBound
import OAI.Geometry.NodalSets.Charts.SphereChartFluxL2

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set
open scoped ContDiff
noncomputable section
local instance sphereChartUniformH1BoundsMeasurable : MeasurableSpace Base := borel Base
local instance sphereChartUniformH1BoundsBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_cutoff_uniform_H1_bound (d : SphereEnergyData) (p : Base)
    (eta : Yau.Jets.Coord → ℝ) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realFinCube 4) :
    ∃ C > 0, ∀ (z : SphereEnergyHilbert d) (i : Fin 4) (h : ℝ),
      (∫ x, (eta x*(sphereChartDerivativeMap d p i z) x+
        Yau.coordPartial eta x i*(sphereEnergyL2Map d z) (sphereChartCoordMap p x))^2) ≤ C*‖z‖^2 ∧
      (∫ x, (Yau.realDifferenceQuotient i h
        (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y)) x)^2) ≤ C*‖z‖^2 := by
  let C : ℝ := 1+∑ j : Fin 4, ‖sphereCutoffDerivativeMap d p eta he hs j‖^2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun z i h ↦ ?_⟩
  have hi : ‖sphereCutoffDerivativeMap d p eta he hs i‖^2 ≤ C := by
    have ht := Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin 4 ↦ ‖sphereCutoffDerivativeMap d p eta he hs j‖^2)
      (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)
    dsimp [C]
    linarith
  have hn := (sphereCutoffDerivativeMap d p eta he hs i).le_opNorm z
  have hn2 : ‖sphereCutoffDerivativeMap d p eta he hs i z‖^2 ≤ C*‖z‖^2 := by
    have ht := mul_le_mul_of_nonneg_right hi (sq_nonneg ‖z‖)
    nlinarith [norm_nonneg (sphereCutoffDerivativeMap d p eta he hs i z),
      mul_nonneg (norm_nonneg (sphereCutoffDerivativeMap d p eta he hs i)) (norm_nonneg z)]
  rw [Yau.real_L2_norm_sq_rep _ _ (sphereCutoffDerivativeMap_ae d p eta he hs i z)] at hn2
  exact ⟨hn2,(sphere_chart_cutoff_difference_bound d p z eta he hs i h).2.trans hn2⟩

theorem sphere_chart_uniform_gradient_bound (d : SphereEnergyData) (p : Base) :
    ∃ C > 0, ∀ z : SphereEnergyHilbert d,
      (∑ j : Fin 4, ∫ x in realFinCube 4, ((sphereChartDerivativeMap d p j z) x)^2) ≤ C*‖z‖^2 := by
  obtain ⟨B,hB,hb⟩ := sphereChartDerivativeMap_bound d p
  refine ⟨4*B^2,by positivity,fun z ↦ ?_⟩
  have hj (j : Fin 4) :
      (∫ x in realFinCube 4, ((sphereChartDerivativeMap d p j z) x)^2) ≤ B^2*‖z‖^2 := by
    have hn : ‖sphereChartDerivativeMap d p j z‖^2 =
        ∫ x in realFinCube 4, ((sphereChartDerivativeMap d p j z) x)^2 := by
      simpa only [Lp.toLp_coeFn] using Yau.real_toLp_norm_sq _ (Lp.memLp (sphereChartDerivativeMap d p j z))
    rw [← hn]
    have ht := hb j z
    nlinarith [norm_nonneg (sphereChartDerivativeMap d p j z),mul_nonneg hB.le (norm_nonneg z)]
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hj j)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_assoc] using ht

theorem sphere_chart_forcingZero_uniform_bound (d : SphereEnergyData) (p : Base) :
    ∃ C > 0, ∀ f : SphereWeightedL2 d,
      (∫ x, (sphereChartForcingZero d p f x)^2) ≤ C*(‖f‖^2+‖sphereWeakSolution d f‖^2) := by
  obtain ⟨C,hC,hb⟩ := sphereChartResolventForcing_bound d p (realFinCube_isCompact 4)
  refine ⟨C,hC,fun f ↦ ?_⟩
  have he : (fun x ↦ (sphereChartForcingZero d p f x)^2) =
      (realFinCube 4).indicator (fun x ↦ (sphereChartResolventForcing d p f x)^2) := by
    funext x
    by_cases hx : x ∈ realFinCube 4 <;> simp [sphereChartForcingZero,hx]
  rw [he,integral_indicator (realFinCube_isCompact 4).measurableSet]
  exact (hb f).2

end
end Yau.Target

end OAI
