import OAI.Geometry.NodalSets.Charts.SphereChartCutoffApproximation
import OAI.Geometry.NodalSets.Elliptic.RealBallCubeContainmentLemmas
import OAI.Geometry.NodalSets.Elliptic.RealCubeCutoffs

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section
local instance sphereInteriorDifferenceL2Measurable : MeasurableSpace Base := borel Base
local instance sphereInteriorDifferenceL2Borel : BorelSpace Base := ⟨rfl⟩

theorem sphere_chart_interior_difference_memLp (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (i j : Fin 4) (h : ℝ) (hh : |h| ≤ 1/8) :
    MemLp (Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z)) 2
      (volume.restrict (Yau.realCenteredCube 4 (1/2))) := by
  obtain ⟨eta,theta,he,ht,hec,htc,hes,hts,heb,htb,ht1,he1⟩ :=
    Yau.real_interior_difference_cutoffs
  have hes' : tsupport eta ⊆ realFinCube 4 := hes
  have hg := (sphere_chart_cutoff_weak d p z eta he hes').2 j
  have hm := (Yau.realDifferenceQuotient_memLp i h _ hg.1).mono_measure
    (Measure.restrict_le_self (s := Yau.realCenteredCube 4 (1/2)))
  apply hm.ae_eq
  apply (ae_restrict_iff' (Yau.realCenteredCube_isCompact 4 (1/2)).measurableSet).mpr
  apply Filter.Eventually.of_forall
  intro x hx
  have hxθ : x ∈ tsupport theta := subset_tsupport theta (by
    change theta x ≠ 0
    rw [(ht1 x hx).eq_of_nhds]
    norm_num)
  obtain ⟨hex,het⟩ := he1 i h hh x hxθ
  exact Yau.real_cutoff_gradient_difference_of_one eta _ _ i j h x hex het

theorem sphere_chart_weighted_difference_memLp (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (eta theta : Yau.Jets.Coord → ℝ)
    (he : ContDiff ℝ ∞ eta) (ht : Continuous theta)
    (hes : tsupport eta ⊆ realFinCube 4) (htc : HasCompactSupport theta)
    (i j : Fin 4) (h : ℝ)
    (h1 : ∀ x ∈ tsupport theta, eta =ᶠ[𝓝 x] (fun _ ↦ 1) ∧
      eta =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1)) :
    MemLp (fun x ↦ theta x*Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z) x)
      2 volume := by
  have hg := (sphere_chart_cutoff_weak d p z eta he hes).2 j
  have hm := Yau.realDifferenceQuotient_memLp i h _ hg.1
  have hb := Yau.real_compact_localL2_product htc theta _ ht (Subset.rfl)
    (hm.mono_measure Measure.restrict_le_self)
  apply hb.ae_eq
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  by_cases hx : x ∈ tsupport theta
  · exact congrArg (fun t : ℝ ↦ theta x*t)
      (Yau.real_cutoff_gradient_difference_of_one eta _ _ i j h x (h1 x hx).1 (h1 x hx).2)
  · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,zero_mul]

end
end Yau.Target

end OAI
