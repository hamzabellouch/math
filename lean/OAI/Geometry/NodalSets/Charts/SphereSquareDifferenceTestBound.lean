import OAI.Geometry.NodalSets.Charts.SphereDifferenceCoercivity
import OAI.Geometry.NodalSets.Charts.SphereDifferenceTestBound
import OAI.Geometry.NodalSets.Charts.SphereInteriorDifferenceL2
import OAI.Geometry.NodalSets.Elliptic.RealCompactGradientMultiplier

namespace OAI

namespace Yau.Target
open MeasureTheory Yau.Geometry Set Filter
open scoped ContDiff Topology
noncomputable section
local instance sphereSquareDifferenceTestBoundMeasurable : MeasurableSpace Base := borel Base
local instance sphereSquareDifferenceTestBoundBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_square_difference_test_bound (d : SphereEnergyData) (p : Base)
    (z : SphereEnergyHilbert d) (eta theta : Yau.Jets.Coord → ℝ)
    (he : ContDiff ℝ ∞ eta) (ht : ContDiff ℝ ∞ theta)
    (hes : tsupport eta ⊆ realFinCube 4) (hts : tsupport theta ⊆ realFinCube 4)
    (hθ : ∀ x, 0 ≤ theta x ∧ theta x ≤ 1) (i : Fin 4) (h : ℝ)
    (h1 : ∀ x ∈ tsupport theta, eta =ᶠ[𝓝 x] (fun _ ↦ 1) ∧
      eta =ᶠ[𝓝 (x+Pi.single i h)] (fun _ ↦ 1)) :
    let q := Yau.realDifferenceQuotient i h
      (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y))
    let T := fun j x ↦ theta x*Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z) x
    let R := fun j x ↦ Yau.coordPartial theta x j*q x
    let P := fun j x ↦ theta x*(T j x+2*R j x)
    let phi := fun x ↦ (theta x*theta x)*q x
    let b := Yau.realDifferenceQuotient i (-h) phi
    (∀ j : Fin 4, MemLp (T j) 2 volume ∧ MemLp (R j) 2 volume ∧ MemLp (P j) 2 volume) ∧
      MemLp b 2 volume ∧
      (∫ x, (b x)^2) ≤ 2*(∑ j, ∫ x, (T j x)^2)+8*(∑ j, ∫ x, (R j x)^2) := by
  dsimp only
  let q := Yau.realDifferenceQuotient i h
    (fun y ↦ eta y*(sphereEnergyL2Map d z) (sphereChartCoordMap p y))
  let T := fun j x ↦ theta x*Yau.realDifferenceQuotient i h (sphereChartDerivativeMap d p j z) x
  let R := fun j x ↦ Yau.coordPartial theta x j*q x
  let P := fun j x ↦ theta x*(T j x+2*R j x)
  let beta := fun x ↦ theta x*theta x
  have hbs : tsupport beta ⊆ realFinCube 4 := tsupport_mul_subset_left.trans hts
  have htc : HasCompactSupport theta := (realFinCube_isCompact 4).of_isClosed_subset (isClosed_tsupport theta) hts
  have hq : MemLp q 2 volume := Yau.realDifferenceQuotient_memLp i h _ (sphere_chart_cutoff_weak d p z eta he hes).1
  have hT (j : Fin 4) : MemLp (T j) 2 volume :=
    sphere_chart_weighted_difference_memLp d p z eta theta he ht.continuous hes htc i j h h1
  obtain ⟨_,_,hRb⟩ := Yau.real_compact_gradient_multiplier_bound theta ht htc
  have hR (j : Fin 4) : MemLp (R j) 2 volume := (hRb q hq).1 j
  have hrep (j : Fin 4) :
      (sphereDifferenceTestDerivativeMap d p eta beta he (ht.mul ht) hes hbs i h j z : Yau.Jets.Coord → ℝ)
      =ᵐ[volume] P j := by
    apply (sphereDifferenceTestDerivativeMap_ae d p eta beta he (ht.mul ht) hes hbs i h j z).trans
    exact Filter.Eventually.of_forall (sphere_difference_square_test_derivative d p z eta theta ht i j h h1)
  have hP (j : Fin 4) : MemLp (P j) 2 volume := (memLp_congr_ae (hrep j)).mp (Lp.memLp _)
  have hv := sphereDifferenceTestMap_ae d p eta beta he (ht.mul ht) hes hbs i h z
  have hd := Yau.realL2DifferenceMap_ae i (-h) _ _ hv
  have hbound := sphere_difference_test_difference_bound d p z eta beta he (ht.mul ht) hes hbs i h i (-h)
  rw [Yau.real_L2_norm_sq_rep _ _ hd,Yau.real_L2_norm_sq_rep _ _ (hrep i)] at hbound
  have hpw (x : Yau.Jets.Coord) : (P i x)^2 ≤ 2*(T i x)^2+8*(R i x)^2 := by
    have hθsq : (theta x)^2 ≤ 1 := by nlinarith [(hθ x).1,(hθ x).2]
    have hle : (P i x)^2 ≤ (T i x+2*R i x)^2 := by
      dsimp only [P]
      rw [mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) hθsq
    nlinarith [sq_nonneg (T i x-2*R i x)]
  have hpi := integral_mono (hP i).integrable_sq
    (((hT i).integrable_sq.const_mul 2).add ((hR i).integrable_sq.const_mul 8)) hpw
  dsimp only [Pi.add_apply] at hpi
  rw [integral_add ((hT i).integrable_sq.const_mul 2) ((hR i).integrable_sq.const_mul 8),
    integral_const_mul,integral_const_mul] at hpi
  have hiT : (∫ x, (T i x)^2) ≤ ∑ j, ∫ x, (T j x)^2 :=
    Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 4 ↦ ∫ x, (T j x)^2)
      (fun j _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)) (Finset.mem_univ i)
  have hiR : (∫ x, (R i x)^2) ≤ ∑ j, ∫ x, (R j x)^2 :=
    Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 4 ↦ ∫ x, (R j x)^2)
      (fun j _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)) (Finset.mem_univ i)
  refine ⟨fun j ↦ ⟨hT j,hR j,hP j⟩,(memLp_congr_ae hd).mp (Lp.memLp _),?_⟩
  exact hbound.trans (hpi.trans (by linarith))

end
end Yau.Target

end OAI
