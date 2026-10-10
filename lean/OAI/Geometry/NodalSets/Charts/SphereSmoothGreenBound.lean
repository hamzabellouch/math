import OAI.Geometry.NodalSets.Charts.SphereSmoothGreenLocal
import OAI.Geometry.NodalSets.Charts.SphereWeightedL1Bound

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory Set
open scoped ContDiff
noncomputable section
local instance sphereSmoothGreenBoundMeasurable : MeasurableSpace Base := borel Base
local instance sphereSmoothGreenBoundBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_smooth_dirichlet_L1_bound (d : SphereEnergyData) (v : SphereEnergySmooth d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SphereEnergySmooth d,
      |sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v)| ≤
        C*(∫ x, |(SphereEnergySmooth.toSmooth d u : Base → ℝ) x| ∂sphereReferenceMeasure) := by
  classical
  obtain ⟨P,theta,htheta,_,hc,hgreen⟩ := sphere_smooth_green_finite_partition d.tensor d.smooth d.symm d.pos
  let I := {p // p ∈ P}
  let G : I → Yau.Jets.Coord → ℝ := fun p x ↦ theta p (sphereChartCoordMap p.val x)*
    Yau.weightedDiv roundCoordDensity (sphereChartFlux d.tensor (SphereEnergySmooth.toSmooth d v) p.val) x
  have hG (p : I) : Continuous (G p) :=
    (spherePullback_smooth (theta p) (htheta p) p.val).continuous.mul
      (Yau.weightedDiv_smooth roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne')
        (intrinsicRealVector_smooth d.tensor d.smooth d.symm d.pos (SphereEnergySmooth.toSmooth d v)
          (SphereEnergySmooth.toSmooth d v).property p.val)).continuous
  have hGc (p : I) : HasCompactSupport (G p) := (hc p).mul_right
  have hb (p : I) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |G p x| ≤ K := by
    obtain ⟨K,hK⟩ := (((hGc p).isCompact_range (hG p)).image continuous_norm).bddAbove
    refine ⟨max K 0,le_max_right _ _,fun x ↦ ?_⟩
    exact (hK ⟨G p x,⟨x,rfl⟩,rfl⟩).trans (le_max_left _ _)
  choose K hK hKb using hb
  refine ⟨∑ p, K p,Finset.sum_nonneg (fun p _ ↦ hK p),?_⟩
  intro u
  let f : Base → ℝ := SphereEnergySmooth.toSmooth d u
  have hf : Continuous f := (SphereEnergySmooth.toSmooth d u).property.continuous
  have hI (p : I) : Integrable (fun x ↦ roundCoordDensity x*|f (sphereChartCoordMap p.val x)|) := by
    simpa only [roundChartDensity_coord_eq] using
      (sphereReferenceMeasure_integrable_chart p.val (fun x ↦ |f x|)).mp
        (sphereReferenceMeasure_integrable_continuous _ hf.abs)
  have hterm (p : I) : |∫ x, roundCoordDensity x*f (sphereChartCoordMap p.val x)*G p x| ≤
      K p*(∫ x, |f x| ∂sphereReferenceMeasure) := by
    have hi : Integrable (fun x ↦ roundCoordDensity x*f (sphereChartCoordMap p.val x)*G p x) :=
      ((roundCoordDensity_smooth.continuous.mul (hf.comp (sphereChartCoordMap_smooth p.val).continuous)).mul (hG p)).integrable_of_hasCompactSupport
        (hGc p).mul_left
    calc
      _ ≤ ∫ x, ‖roundCoordDensity x*f (sphereChartCoordMap p.val x)*G p x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, K p*(roundCoordDensity x*|f (sphereChartCoordMap p.val x)|) := by
        apply integral_mono hi.norm ((hI p).const_mul (K p))
        intro x
        simp only [norm_mul,Real.norm_eq_abs,abs_of_pos (roundCoordDensity_pos x)]
        nlinarith [mul_le_mul_of_nonneg_left (hKb p x)
          (mul_nonneg (roundCoordDensity_pos x).le (abs_nonneg (f (sphereChartCoordMap p.val x))))]
      _ = _ := by
        rw [integral_const_mul,sphereReferenceMeasure_integral_chart p.val]
        simp only [roundChartDensity_coord_eq]
  have hg := hgreen f (SphereEnergySmooth.toSmooth d v) (SphereEnergySmooth.toSmooth d u).property
    (SphereEnergySmooth.toSmooth d v).property
  rw [hg,abs_neg]
  calc
    _ = |∑ p : I, ∫ x, roundCoordDensity x*f (sphereChartCoordMap p.val x)*G p x| := by
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x ↦ by dsimp [G]; ring)
    _ ≤ ∑ p : I, |∫ x, roundCoordDensity x*f (sphereChartCoordMap p.val x)*G p x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : I, K p*(∫ x, |f x| ∂sphereReferenceMeasure) :=
      Finset.sum_le_sum (fun p _ ↦ hterm p)
    _ = _ := by rw [Finset.sum_mul]

theorem sphere_smooth_dirichlet_L2_bound (d : SphereEnergyData) (v : SphereEnergySmooth d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SphereEnergySmooth d,
      |sphereDirichletForm d.tensor (SphereEnergySmooth.toSmooth d u) (SphereEnergySmooth.toSmooth d v)| ≤
        C*‖sphereEnergyL2Linear d u‖ := by
  obtain ⟨C,hC,hb⟩ := sphere_smooth_dirichlet_L1_bound d v
  obtain ⟨B,hB,hL⟩ := sphere_reference_L1_bound d
  refine ⟨C*B,mul_nonneg hC hB,fun u ↦ ?_⟩
  exact (hb u).trans ((mul_le_mul_of_nonneg_left (hL u) hC).trans_eq (mul_assoc C B _).symm)

end
end Yau.Target

end OAI
