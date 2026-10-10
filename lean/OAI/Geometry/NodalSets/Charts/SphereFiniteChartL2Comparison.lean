import OAI.Geometry.NodalSets.Charts.SphereFiniteSmoothPartition
import OAI.Geometry.NodalSets.Charts.SphereReferenceMeasurePositive
import OAI.Geometry.NodalSets.Elliptic.RealCubeL2EmbeddingLemmas

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem sphere_finite_chart_l2_comparison (rho : Base → ℝ)
    (hr : Continuous rho) (hrp : ∀ x, 0 < rho x) :
    ∃ (P : Finset Base) (R : ℝ), 0 < R ∧ ∀ u : Base → ℝ, Continuous u →
      sphereWeightedPairing rho u u ≤
        R*∑ p : {p // p ∈ P}, ∫ x in realFinCube 4, (u (sphereChartCoordMap p.val x))^2 := by
  classical
  obtain ⟨P,theta,htheta,htn,htsum,_,htsupport,_⟩ := sphere_finite_smooth_partition
  obtain ⟨R,hR,hRb⟩ := (isCompact_univ.image hr).isBounded.exists_pos_norm_le
  have hrle (x : Base) : rho x ≤ R := (le_abs_self _).trans (hRb _ ⟨x,mem_univ x,rfl⟩)
  have htle (p : {p // p ∈ P}) (x : Base) : theta p x ≤ 1 := by
    rw [← htsum x]
    exact Finset.single_le_sum (fun q _ ↦ htn q x) (Finset.mem_univ p)
  refine ⟨P,R,hR,?_⟩
  intro u hu
  let f : {p // p ∈ P} → Base → ℝ := fun p x ↦ rho x*theta p x*u x^2
  have hf (p : {p // p ∈ P}) : Continuous (f p) := (hr.mul (htheta p).continuous).mul (hu.pow 2)
  have hsum (x : Base) : (∑ p, f p x)=rho x*u x*u x := by
    simp only [f,← Finset.sum_mul,← Finset.mul_sum,htsum,one_mul,pow_two,mul_assoc]
  have hlocal (p : {p // p ∈ P}) : (∫ x, f p x ∂sphereReferenceMeasure) ≤
      R*(∫ x in realFinCube 4, (u (sphereChartCoordMap p.val x))^2) := by
    let F : Yau.Jets.Coord → ℝ := fun x ↦ roundCoordDensity x*f p (sphereChartCoordMap p.val x)
    have hF : Continuous F := roundCoordDensity_smooth.continuous.mul
      ((hf p).comp (sphereChartCoordMap_smooth p.val).continuous)
    have hz (x : Yau.Jets.Coord) (hx : x ∉ realFinCube 4) : F x=0 := by
      have ht : theta p (sphereChartCoordMap p.val x)=0 := by
        apply Function.notMem_support.mp
        intro hs
        have hb := htsupport p (subset_closure hs)
        exact hx (by rwa [realFinCube_four_eq_closedBall])
      simp [F,f,ht]
    rw [sphereReferenceMeasure_integral_chart p.val]
    simp only [roundChartDensity_coord_eq]
    change (∫ x, F x) ≤ _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    have hpt (x : Yau.Jets.Coord) : F x ≤ R*(u (sphereChartCoordMap p.val x))^2 := by
      have h1 := mul_le_mul_of_nonneg_right (roundCoordDensity_le_one x) (hrp (sphereChartCoordMap p.val x)).le
      have h2 := mul_le_mul_of_nonneg_left (htle p (sphereChartCoordMap p.val x))
        (mul_nonneg (roundCoordDensity_pos x).le (hrp (sphereChartCoordMap p.val x)).le)
      have hb : roundCoordDensity x*rho (sphereChartCoordMap p.val x)*theta p (sphereChartCoordMap p.val x) ≤ R := by
        nlinarith only [h1,h2,hrle (sphereChartCoordMap p.val x)]
      have h := mul_le_mul_of_nonneg_right hb (sq_nonneg (u (sphereChartCoordMap p.val x)))
      dsimp [F,f]
      nlinarith only [h]
    have hiR : IntegrableOn (fun x ↦ R*(u (sphereChartCoordMap p.val x))^2) (realFinCube 4) :=
      realFinCube_integrable 4 _ (((hu.comp (sphereChartCoordMap_smooth p.val).continuous).pow 2).const_mul R)
    have hm := setIntegral_mono_on (μ := volume) (s := realFinCube 4)
      (realFinCube_integrable 4 F hF) hiR
      (realFinCube_isCompact 4).measurableSet (fun x _ ↦ hpt x)
    rw [integral_const_mul] at hm
    exact hm

  calc
    sphereWeightedPairing rho u u = ∫ x, ∑ p, f p x ∂sphereReferenceMeasure := by
      unfold sphereWeightedPairing
      exact integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ (hsum x).symm))
    _ = ∑ p, ∫ x, f p x ∂sphereReferenceMeasure := by
      exact integral_finsetSum (Finset.univ : Finset {p // p ∈ P})
        (fun p _ ↦ sphereReferenceMeasure_integrable_continuous _ (hf p))
    _ ≤ ∑ p : {p // p ∈ P}, R*(∫ x in realFinCube 4, (u (sphereChartCoordMap p.val x))^2) :=
      by
        exact Finset.sum_le_sum (fun p _ ↦ hlocal p)
    _ = _ := by
      rw [Finset.mul_sum]

end
end Yau.Target

end OAI
