import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarHierarchyAverageAlgebra
import OAI.Probability.SKBarriers.Hierarchy.HierarchyScoreGeneral
import OAI.Probability.SKBarriers.Scalar.ScalarLevelRepresentation

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarPath_square_bound_convex (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hc : ScalarSpinConvex f) :
    (∫ z, (coordinateLinear n v z)^2 ∂hierarchyPathLaw n m
      (fun z => f (coordinateLinear n v z)) 0) ≤
      2*(∑ i, (v i)^2)+4*(∑ i, (v i)^2)^2 := by
  have H := hierarchy_square_bound n m hm hmono (fun z => f (coordinateLinear n v z))
    (hf.compCLM (coordinateLinear n v)) (fun i => |v i|) (fun i => abs_nonneg _)
    (fun z i => by
      rw [(scalar_comp_directional hf (coordinateLinear n v) z (coordinateAxis n i)).1,
        coordinateLinear_coordinateAxis,abs_mul]
      exact (mul_le_mul_of_nonneg_right (hc.bounds _).1 (abs_nonneg _)).trans_eq (one_mul _)) 0 v
  have he : (∑ i, |v i| * |v i|) = ∑ i, (v i)^2 :=
    Finset.sum_congr rfl (fun i _ => by rw [← sq_abs]; ring)
  rw [he] at H
  nlinarith

theorem scalarHierarchyAverage_compact_lower (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hc : ScalarSpinConvex f)
    (hg : BoundedScalar g) {T c : ℝ} (hT : 0≤T) (hV : ∑ i, (v i)^2 ≤ T)
    (hc0 : 0≤c) (hg0 : ∀ x,0≤g x)
    (hgc : ∀ x, |x|≤1+2*T+4*T^2 → c≤g x) :
    c/2≤ scalarHierarchyAverage n m v f g 0 := by
  let μ := hierarchyPathLaw n m (fun z => f (coordinateLinear n v z)) 0
  let L := coordinateLinear n v
  let M := 2*T+4*T^2
  let R := 1+M
  have hM : 0≤M := by dsimp [M]; positivity
  have hR : 0<R := by dsimp [R]; positivity
  have hR2 : 2*M≤R^2 := by dsimp only [R]; nlinarith [sq_nonneg M]
  have hRdef : 1+2*T+4*T^2=R := by dsimp [R,M]; ring
  have he (x : ℝ) : c*(1-x^2/R^2)≤g x := by
    by_cases hx : |x|≤R
    · have H : 1-x^2/R^2≤1 := sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))
      exact (mul_le_of_le_one_right hc0 H).trans (hgc x (hRdef ▸ hx))
    · have hsq : R^2≤x^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ hR.le (abs_nonneg x)).mpr (le_of_not_ge hx)
      have hdiv : 1≤x^2/R^2 := (one_le_div (sq_pos_of_pos hR)).mpr hsq
      exact (mul_nonpos_of_nonneg_of_nonpos hc0 (by linarith)).trans (hg0 x)
  have hF : BoundedDerivs (fun z => f (L z)) := hf.compCLM L
  let := hierarchyPathLaw_probability n m _ hF 0
  have hi : Integrable (fun z => (L z)^2) μ := by
    rw [show μ=(fiberGaussian n 0).tilted (hierarchyPathLogDensity n m (fun z => f (L z))) from
      hierarchyPathLaw_eq_tilted n m _ hF 0]
    exact ((HasExpGrowth.linear L).pow 2).integrable_tilted_fiberGaussian n _
      (hierarchyPathLogDensity_regular n m hF) (L.continuous.pow 2) 0
  have hig : Integrable (fun z => g (L z)) μ := by
    obtain ⟨B,hB,hb⟩ := hg.bounded
    exact hierarchyPathLaw_integrable n m _ _ hF (hg.continuous.comp L.continuous)
      (C:=B) (fun z => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hb (L z)) 0
  have H := integral_mono (((integrable_const (1:ℝ)).sub (hi.div_const (R^2))).const_mul c) hig
    (fun z => he (L z))
  change (∫ z, c*(1-(L z)^2/R^2) ∂μ)≤∫ z,g (L z) ∂μ at H
  simp only [integral_const_mul,integral_sub (integrable_const _) (hi.div_const _),
    integral_div,integral_const,probReal_univ,smul_eq_mul,one_mul] at H
  have hs : 0≤∑ i,(v i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have HM : (∫ z, (L z)^2 ∂μ)≤M := (scalarPath_square_bound_convex n m v hm hmono hf hc).trans (by
    dsimp only [M]; nlinarith [sq_le_sq₀ hs hT |>.mpr hV])
  have Hd : (∫ z, (L z)^2 ∂μ)/R^2≤1/2 := (div_le_iff₀ (sq_pos_of_pos hR)).mpr (by linarith)
  rw [scalarHierarchyAverage_integral hf hg]
  simp only [zero_add]
  change c/2≤∫ z,g (L z) ∂μ
  nlinarith [mul_le_mul_of_nonneg_left Hd hc0]

end SK.Analytic

end
end

end OAI
