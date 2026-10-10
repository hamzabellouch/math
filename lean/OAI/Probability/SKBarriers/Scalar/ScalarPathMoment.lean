import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarCDFLimit
import OAI.Probability.SKBarriers.Scalar.ScalarTiltedExpectation
import OAI.Probability.SKBarriers.Hierarchy.HierarchyExponentialMoment

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarPath_terminal_affine (n : ℕ) (v : Fin n → ℝ) :
    (fun z => scalarSpinTerminal (coordinateLinear n v z))=
      affineLogPartition (fun _ : Bool => 0) (fun b => spin b • coordinateLinear n v) := by
  funext z
  rw [affineLogPartition_bool]
  rfl

theorem scalarPath_square_bound (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) :
    (∫ z, (coordinateLinear n v z)^2 ∂hierarchyPathLaw n m
      (fun z => scalarSpinTerminal (coordinateLinear n v z)) 0) ≤
      2*(∑ i, (v i)^2)+4*(∑ i, (v i)^2)^2 := by
  rw [scalarPath_terminal_affine]
  have H := affineHierarchy_square_bound n m hm hmono (fun _ : Bool => 0)
    (fun b => spin b • coordinateLinear n v) (fun i => |v i|) (fun i => abs_nonneg _)
    (fun b i => by cases b <;> simp [spin]) 0 v
  have he : (∑ i, |v i| * |v i|) = ∑ i, (v i)^2 := Finset.sum_congr rfl (fun i _ => by rw [← sq_abs]; ring)
  rw [he] at H
  nlinarith

theorem scalarPath_square_integrable (n : ℕ) (m v : Fin n → ℝ) :
    Integrable (fun z => (coordinateLinear n v z)^2) (hierarchyPathLaw n m
      (fun z => scalarSpinTerminal (coordinateLinear n v z)) 0) := by
  rw [hierarchyPathLaw_eq_tilted n m _ (scalarSpinTerminal_regular.compCLM (coordinateLinear n v)) 0]
  exact ((HasExpGrowth.linear (coordinateLinear n v)).pow 2).integrable_tilted_fiberGaussian n _
    (hierarchyPathLogDensity_regular n m (scalarSpinTerminal_regular.compCLM (coordinateLinear n v)))
    ((coordinateLinear n v).continuous.pow 2) 0

theorem scalarMagnetization_gap_envelope {R : ℝ} (hR : 0<R) (x : ℝ) :
    (1/(Real.cosh R)^2)*(1-x^2/R^2) ≤ 1-(scalarMagnetization x)^2 := by
  rw [← scalarMagnetization_derivative_identity]
  by_cases h : |x|≤R
  · have hc : Real.cosh x ≤ Real.cosh R := Real.cosh_le_cosh.mpr (by simpa only [abs_of_pos hR] using h)
    have hh : 1/(Real.cosh R)^2 ≤ 1/(Real.cosh x)^2 :=
      one_div_le_one_div_of_le (by positivity) (sq_le_sq₀ (Real.cosh_pos x).le (Real.cosh_pos R).le |>.mpr hc)
    have hsmall : 1-x^2/R^2 ≤ 1 := by
      have : 0 ≤ x^2/R^2 := by positivity
      linarith
    exact (mul_le_of_le_one_right (by positivity) hsmall).trans hh
  · have hr : R^2 ≤ x^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ hR.le (abs_nonneg x)).mpr (le_of_not_ge h)
    have hdiv : 1≤x^2/R^2 := (one_le_div (sq_pos_of_pos hR)).mpr hr
    exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)).trans (by positivity)

theorem scalarHierarchyAverage_square_gap (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {T : ℝ} (hT : 0≤T) (hv : ∑ i, (v i)^2 ≤ T) :
    scalarHierarchyAverage n m v scalarSpinTerminal (fun z => (scalarMagnetization z)^2) 0 ≤
      1-(1/(2*(Real.cosh (1+2*T+4*T^2))^2)) := by
  let μ := hierarchyPathLaw n m (fun z => scalarSpinTerminal (coordinateLinear n v z)) 0
  let L := coordinateLinear n v
  let M := 2*T+4*T^2
  let R := 1+M
  have hM : 0≤M := by dsimp [M]; positivity
  have hR : 0<R := by dsimp [R]; positivity
  have hR2 : 2*M ≤ R^2 := by dsimp only [R]; nlinarith [sq_nonneg M]
  let := hierarchyPathLaw_probability n m _ (scalarSpinTerminal_regular.compCLM L) 0
  have hi : Integrable (fun z => (L z)^2) μ := scalarPath_square_integrable n m v
  have hib : Integrable (fun z => (scalarMagnetization (L z))^2) μ :=
    hierarchyPathLaw_integrable n m _ _ (scalarSpinTerminal_regular.compCLM L)
      (scalarMagnetization_lipschitz.continuous.comp L.continuous |>.pow 2)
      (C:=1) (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; exact scalarMagnetization_sq_le_one _) 0
  have H := integral_mono (((integrable_const (1:ℝ)).sub (hi.div_const (R^2))).const_mul (1/(Real.cosh R)^2))
    ((integrable_const (1:ℝ)).sub hib) (fun z => scalarMagnetization_gap_envelope hR (L z))
  change (∫ z, (1/(Real.cosh R)^2)*(1-(L z)^2/R^2) ∂μ) ≤ ∫ z, 1-(scalarMagnetization (L z))^2 ∂μ at H
  simp only [integral_const_mul,integral_sub (integrable_const _) (hi.div_const _),
    integral_sub (integrable_const _) hib,integral_div,integral_const,probReal_univ,smul_eq_mul,one_mul] at H
  have hs : 0 ≤ ∑ i, (v i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have HM : (∫ z, (L z)^2 ∂μ)≤M := (scalarPath_square_bound n m v hm hmono).trans (by
    dsimp only [M]; nlinarith [sq_le_sq₀ hs hT |>.mpr hv])
  have Hd : (∫ z, (L z)^2 ∂μ)/R^2 ≤ 1/2 := (div_le_iff₀ (sq_pos_of_pos hR)).mpr (by linarith)
  rw [scalarHierarchyAverage_eq_integral n m v (g:=fun z => (scalarMagnetization z)^2) scalarSpinTerminal_regular
    (scalarMagnetization_lipschitz.continuous.pow 2) zero_le_one (fun z => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact scalarMagnetization_sq_le_one z) 0]
  simp only [zero_add]
  have hRdef : 1+2*T+4*T^2=R := by dsimp [R,M]; ring
  rw [hRdef]
  change (∫ z, (scalarMagnetization (L z))^2 ∂μ) ≤ 1-1/(2*(Real.cosh R)^2)
  have hc : 0≤1/(Real.cosh R)^2 := by positivity
  have hh : 1/(2*(Real.cosh R)^2)=(1/(Real.cosh R)^2)/2 := by ring
  rw [hh]
  nlinarith [mul_le_mul_of_nonneg_left Hd hc]

end SK.Analytic

end
end

end OAI
