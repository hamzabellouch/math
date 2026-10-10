import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarPathMoment

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarPath_terminal_affine_shift (n : ℕ) (v : Fin n → ℝ) (x : ℝ) :
    (fun z => scalarSpinTerminal (x+coordinateLinear n v z))=
      affineLogPartition (fun b : Bool => spin b*x) (fun b => spin b • coordinateLinear n v) := by
  funext z
  simp only [affineLogPartition,Fintype.sum_bool,spin,scalarSpinTerminal,
    Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul,smul_apply,smul_eq_mul,Real.cosh_eq]
  rw [show -x+ -(coordinateLinear n v z)= -(x+coordinateLinear n v z) by ring]
  congr 1
  ring

theorem scalarPath_square_bound_shift (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (x : ℝ) :
    (∫ z, (coordinateLinear n v z)^2 ∂hierarchyPathLaw n m
      (fun z => scalarSpinTerminal (x+coordinateLinear n v z)) 0) ≤
      2*(∑ i, (v i)^2)+4*(∑ i, (v i)^2)^2 := by
  rw [scalarPath_terminal_affine_shift]
  have H := affineHierarchy_square_bound n m hm hmono (fun b : Bool => spin b*x)
    (fun b => spin b • coordinateLinear n v) (fun i => |v i|) (fun i => abs_nonneg _)
    (fun b i => by cases b <;> simp [spin]) 0 v
  have he : (∑ i, |v i| * |v i|) = ∑ i, (v i)^2 :=
    Finset.sum_congr rfl (fun i _ => by rw [← sq_abs]; ring)
  rw [he] at H
  nlinarith

theorem scalarHierarchyAverage_square_gap_compact (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {T A : ℝ} (hT : 0≤T) (hA : 0≤A) (hv : ∑ i, (v i)^2 ≤ T)
    {x : ℝ} (hx : |x|≤A) :
    scalarHierarchyAverage n m v scalarSpinTerminal (fun z => (scalarMagnetization z)^2) x ≤
      1-1/(2*(Real.cosh (1+2*A^2+4*T+8*T^2))^2) := by
  let μ := hierarchyPathLaw n m (fun z => scalarSpinTerminal (x+coordinateLinear n v z)) 0
  let L := coordinateLinear n v
  let M := 2*A^2+4*T+8*T^2
  let R := 1+M
  have hM : 0≤M := by dsimp [M]; positivity
  have hR : 0<R := by dsimp [R]; positivity
  have hR2 : 2*M ≤ R^2 := by dsimp only [R]; nlinarith [sq_nonneg M]
  have hf : BoundedDerivs (fun z => scalarSpinTerminal (x+L z)) :=
    (scalarSpinTerminal_regular.translate x).compCLM L
  let := hierarchyPathLaw_probability n m _ hf 0
  have hi : Integrable (fun z => (L z)^2) μ := by
    rw [show μ=(fiberGaussian n 0).tilted
      (hierarchyPathLogDensity n m (fun z => scalarSpinTerminal (x+L z))) from
        hierarchyPathLaw_eq_tilted n m _ hf 0]
    exact ((HasExpGrowth.linear L).pow 2).integrable_tilted_fiberGaussian n _
      (hierarchyPathLogDensity_regular n m hf) (L.continuous.pow 2) 0
  have hie : Integrable (fun z => (x+L z)^2) μ := by
    rw [show μ=(fiberGaussian n 0).tilted
      (hierarchyPathLogDensity n m (fun z => scalarSpinTerminal (x+L z))) from
        hierarchyPathLaw_eq_tilted n m _ hf 0]
    exact (((HasExpGrowth.const x).add (HasExpGrowth.linear L)).pow 2).integrable_tilted_fiberGaussian n _
      (hierarchyPathLogDensity_regular n m hf) ((continuous_const.add L.continuous).pow 2) 0
  have hib : Integrable (fun z => (scalarMagnetization (x+L z))^2) μ :=
    hierarchyPathLaw_integrable n m _ _ hf
      (scalarMagnetization_lipschitz.continuous.comp (continuous_const.add L.continuous) |>.pow 2)
      (C:=1) (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; exact scalarMagnetization_sq_le_one _) 0
  have H := integral_mono (((integrable_const (1:ℝ)).sub (hie.div_const (R^2))).const_mul (1/(Real.cosh R)^2))
    ((integrable_const (1:ℝ)).sub hib) (fun z => scalarMagnetization_gap_envelope hR (x+L z))
  change (∫ z, (1/(Real.cosh R)^2)*(1-(x+L z)^2/R^2) ∂μ) ≤ ∫ z, 1-(scalarMagnetization (x+L z))^2 ∂μ at H
  simp only [integral_const_mul,integral_sub (integrable_const _) (hie.div_const _),
    integral_sub (integrable_const _) hib,integral_div,integral_const,probReal_univ,smul_eq_mul,one_mul] at H
  have hs : 0 ≤ ∑ i, (v i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have HM : (∫ z, (L z)^2 ∂μ)≤2*T+4*T^2 :=
    (scalarPath_square_bound_shift n m v hm hmono x).trans (by
      nlinarith [sq_le_sq₀ hs hT |>.mpr hv])
  have HX := integral_mono hie ((integrable_const (2*x^2)).add (hi.const_mul 2))
    (fun z => by nlinarith [sq_nonneg (x-L z)] : ∀ z, (x+L z)^2≤2*x^2+2*(L z)^2)
  change (∫ z, (x+L z)^2 ∂μ) ≤ ∫ z, 2*x^2+2*(L z)^2 ∂μ at HX
  simp only [integral_add (integrable_const _) (hi.const_mul _),integral_const_mul,
    integral_const,probReal_univ,smul_eq_mul,one_mul] at HX
  have hx2 : x^2≤A^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hA).mpr hx
  have HXM : (∫ z, (x+L z)^2 ∂μ)≤M := by dsimp only [M]; linarith
  have Hd : (∫ z, (x+L z)^2 ∂μ)/R^2 ≤ 1/2 := (div_le_iff₀ (sq_pos_of_pos hR)).mpr (by linarith)
  rw [scalarHierarchyAverage_eq_integral n m v (g:=fun z => (scalarMagnetization z)^2) scalarSpinTerminal_regular
    (scalarMagnetization_lipschitz.continuous.pow 2) zero_le_one (fun z => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact scalarMagnetization_sq_le_one z) x]
  have hRdef : 1+2*A^2+4*T+8*T^2=R := by dsimp [R,M]; ring
  rw [hRdef]
  change (∫ z, (scalarMagnetization (x+L z))^2 ∂μ) ≤ 1-1/(2*(Real.cosh R)^2)
  have hc : 0≤1/(Real.cosh R)^2 := by positivity
  have hh : 1/(2*(Real.cosh R)^2)=(1/(Real.cosh R)^2)/2 := by ring
  rw [hh]
  nlinarith [mul_le_mul_of_nonneg_left Hd hc]

end SK.Analytic

end
end

end OAI
