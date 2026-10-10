import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Complex
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E]
  [IsScalarTower ℝ ℂ E]

lemma complex_smul_split (c : ℂ) (x : E) :
    c • x = c.re • x + c.im • (I • x) := by
  calc
    c • x = ((c.re:ℂ)+(c.im:ℂ)*I) • x := by rw [re_add_im]
    _ = (c.re:ℂ) • x + (c.im:ℂ) • (I • x) := by rw [add_smul,mul_smul]
    _ = _ := congrArg₂ (fun u v : E => u+v)
      (RCLike.real_smul_eq_coe_smul (K := ℂ) c.re x).symm
      (RCLike.real_smul_eq_coe_smul (K := ℂ) c.im (I • x)).symm

def complexLinear (f : E →ₗ[ℝ] ℂ) (hi : ∀ x, f (I • x) = I*f x) : E →ₗ[ℂ] ℂ where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    rw [complex_smul_split,map_add,map_smul,map_smul,hi]
    simp only [RingHom.id_apply,smul_eq_mul,Complex.real_smul]
    conv_rhs => rw [← re_add_im c]
    ring

def holPart (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z w : E) : ℂ :=
  ((B z w-B (I • z) (I • w))/2 : ℝ) -
    I*(( (B (I • z) w+B z (I • w))/2 : ℝ) : ℂ)

def hermPart (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z w : E) : ℂ :=
  ((B z w+B (I • z) (I • w))/2 : ℝ) +
    I*(( (B z (I • w)-B (I • z) w)/2 : ℝ) : ℂ)

omit [IsScalarTower ℝ ℂ E] in
lemma holPart_add_left (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y z : E) :
    holPart B (x+y) z = holPart B x z+holPart B y z := by
  simp only [holPart,smul_add,map_add,LinearMap.add_apply,ofReal_div,
    ofReal_sub,ofReal_add,ofReal_ofNat]
  ring

omit [IsScalarTower ℝ ℂ E] in
lemma holPart_add_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y z : E) :
    holPart B x (y+z) = holPart B x y+holPart B x z := by
  simp only [holPart,smul_add,map_add,ofReal_div,ofReal_sub,ofReal_add,ofReal_ofNat]
  ring

lemma holPart_real_left (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (r : ℝ) (x y : E) :
    holPart B (r • x) y = r • holPart B x y := by
  simp only [holPart,smul_comm I r,map_smul,LinearMap.smul_apply,smul_eq_mul,
    ofReal_div,ofReal_sub,ofReal_add,ofReal_mul,ofReal_ofNat,Complex.real_smul]
  ring

lemma holPart_real_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (r : ℝ) (x y : E) :
    holPart B x (r • y) = r • holPart B x y := by
  simp only [holPart,smul_comm I r,map_smul,smul_eq_mul,
    ofReal_div,ofReal_sub,ofReal_add,ofReal_mul,ofReal_ofNat,Complex.real_smul]
  ring

omit [IsScalarTower ℝ ℂ E] in
lemma holPart_I_left (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y : E) :
    holPart B (I • x) y = I*holPart B x y := by
  simp only [holPart,smul_smul,I_mul_I,neg_smul,one_smul,map_neg,
    LinearMap.neg_apply,ofReal_div,ofReal_sub,ofReal_add,ofReal_neg,ofReal_ofNat]
  linear_combination ((B (I • x) y : ℂ)+(B x (I • y) : ℂ))/2*I_sq

omit [IsScalarTower ℝ ℂ E] in
lemma holPart_I_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y : E) :
    holPart B x (I • y) = I*holPart B x y := by
  simp only [holPart,smul_smul,I_mul_I,neg_smul,one_smul,map_neg,
    ofReal_div,ofReal_sub,ofReal_add,ofReal_neg,ofReal_ofNat]
  linear_combination ((B (I • x) y : ℂ)+(B x (I • y) : ℂ))/2*I_sq

lemma holPart_smul_left (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (x y : E) :
    holPart B (c • x) y = c*holPart B x y := by
  rw [complex_smul_split,holPart_add_left,holPart_real_left,holPart_real_left,holPart_I_left]
  simp only [Complex.real_smul]
  conv_rhs => rw [← re_add_im c]
  ring

lemma holPart_smul_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (x y : E) :
    holPart B x (c • y) = c*holPart B x y := by
  rw [complex_smul_split,holPart_add_right,holPart_real_right,holPart_real_right,holPart_I_right]
  simp only [Complex.real_smul]
  conv_rhs => rw [← re_add_im c]
  ring

def holBilinear (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : E →ₗ[ℂ] E →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (holPart B) (holPart_add_left B) (holPart_smul_left B)
    (holPart_add_right B) (holPart_smul_right B)

omit [IsScalarTower ℝ ℂ E] in
lemma hermPart_add_left (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y z : E) :
    hermPart B (x+y) z = hermPart B x z+hermPart B y z := by
  simp only [hermPart,smul_add,map_add,LinearMap.add_apply,ofReal_div,
    ofReal_sub,ofReal_add,ofReal_ofNat]
  ring

omit [IsScalarTower ℝ ℂ E] in
lemma hermPart_add_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y z : E) :
    hermPart B x (y+z) = hermPart B x y+hermPart B x z := by
  simp only [hermPart,smul_add,map_add,ofReal_div,ofReal_sub,ofReal_add,ofReal_ofNat]
  ring

lemma hermPart_real_left (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (r : ℝ) (x y : E) :
    hermPart B (r • x) y = r • hermPart B x y := by
  simp only [hermPart,smul_comm I r,map_smul,LinearMap.smul_apply,smul_eq_mul,
    ofReal_div,ofReal_sub,ofReal_add,ofReal_mul,ofReal_ofNat,Complex.real_smul]
  ring

lemma hermPart_real_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (r : ℝ) (x y : E) :
    hermPart B x (r • y) = r • hermPart B x y := by
  simp only [hermPart,smul_comm I r,map_smul,smul_eq_mul,
    ofReal_div,ofReal_sub,ofReal_add,ofReal_mul,ofReal_ofNat,Complex.real_smul]
  ring

omit [IsScalarTower ℝ ℂ E] in
lemma hermPart_I_left (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y : E) :
    hermPart B (I • x) y = I*hermPart B x y := by
  simp only [hermPart,smul_smul,I_mul_I,neg_smul,one_smul,map_neg,
    LinearMap.neg_apply,ofReal_div,ofReal_sub,ofReal_add,ofReal_neg,ofReal_ofNat]
  linear_combination ((B (I • x) y : ℂ)-(B x (I • y) : ℂ))/2*I_sq

omit [IsScalarTower ℝ ℂ E] in
lemma hermPart_I_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y : E) :
    hermPart B x (I • y) = -I*hermPart B x y := by
  simp only [hermPart,smul_smul,I_mul_I,neg_smul,one_smul,map_neg,
    ofReal_div,ofReal_sub,ofReal_add,ofReal_neg,ofReal_ofNat]
  linear_combination ((B x (I • y) : ℂ)-(B (I • x) y : ℂ))/2*I_sq

lemma hermPart_smul_left (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (x y : E) :
    hermPart B (c • x) y = c*hermPart B x y := by
  rw [complex_smul_split,hermPart_add_left,hermPart_real_left,hermPart_real_left,hermPart_I_left]
  simp only [Complex.real_smul]
  conv_rhs => rw [← re_add_im c]
  ring

lemma hermPart_smul_right (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (x y : E) :
    hermPart B x (c • y) = (starRingEnd ℂ c)*hermPart B x y := by
  rw [complex_smul_split,hermPart_add_right,hermPart_real_right,hermPart_real_right,hermPart_I_right]
  simp only [Complex.real_smul]
  conv_rhs => rw [← re_add_im c]
  simp only [map_add,map_mul,conj_ofReal,conj_I]
  ring

omit [IsScalarTower ℝ ℂ E] in
lemma hermPart_conj (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hs : ∀ x y, B x y = B y x)
    (x y : E) : hermPart B y x = star (hermPart B x y) := by
  apply Complex.ext <;> simp [hermPart,hs y x,hs (I • y) (I • x),hs y (I • x),hs (I • y) x]
  ring

omit [IsScalarTower ℝ ℂ E] in
lemma quadratic_decomposition (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x : E) :
    B x x = (hermPart B x x).re + (holPart B x x).re := by
  simp [hermPart,holPart]
  ring

omit [IsScalarTower ℝ ℂ E] in
lemma hermPart_diag_real (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hs : ∀ x y, B x y = B y x)
    (x : E) : (hermPart B x x).im = 0 := by
  simp [hermPart,hs (I • x) x]

lemma hermPart_smul_both (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (x y : E) :
    hermPart B (c • x) (c • y) = (Complex.normSq c : ℂ)*hermPart B x y := by
  rw [hermPart_smul_left,hermPart_smul_right,← mul_assoc,Complex.mul_conj]

lemma holPart_smul_both (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (x y : E) :
    holPart B (c • x) (c • y) = c^2*holPart B x y := by
  rw [holPart_smul_left,holPart_smul_right]
  ring

omit [IsScalarTower ℝ ℂ E] in
lemma hermPart_zero (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : hermPart B 0 0 = 0 := by
  simp [hermPart]

def symmetrize (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  (1/2 : ℝ) • (B+B.flip)

omit [IsScalarTower ℝ ℂ E] [Module ℂ E] in
lemma symmetrize_symm (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x y : E) :
    symmetrize B x y = symmetrize B y x := by
  simp [symmetrize,add_comm]

omit [IsScalarTower ℝ ℂ E] [Module ℂ E] in
lemma symmetrize_diag (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x : E) :
    symmetrize B x x = B x x := by
  simp [symmetrize]
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]

def holContinuous (B : F →ₗ[ℝ] F →ₗ[ℝ] ℝ) : F →L[ℂ] F →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (holBilinear B))

lemma holPart_analytic (B : F →ₗ[ℝ] F →ₗ[ℝ] ℝ) (z : F) :
    AnalyticAt ℂ (fun x => holPart B x x) z := by
  exact (holContinuous B |>.analyticAt_bilinear (z,z)).comp (f := fun x : F => (x,x))
    (analyticAt_id.prod analyticAt_id)

omit [FiniteDimensional ℂ F] in
lemma hermPart_unit (B : F →ₗ[ℝ] F →ₗ[ℝ] ℝ) (c : ℂ) (hc : ‖c‖ = 1) (x y : F) :
    hermPart B (c • x) (c • y) = hermPart B x y := by
  rw [hermPart_smul_both,Complex.normSq_eq_norm_sq,hc]
  norm_num

end Release061.Hermitian

end

end OAI
