import Mathlib
import OAI.Analysis.HardSphere.Cutoffs.RegularizationWeight

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open ContinuousLinearMap Filter
open scoped Topology

lemma heatScalar_eq_exp {t x : ℝ} (ht : 0<t) (hx : 0<x) :
    heatScalar t x=Real.exp (-t*(x⁻¹-1)) := by
  rw [heatScalar_of_pos ht hx]
  congr 1
  field_simp
  ring

def generatorScalar (t x : ℝ) : ℝ := t⁻¹*x*(1-heatScalar t x)

lemma generatorScalar_bounds {t x : ℝ} (ht : 0<t) (hx : x∈Set.Icc (0:ℝ) 1) :
    0≤generatorScalar t x ∧ generatorScalar t x≤1-x := by
  rcases eq_or_lt_of_le hx.1 with hzero | hx0
  · subst x
    simp [generatorScalar]
  have hq : 0≤x⁻¹-1 := sub_nonneg.mpr ((one_le_inv₀ hx0).mpr hx.2)
  have hh : heatScalar t x=Real.exp (-t*(x⁻¹-1)) := heatScalar_eq_exp ht hx0
  have he1 : Real.exp (-t*(x⁻¹-1))≤1 := by
    simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg ht.le hq))
  have he2 := Real.add_one_le_exp (-t*(x⁻¹-1))
  have hid : t⁻¹*x*(t*(x⁻¹-1))=1-x := by field_simp
  rw [generatorScalar,hh]
  constructor
  · positivity
  · calc
      _ ≤ t⁻¹*x*(t*(x⁻¹-1)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := hid

lemma generatorScalar_range_error {t x : ℝ} (ht : 0<t) (hx : x∈Set.Icc (0:ℝ) 1) :
    |(generatorScalar t x-(1-x))*x|≤t := by
  have hg := generatorScalar_bounds ht hx
  rcases eq_or_lt_of_le hx.1 with hz | hx0
  · subst x
    simpa using ht.le
  let y := t*(x⁻¹-1)
  have hy : 0≤y := mul_nonneg ht.le (sub_nonneg.mpr ((one_le_inv₀ hx0).mpr hx.2))
  have hyx : y*x=t*(1-x) := by dsimp [y]; field_simp
  rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hg.2) hx.1)]
  by_cases hy1 : y≤1
  · have he := Real.abs_exp_sub_one_sub_id_le (x := -y) (by simpa only [abs_neg,abs_of_nonneg hy] using hy1)
    have herr : -(generatorScalar t x-(1-x))*x = x^2*t⁻¹*(Real.exp (-y)-1+y) := by
      rw [generatorScalar,heatScalar_eq_exp ht hx0]
      dsimp [y]
      field_simp
      ring
    have heq : x^2*t⁻¹*y^2=t*(1-x)^2 := by
      have ht0 := ht.ne'
      calc
        _ = t⁻¹*(y*x)^2 := by ring
        _ = t⁻¹*(t*(1-x))^2 := by rw [hyx]
        _ = _ := by field_simp
    calc
      _ = -(generatorScalar t x-(1-x))*x := by ring
      _ = _ := herr
      _ ≤ x^2*t⁻¹*y^2 := mul_le_mul_of_nonneg_left
        (by simpa only [sub_neg_eq_add,neg_sq] using (le_abs_self _).trans he) (by positivity)
      _ = t*(1-x)^2 := heq
      _ ≤ t := by nlinarith [mul_nonneg ht.le (mul_nonneg hx.1 (sub_nonneg.mpr hx.2))]
  · have hy1' : 1≤y := le_of_lt (lt_of_not_ge hy1)
    have hxt : x≤t := by nlinarith [mul_le_mul_of_nonneg_right hy1' hx.1]
    nlinarith [mul_nonneg hg.1 hx.1,sq_nonneg x]

section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] [Nontrivial F]
local instance : Algebra ℝ (F →L[ℂ] F) := Algebra.restrictScalars ℝ ℂ _

def generatorOperator (R : F →L[ℂ] F) (t : ℝ) : F →L[ℂ] F :=
  cfc (p := IsSelfAdjoint) (generatorScalar t) R

lemma generatorScalar_continuous (t : ℝ) : Continuous (generatorScalar t) :=
  (continuous_const.mul continuous_id).mul (continuous_const.sub (heatScalar_smooth t).continuous)

omit [Nontrivial F] in
lemma generatorOperator_eq {R : F →L[ℂ] F} (hRp : R.IsPositive) (t : ℝ) :
    generatorOperator R t = t⁻¹ • ((1-cfc (p := IsSelfAdjoint) (heatScalar t) R)*R) := by
  have hf : generatorScalar t = fun x : ℝ ↦ t⁻¹*((1-heatScalar t x)*x) := by
    funext x; dsimp [generatorScalar]; ring
  have hhc := (heatScalar_smooth t).continuous
  rw [generatorOperator,hf,
    cfc_const_mul t⁻¹ (fun x:ℝ ↦ (1-heatScalar t x)*x) R
      ((continuous_const.sub hhc).mul continuous_id).continuousOn,
    cfc_mul (fun x:ℝ ↦ 1-heatScalar t x) (fun x:ℝ ↦ x) R
      (continuous_const.sub hhc).continuousOn continuous_id.continuousOn,
    cfc_sub (fun _:ℝ ↦ 1) (heatScalar t) R continuousOn_const hhc.continuousOn,
    cfc_const 1 R hRp.isSelfAdjoint,cfc_id' ℝ R hRp.isSelfAdjoint]
  simp only [map_one]

lemma generatorOperator_norm_le {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    {t : ℝ} (ht : 0<t) : ‖generatorOperator R t‖≤1 := by
  apply norm_cfc_le zero_le_one
  intro x hx
  have hs := positive_contraction_spectrum hRp hRn hx
  have hg := generatorScalar_bounds ht hs
  simpa only [Real.norm_eq_abs,abs_of_nonneg hg.1] using hg.2.trans (by linarith [hs.1])

lemma one_sub_positive_contraction_norm_le {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1) :
    ‖1-R‖≤1 := by
  have he : (1:F→L[ℂ] F)-R=cfc (p := IsSelfAdjoint) (fun x:ℝ ↦ 1-x) R := by
    rw [cfc_sub (fun _:ℝ ↦ 1) (fun x:ℝ ↦ x) R continuousOn_const continuous_id.continuousOn,
      cfc_const 1 R hRp.isSelfAdjoint,cfc_id' ℝ R hRp.isSelfAdjoint]
    simp only [map_one]
  rw [he]
  apply norm_cfc_le zero_le_one
  intro x hx
  have hs := positive_contraction_spectrum hRp hRn hx
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hs.2)] using (show 1-x≤1 by linarith [hs.1])

lemma generatorOperator_range_error {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1)
    {t : ℝ} (ht : 0<t) : ‖(generatorOperator R t-(1-R))*R‖≤t := by
  have he : (generatorOperator R t-(1-R))*R =
      cfc (p := IsSelfAdjoint) (fun x:ℝ ↦ (generatorScalar t x-(1-x))*x) R := by
    rw [cfc_mul (fun x:ℝ ↦ generatorScalar t x-(1-x)) (fun x:ℝ ↦ x) R
      (((generatorScalar_continuous t).sub (continuous_const.sub continuous_id)).continuousOn)
        continuous_id.continuousOn,
      cfc_sub (generatorScalar t) (fun x:ℝ ↦ 1-x) R (generatorScalar_continuous t).continuousOn
        (continuous_const.sub continuous_id).continuousOn,
      cfc_sub (fun _:ℝ ↦ 1) (fun x:ℝ ↦ x) R continuousOn_const continuous_id.continuousOn,
      cfc_const 1 R hRp.isSelfAdjoint,cfc_id' ℝ R hRp.isSelfAdjoint]
    simp only [generatorOperator,map_one]
  rw [he]
  exact norm_cfc_le ht.le (fun x hx ↦ by
    simpa only [Real.norm_eq_abs] using generatorScalar_range_error ht (positive_contraction_spectrum hRp hRn hx))

lemma generatorOperator_tendsto {ι : Type*} {l : Filter ι} {d : ι→ℝ}
    (hd : ∀ i, 0<d i) (ht : Tendsto d l (𝓝 0))
    {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1) (hRd : DenseRange R) (f : F) :
    Tendsto (fun i ↦ generatorOperator R (d i) f) l (𝓝 ((1-R) f)) := by
  have hC (i : ι) (u : F) : ‖generatorOperator R (d i) u‖≤‖u‖ := by
    exact (le_opNorm _ _).trans (by simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (generatorOperator_norm_le hRp hRn (hd i)) (norm_nonneg u)))
  have hRange : ∀ u : F, Tendsto (fun i ↦ generatorOperator R (d i) (R u)) l (𝓝 ((1-R) (R u))) := by
    intro u
    rw [← tendsto_sub_nhds_zero_iff,tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun i ↦ d i*‖u‖) (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ ?_
    · exact Eventually.of_forall fun i ↦ by
        change ‖((generatorOperator R (d i)-(1-R))*R) u‖≤_
        exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
          (generatorOperator_range_error hRp hRn (hd i)) (norm_nonneg u))
    · simpa using ht.mul_const ‖u‖
  have hB (u : F) : ‖(1-R) u‖≤‖u‖ := by
    exact (le_opNorm _ _).trans (by simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (one_sub_positive_contraction_norm_le hRp hRn) (norm_nonneg u)))
  exact strong_contraction_limit_of_dense (fun i ↦ generatorOperator R (d i)) (1-R) hC hB R hRd hRange f

lemma heat_difference_resolvent_tendsto {ι : Type*} {l : Filter ι} {d : ι→ℝ}
    (hd : ∀ i, 0<d i) (ht : Tendsto d l (𝓝 0))
    {R : F →L[ℂ] F} (hRp : R.IsPositive) (hRn : ‖R‖≤1) (hRd : DenseRange R) (f : F) :
    Tendsto (fun i ↦ ((d i)⁻¹ : ℂ) • (R f-cfc (p := IsSelfAdjoint) (heatScalar (d i)) R (R f)))
      l (𝓝 (f-R f)) := by
  have h := generatorOperator_tendsto hd ht hRp hRn hRd f
  simp only [generatorOperator_eq hRp,smul_apply,mul_apply_eq_comp,
    sub_apply,one_apply_eq_self,
    RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.ofReal_inv] at h
  exact h

end
end HardSphere

end
end
end
end
end
end

end OAI
