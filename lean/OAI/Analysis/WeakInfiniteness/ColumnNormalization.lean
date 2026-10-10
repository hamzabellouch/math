import Mathlib
import OAI.Analysis.WeakInfiniteness.Intertwining

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def columnMetricFunction (τ s : ℝ) : ℝ := (max τ (Real.sqrt s))⁻¹

def columnCoreFunction (τ s : ℝ) : ℝ := max (Real.sqrt s-τ) 0

lemma continuous_columnMetricFunction {τ : ℝ} (hτ : 0 < τ) :
    Continuous (columnMetricFunction τ) := by
  apply Continuous.inv₀ (continuous_const.max Real.continuous_sqrt)
  intro s
  exact ne_of_gt (lt_of_lt_of_le hτ (le_max_left _ _))

lemma continuous_columnCoreFunction (τ : ℝ) : Continuous (columnCoreFunction τ) := by
  unfold columnCoreFunction
  fun_prop

lemma columnMetricFunction_nonneg {τ : ℝ} (hτ : 0 < τ) (s : ℝ) :
    0 ≤ columnMetricFunction τ s := inv_nonneg.mpr (hτ.le.trans (le_max_left _ _))

lemma columnMetricFunction_bound {τ : ℝ} (hτ : 0 < τ) (s : ℝ) :
    columnMetricFunction τ s ≤ τ⁻¹ :=
  inv_anti₀ hτ (le_max_left _ _)

lemma columnMetricFunction_scalar {τ s : ℝ} (hτ : 0 < τ) (hs : 0 ≤ s) :
    0 ≤ s*(columnMetricFunction τ s)^2 ∧ s*(columnMetricFunction τ s)^2 ≤ 1 ∧
      (s*(columnMetricFunction τ s)^2)*columnCoreFunction τ s=columnCoreFunction τ s := by
  have hm : 0 < max τ (Real.sqrt s) := hτ.trans_le (le_max_left _ _)
  have he : s*(columnMetricFunction τ s)^2=(Real.sqrt s/max τ (Real.sqrt s))^2 := by
    rw [div_pow,Real.sq_sqrt hs]
    simp only [columnMetricFunction,div_eq_mul_inv,inv_pow]
  have hr0 : 0 ≤ Real.sqrt s/max τ (Real.sqrt s) := div_nonneg (Real.sqrt_nonneg _) hm.le
  have hr1 : Real.sqrt s/max τ (Real.sqrt s) ≤ 1 := (div_le_one₀ hm).mpr (le_max_right _ _)
  refine ⟨by positivity,by rw [he]; nlinarith,?_⟩
  by_cases h : Real.sqrt s ≤ τ
  · have hc : columnCoreFunction τ s=0 := max_eq_right (sub_nonpos.mpr h)
    rw [hc,mul_zero]
  · have hp : 0 < Real.sqrt s := hτ.trans (lt_of_not_ge h)
    have hmax : max τ (Real.sqrt s)=Real.sqrt s := max_eq_right (le_of_not_ge h)
    rw [he,hmax,div_self (ne_of_gt hp),one_pow,one_mul]

lemma column_left_normalization (D : B) {τ : ℝ} (hτ : 0 < τ) :
    let F := cfc (columnMetricFunction τ) (D*star D)
    let p := F*D
    let h := cfc (columnCoreFunction τ) (star D*D)
    ‖F‖ ≤ τ⁻¹ ∧ ‖p‖ ≤ 1 ∧ 0 ≤ h ∧ star p*p*h=h := by
  dsimp only
  let f := columnMetricFunction τ
  let G := cfc f (star D*D)
  have hf := continuous_columnMetricFunction hτ
  have hc := continuous_columnCoreFunction τ
  have hF : ‖cfc f (D*star D)‖ ≤ τ⁻¹ := by
    apply norm_cfc_le (by positivity)
    intro s _
    rw [Real.norm_eq_abs,abs_of_nonneg (columnMetricFunction_nonneg hτ s)]
    exact columnMetricFunction_bound hτ s
  have hG : IsSelfAdjoint G := cfc_predicate _ _
  have hpair : star (cfc f (D*star D)*D)*(cfc f (D*star D)*D)=
      cfc (fun s : ℝ => s*(f s)^2) (star D*D) := by
    rw [cfc_star_mul_intertwine D f hf,star_mul,hG.star_eq]
    have hfun : cfc (fun s : ℝ => s*(f s)^2) (star D*D)=(star D*D)*G*G := by
      rw [show (fun s : ℝ => s*(f s)^2)=(fun s : ℝ => s*f s*f s) by ext; ring]
      rw [cfc_mul (fun s : ℝ => s*f s) f _ (continuous_id.mul hf).continuousOn hf.continuousOn,
        cfc_mul (fun s : ℝ => s) f _ continuous_id.continuousOn hf.continuousOn,cfc_id' ℝ (star D*D) (IsSelfAdjoint.star_mul_self D)]
    rw [hfun]
    have hcomm : Commute G (star D*D) := (Commute.refl (star D*D)).cfc_real f
    calc
      G*star D*(D*G)=G*(star D*D)*G := by simp only [mul_assoc]
      _=(star D*D)*G*G := by rw [hcomm.eq]
  have hp : ‖cfc f (D*star D)*D‖ ≤ 1 := by
    have hn : ‖cfc (fun s : ℝ => s*(f s)^2) (star D*D)‖ ≤ 1 := by
      apply norm_cfc_le (by positivity)
      intro s hs
      have h := columnMetricFunction_scalar hτ (spectrum_nonneg_of_nonneg (star_mul_self_nonneg D) hs)
      rw [Real.norm_eq_abs,abs_of_nonneg h.1]
      exact h.2.1
    rw [← hpair,CStarRing.norm_star_mul_self] at hn
    nlinarith [norm_nonneg (cfc f (D*star D)*D)]
  refine ⟨hF,hp,cfc_nonneg (fun s _ => le_max_right _ _),?_⟩
  rw [hpair,← cfc_mul (fun s : ℝ => s*(f s)^2) (columnCoreFunction τ) _
    (continuous_id.mul (hf.pow 2)).continuousOn hc.continuousOn]
  apply cfc_congr
  intro s hs
  exact (columnMetricFunction_scalar hτ (spectrum_nonneg_of_nonneg (star_mul_self_nonneg D) hs)).2.2

end

end

end WeakPureInfiniteness
end

end OAI
