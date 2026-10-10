import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
namespace ScalarConductivity
open MeasureTheory Filter Topology
open scoped ENNReal

variable {ι : Type*}

def sequenceMultiplier (m : ι → ℂ) (C : ℝ) (hC : 0≤C) (hm : ∀ i, ‖m i‖≤C) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun i => m i*f i,
        ((lp.memℓp f).norm.const_smul C).mono (fun i => by
          simpa only [Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hC,
            abs_of_nonneg (norm_nonneg _),norm_mul] using mul_le_mul_of_nonneg_right (hm i) (norm_nonneg (f i)))⟩
      map_add' := fun f g => by ext i; change m i*(f i+g i)=_; exact mul_add _ _ _
      map_smul' := fun r f => by ext i; change m i*(r*f i)=r*(m i*f i); ring }
    C (fun f => by
      have hh := lp.norm_mono (p:=(2:ℝ≥0∞)) (show (2:ℝ≥0∞)≠0 by norm_num)
        (x:=⟨fun i => m i*f i, by
          exact ((lp.memℓp f).norm.const_smul C).mono (fun i => by
            simpa only [Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hC,
              abs_of_nonneg (norm_nonneg _),norm_mul] using mul_le_mul_of_nonneg_right (hm i) (norm_nonneg (f i)))⟩)
        (y:=C • f) (fun i => by
          change ‖m i*f i‖≤‖C • f i‖
          rw [norm_mul,norm_smul,Real.norm_eq_abs,abs_of_nonneg hC]
          exact mul_le_mul_of_nonneg_right (hm i) (norm_nonneg _))
      change ‖(⟨fun i => m i*f i, _⟩ : lp (fun _ : ι => ℂ) 2)‖≤_
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC] using hh)

@[simp] lemma sequenceMultiplier_apply (m : ι → ℂ) (C : ℝ) (hC : 0≤C)
    (hm : ∀ i, ‖m i‖≤C) (f : lp (fun _ : ι => ℂ) 2) (i : ι) :
    sequenceMultiplier m C hC hm f i=m i*f i := rfl

lemma sequenceMultiplier_norm (m : ι → ℂ) (C : ℝ) (hC : 0≤C)
    (hm : ∀ i, ‖m i‖≤C) : ‖sequenceMultiplier m C hC hm‖≤C :=
  LinearMap.mkContinuous_norm_le _ hC _

lemma sequenceMultiplier_one (f : lp (fun _ : ι => ℂ) 2) :
    sequenceMultiplier (fun _ => 1) 1 zero_le_one (fun _ => by simp) f=f := by
  ext i; simp

lemma sequenceMultiplier_coeff_tendsto {α : Type*} {l : Filter α}
    (m : α → ι → ℂ) (C : ℝ) (hC : 0≤C) (hm : ∀ t i, ‖m t i‖≤C)
    (ht : ∀ i, Tendsto (fun t => m t i) l (𝓝 1)) (f : lp (fun _ : ι => ℂ) 2) :
    Tendsto (fun t => sequenceMultiplier (m t) C hC (hm t) f) l (𝓝 f) := by
  have hs : Summable (fun i => ‖f i‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (lp.memℓp f).summable (by norm_num : 0<(2:ℝ≥0∞).toReal)
  have hd : ∀ t i, ‖‖m t i*f i-f i‖^2‖≤(C+1)^2*‖f i‖^2 := by
    intro t i
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    calc
      _ = (‖m t i-1‖*‖f i‖)^2 := by rw [←norm_mul,sub_mul,one_mul]
      _ ≤ ((C+1)*‖f i‖)^2 := by
        gcongr
        exact (norm_sub_le _ _).trans (by simpa using add_le_add_right (hm t i) 1)
      _ = _ := mul_pow _ _ _
  have ht' : Tendsto (fun t => ∑' i, ‖m t i*f i-f i‖^2) l (𝓝 0) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence (g:=fun _ : ι => (0:ℝ)) (hs.mul_left ((C+1)^2))
      (fun i => by simpa using (((ht i).mul_const (f i)).sub_const (f i)).norm.pow 2)
      (Filter.Eventually.of_forall hd)
  have he (t : α) : ∑' i, ‖m t i*f i-f i‖^2 =
      ‖sequenceMultiplier (m t) C hC (hm t) f-f‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,lp.coeFn_sub,Pi.sub_apply,
      sequenceMultiplier_apply] using (lp.norm_rpow_eq_tsum
      (by norm_num : 0<(2:ℝ≥0∞).toReal) (sequenceMultiplier (m t) C hC (hm t) f-f)).symm
  simp only [he] at ht'
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp ht'
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

end ScalarConductivity

end

end OAI
