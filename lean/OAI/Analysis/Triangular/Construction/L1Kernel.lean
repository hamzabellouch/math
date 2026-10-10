import OAI.Analysis.Triangular.Basic

namespace OAI

noncomputable section
open scoped BigOperators Topology lp
namespace AtomicTriangular.L1Kernel
variable {α β : Type*}

lemma l1_norm (a : ℓ¹(α,ℝ)) : ‖a‖ = ∑' i, |a i| := by
  simpa only [ENNReal.toReal_one,Real.rpow_one,one_div_one,Real.norm_eq_abs] using
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (1:ENNReal).toReal) a
lemma l1_summable (a : ℓ¹(α,ℝ)) : Summable (fun i => |a i|) := by
  simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs] using
    a.property.summable (by norm_num : 0 < (1:ENNReal).toReal)

def column (K : β → α → ℝ) (hK : ∀ j, Summable (fun i => |K i j|)) (j : α) : ℓ¹(β,ℝ) :=
  ⟨fun i => K i j, by
    apply (memℓp_gen_iff (by norm_num : 0 < (1:ENNReal).toReal)).mpr
    simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs] using hK j⟩
lemma column_norm (K : β → α → ℝ) (hK : ∀ j, Summable (fun i => |K i j|)) (j : α) :
    ‖column K hK j‖ = ∑' i, |K i j| := l1_norm _

variable (K : β → α → ℝ) (hK : ∀ j, Summable (fun i => |K i j|))
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ j, ∑' i, |K i j| ≤ C)
include C hB
lemma summable_columns (a : ℓ¹(α,ℝ)) :
    Summable (fun j => a j • column K hK j) := by
  apply Summable.of_norm_bounded ((l1_summable a).mul_right C)
  intro j
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((column_norm K hK j).trans_le (hB j)) (abs_nonneg _)

omit C hB in
def applyKernel (a : ℓ¹(α,ℝ)) : ℓ¹(β,ℝ) := ∑' j, a j • column K hK j
lemma applyKernel_norm (a : ℓ¹(α,ℝ)) : ‖applyKernel K hK a‖ ≤ C*‖a‖ := by
  have hs : Summable (fun j => ‖a j • column K hK j‖) :=
    ((l1_summable a).mul_right C).of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((column_norm K hK j).trans_le (hB j)) (abs_nonneg _))
  calc
    _ ≤ ∑' j, ‖a j • column K hK j‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j, |a j| * C := hs.tsum_le_tsum (fun j => by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((column_norm K hK j).trans_le (hB j)) (abs_nonneg _))
      ((l1_summable a).mul_right C)
    _ = C*‖a‖ := by rw [tsum_mul_right,l1_norm,mul_comm]

lemma applyKernel_add (a b : ℓ¹(α,ℝ)) :
    applyKernel K hK (a+b) = applyKernel K hK a + applyKernel K hK b := by
  simp only [applyKernel,lp.coeFn_add,Pi.add_apply,add_smul]
  exact (summable_columns K hK C hB a).tsum_add (summable_columns K hK C hB b)
lemma applyKernel_smul (r : ℝ) (a : ℓ¹(α,ℝ)) :
    applyKernel K hK (r • a) = r • applyKernel K hK a := by
  simp only [applyKernel,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,mul_smul]
  exact (summable_columns K hK C hB a).tsum_const_smul r

def operator : ℓ¹(α,ℝ) →L[ℝ] ℓ¹(β,ℝ) :=
  LinearMap.mkContinuous
    { toFun := applyKernel K hK
      map_add' := applyKernel_add K hK C hB
      map_smul' := fun r a => applyKernel_smul K hK C hB r a }
    C (applyKernel_norm K hK C hB)
include hC in
lemma operator_norm : ‖operator K hK C hB‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (applyKernel_norm K hK C hB)
end AtomicTriangular.L1Kernel
end

end OAI
