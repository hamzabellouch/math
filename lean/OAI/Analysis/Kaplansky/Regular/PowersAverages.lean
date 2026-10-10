import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Regular.PowersOperators

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance 2000] Classical.propDecidable Classical.decEq
variable {G : Type*} [Group G]

def conjugateMap (g : G) : Algebra G →ₗ[ℂ] Algebra G where
  toFun x := generator g*x*generator g⁻¹
  map_add' x y := by simp [mul_add,add_mul]
  map_smul' c x := by simp

lemma conjugateMap_val (g : G) (x : Algebra G) :
    (conjugateMap g x).val = left g*x.val*left g⁻¹ := rfl
lemma conjugateMap_norm_le (g : G) (x : Algebra G) :
    ‖conjugateMap g x‖ ≤ ‖x‖ := conjugate_norm_le g x.val
@[simp] lemma conjugateMap_one (g : G) : conjugateMap g (1:Algebra G) = 1 := by
  apply Subtype.ext
  change left g*1*left g⁻¹ = 1
  rw [mul_one,←left_mul,mul_inv_cancel,left_one]
lemma conjugateMap_mul (g h : G) (x : Algebra G) :
    conjugateMap (g*h) x = conjugateMap g (conjugateMap h x) := by
  apply Subtype.ext
  simp only [conjugateMap_val,mul_inv_rev,left_mul,mul_assoc]

lemma conjugateMap_generator (g f : G) :
    conjugateMap g (generator f) = generator (g*f*g⁻¹) := by
  apply Subtype.ext
  change left g*left f*left g⁻¹ = _
  rw [←left_mul,←left_mul]
  rfl

def averageConjugate {N : ℕ} (h : Fin N → G) : Algebra G →ₗ[ℂ] Algebra G :=
  @SMul.smul ℂ (Algebra G →ₗ[ℂ] Algebra G) _ (N:ℂ)⁻¹ (∑ i, conjugateMap (h i))

lemma averageConjugate_apply {N : ℕ} (h : Fin N → G) (x : Algebra G) :
    averageConjugate h x = (N:ℂ)⁻¹ • ∑ i, conjugateMap (h i) x := by
  change (N:ℂ)⁻¹ • ((∑ i, conjugateMap (h i)) : Algebra G →ₗ[ℂ] Algebra G) x = _
  rw [LinearMap.sum_apply]

lemma averageConjugate_norm_le {N : ℕ} (hN : 0<N) (h : Fin N → G) (x : Algebra G) :
    ‖averageConjugate h x‖ ≤ ‖x‖ := by
  rw [averageConjugate_apply,norm_smul,norm_inv,Complex.norm_natCast]
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  calc
    _ ≤ (N:ℝ)⁻¹ * ∑ i, ‖conjugateMap (h i) x‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (le_of_lt (inv_pos.mpr hn))
    _ ≤ (N:ℝ)⁻¹ * ∑ _i : Fin N, ‖x‖ := by gcongr with i; exact conjugateMap_norm_le _ _
    _ = ‖x‖ := by simp [nsmul_eq_mul,ne_of_gt hn]

@[simp] lemma averageConjugate_one {N : ℕ} (hN : 0<N) (h : Fin N → G) :
    averageConjugate h (1:Algebra G) = 1 := by
  rw [averageConjugate_apply]
  simp only [conjugateMap_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [←Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)),one_smul]

lemma averageConjugate_val {N : ℕ} (h : Fin N → G) (x : Algebra G) :
    (averageConjugate h x).val = (N:ℂ)⁻¹ • ∑ i, left (h i)*x.val*left (h i)⁻¹ := by
  rw [averageConjugate_apply]
  change (Algebra G).subtype ((N:ℂ)⁻¹ • ∑ i, conjugateMap (h i) x) = _
  simp only [map_smul,map_sum]
  rfl

lemma mask_left_mask_zero (D : G → Prop) (f : G)
    (hD : ∀ w, D w → ¬D (f*w)) :
    mask (H:=ℂ) D*left f*mask D = 0 := by
  ext x w
  simp only [mul_apply_eq_comp,mask_apply,left_apply,zero_apply,lp.coeFn_zero,Pi.zero_apply]
  by_cases hw : D w
  · have hf : ¬D (f⁻¹*w) := by
      intro hf
      have hk := hD (f⁻¹*w) hf
      simp only [mul_inv_cancel_left] at hk
      exact hk hw
    simp only [ite_eq_left hw,ite_eq_right hf]
  · simp only [ite_eq_right hw]


end KaplanskyConsequences.Regular

end

end OAI
