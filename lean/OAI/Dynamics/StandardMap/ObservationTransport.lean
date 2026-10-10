import OAI.Dynamics.StandardMap.TransferCore

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma transferStep_difference_bound (v w : ℝ) : ‖transferStep v-transferStep w‖ ≤ |v-w| := by
  apply (transferStep v-transferStep w).opNorm_le_bound (abs_nonneg _)
  intro z
  have he : (transferStep v-transferStep w) z=((v-w)*z.re : ℝ) := by
    apply Complex.ext <;> simp only [sub_apply,Complex.sub_re,Complex.sub_im,
      transferStep_re,transferStep_im,Complex.ofReal_re,Complex.ofReal_im] <;> ring
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg _)

lemma transferProduct_difference_bound (v w : ℕ → ℝ) (M δ : ℝ) (n : ℕ)
    (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (hv : ∀ i, 1 ≤ i → i ≤ n → |v i|+1 ≤ M)
    (hw : ∀ i, 1 ≤ i → i ≤ n → |w i|+1 ≤ M)
    (hd : ∀ i, 1 ≤ i → i ≤ n → |v i-w i| ≤ δ) :
    ‖transferProduct v n-transferProduct w n‖ ≤ (n:ℝ)*δ*M^n := by
  induction n with
  | zero => simp [transferProduct]
  | succ n ih =>
    have hvn : ‖transferProduct v n‖ ≤ M^n :=
      (transferProduct_norm_bounds v M n (by linarith) (fun i hi hin => hv i hi (by omega))).2
    have hwn : ‖transferStep (w (n+1))‖ ≤ M := (transferStep_norm _).trans (hw _ (by omega) le_rfl)
    have hdn := (transferStep_difference_bound (v (n+1)) (w (n+1))).trans (hd _ (by omega) le_rfl)
    have hpn := ih (fun i hi hin => hv i hi (by omega)) (fun i hi hin => hw i hi (by omega))
      (fun i hi hin => hd i hi (by omega))
    have he : transferProduct v (n+1)-transferProduct w (n+1)=
        (transferStep (v (n+1))-transferStep (w (n+1))).comp (transferProduct v n)+
        (transferStep (w (n+1))).comp (transferProduct v n-transferProduct w n) := by
      apply ContinuousLinearMap.ext
      intro z
      simp only [transferProduct,sub_apply,add_apply,
        ContinuousLinearMap.comp_apply,map_sub]
      abel
    rw [he]
    calc
      _ ≤ ‖(transferStep (v (n+1))-transferStep (w (n+1))).comp (transferProduct v n)‖+
          ‖(transferStep (w (n+1))).comp (transferProduct v n-transferProduct w n)‖ := norm_add_le _ _
      _ ≤ δ*M^n+M*((n:ℝ)*δ*M^n) := add_le_add
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hdn hvn (norm_nonneg _) hδ))
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hwn hpn (norm_nonneg _) (by linarith)))
      _ ≤ δ*M^(n+1)+M*((n:ℝ)*δ*M^n) := by
        exact add_le_add (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hM (Nat.le_succ n)) hδ) le_rfl
      _ = _ := by rw [pow_succ]; push_cast; ring

lemma log_lipschitz_above_one (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.log x-Real.log y| ≤ |x-y| := by
  have hh := (convex_Ici (1:ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.log) (f' := fun x => x⁻¹) (C := 1)
    (fun z hz => (Real.hasDerivAt_log (by have : 1 ≤ z := hz; linarith : z ≠ 0)).hasDerivWithinAt)
    (fun z hz => by
      change 1 ≤ z at hz
      change |z⁻¹| ≤ 1
      rw [abs_of_nonneg (inv_nonneg.mpr (by linarith))]
      exact inv_le_one_of_one_le₀ hz) hy hx
  simpa only [Real.norm_eq_abs,one_mul] using hh

lemma transfer_log_difference_bound (v w : ℕ → ℝ) (M δ : ℝ) (n : ℕ)
    (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (hv : ∀ i, 1 ≤ i → i ≤ n → |v i|+1 ≤ M)
    (hw : ∀ i, 1 ≤ i → i ≤ n → |w i|+1 ≤ M)
    (hd : ∀ i, 1 ≤ i → i ≤ n → |v i-w i| ≤ δ) :
    |Real.log ‖transferProduct v n‖-Real.log ‖transferProduct w n‖| ≤ (n:ℝ)*δ*M^n := by
  exact (log_lipschitz_above_one _ _
    (transferProduct_norm_bounds v M n (by linarith) hv).1
    (transferProduct_norm_bounds w M n (by linarith) hw).1).trans
    ((abs_norm_sub_norm_le _ _).trans (transferProduct_difference_bound v w M δ n hM hδ hv hw hd))
end StandardMapEntropy

end OAI
