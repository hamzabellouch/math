import OAI.Dynamics.StandardMap.PlaneTransfer

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

noncomputable def transferStep (v : ℝ) : ℂ →L[ℝ] ℂ :=
  { toLinearMap :=
      { toFun := fun z => ⟨v*z.re-z.im,z.re⟩
        map_add' := by intro z w; apply Complex.ext <;> simp ; ring
        map_smul' := by intro t z; apply Complex.ext <;> simp ; ring }
    cont := by
      exact Complex.equivRealProdCLM.symm.continuous.comp
        (((continuous_const.mul Complex.continuous_re).sub Complex.continuous_im).prodMk Complex.continuous_re) }
@[simp] lemma transferStep_re (v : ℝ) (z : ℂ) : (transferStep v z).re = v*z.re-z.im := rfl
@[simp] lemma transferStep_im (v : ℝ) (z : ℂ) : (transferStep v z).im = z.re := rfl
noncomputable def transferStepInv (v : ℝ) : ℂ →L[ℝ] ℂ :=
  { toLinearMap :=
      { toFun := fun z => ⟨z.im,v*z.im-z.re⟩
        map_add' := by intro z w; apply Complex.ext <;> simp ; ring
        map_smul' := by intro t z; apply Complex.ext <;> simp ; ring }
    cont := by
      exact Complex.equivRealProdCLM.symm.continuous.comp
        (Complex.continuous_im.prodMk ((continuous_const.mul Complex.continuous_im).sub Complex.continuous_re)) }
@[simp] lemma transferStepInv_re (v : ℝ) (z : ℂ) : (transferStepInv v z).re = z.im := rfl
@[simp] lemma transferStepInv_im (v : ℝ) (z : ℂ) : (transferStepInv v z).im = v*z.im-z.re := rfl
lemma transferStep_area (v : ℝ) : PlaneAreaPreserving (transferStep v) := by
  intro z w; simp [wedge]; ring
lemma transferStepInv_area (v : ℝ) : PlaneAreaPreserving (transferStepInv v) := by
  intro z w; simp [wedge]; ring
@[simp] lemma transferStep_inv (v : ℝ) (z : ℂ) : transferStep v (transferStepInv v z)=z := by
  apply Complex.ext <;> simp
@[simp] lemma transferStepInv_inv (v : ℝ) (z : ℂ) : transferStepInv v (transferStep v z)=z := by
  apply Complex.ext <;> simp
lemma transferStep_norm (v : ℝ) : ‖transferStep v‖ ≤ |v|+1 := by
  apply (transferStep v).opNorm_le_bound (by positivity)
  intro z
  have hdecomp : transferStep v z = (v*z.re : ℝ) + quarterTurn z := by
    apply Complex.ext <;> simp [quarterTurn] ; ring
  rw [hdecomp]
  calc
    _ ≤ ‖((v*z.re : ℝ):ℂ)‖+‖quarterTurn z‖ := norm_add_le _ _
    _ ≤ |v| *‖z‖+‖z‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,norm_quarterTurn]
      simpa only [add_comm] using add_le_add_right (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg v)) ‖z‖
    _ = _ := by ring
lemma transferStepInv_norm (v : ℝ) : ‖transferStepInv v‖ ≤ |v|+1 := by
  rw [← (transferStep_area v).norm_inverse (transferStepInv_area v) (transferStep_inv v) (transferStepInv_inv v)]
  exact transferStep_norm v

noncomputable def transferProduct (v : ℕ → ℝ) : ℕ → (ℂ →L[ℝ] ℂ)
  | 0 => ContinuousLinearMap.id ℝ ℂ
  | n+1 => (transferStep (v (n+1))).comp (transferProduct v n)
noncomputable def transferProductInv (v : ℕ → ℝ) : ℕ → (ℂ →L[ℝ] ℂ)
  | 0 => ContinuousLinearMap.id ℝ ℂ
  | n+1 => (transferProductInv v n).comp (transferStepInv (v (n+1)))
lemma transferProduct_pair (v : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    transferProduct v n ⟨b,a⟩ = ⟨linearSolution v a b (n+1),linearSolution v a b n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [transferProduct,ContinuousLinearMap.comp_apply,ih]
    apply Complex.ext <;> simp only [transferStep_re,transferStep_im,linearSolution_step]
lemma transferProduct_area (v : ℕ → ℝ) (n : ℕ) : PlaneAreaPreserving (transferProduct v n) := by
  induction n with
  | zero => intro z w; rfl
  | succ n ih => exact (transferStep_area _).comp ih
lemma transferProductInv_area (v : ℕ → ℝ) (n : ℕ) : PlaneAreaPreserving (transferProductInv v n) := by
  induction n with
  | zero => intro z w; rfl
  | succ n ih => exact ih.comp (transferStepInv_area _)
lemma transferProduct_inverse (v : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    transferProduct v n (transferProductInv v n z)=z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [transferProduct, transferProductInv,ContinuousLinearMap.comp_apply,ih,transferStep_inv]
lemma transferProductInv_inverse (v : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    transferProductInv v n (transferProduct v n z)=z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [transferProduct, transferProductInv,ContinuousLinearMap.comp_apply,transferStepInv_inv,ih]
lemma transferProduct_norm_inverse (v : ℕ → ℝ) (n : ℕ) :
    ‖transferProduct v n‖=‖transferProductInv v n‖ :=
  (transferProduct_area v n).norm_inverse (transferProductInv_area v n)
    (transferProduct_inverse v n) (transferProductInv_inverse v n)
lemma transferProduct_norm_bounds (v : ℕ → ℝ) (M : ℝ) (n : ℕ) (hM : 0≤M)
    (hv : ∀ i : ℕ, 1 ≤ i → i ≤ n → |v i| + 1 ≤ M) :
    1≤‖transferProduct v n‖ ∧ ‖transferProduct v n‖≤M^n := by
  refine ⟨(transferProduct_area v n).singular_pair.choose_spec.2.2.2.2,?_⟩
  induction n with
  | zero => simp [transferProduct]
  | succ n ih =>
    calc
      _ ≤ ‖transferStep (v (n+1))‖*‖transferProduct v n‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M*M^n := mul_le_mul ((transferStep_norm _).trans (hv _ (by omega) (by omega)))
        (ih fun i hi hin => hv i hi (by omega)) (norm_nonneg _) hM
      _ = _ := by rw [pow_succ]; ring
end StandardMapEntropy

end OAI
