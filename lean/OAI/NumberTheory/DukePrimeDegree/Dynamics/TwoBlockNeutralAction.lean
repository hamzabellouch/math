import OAI.NumberTheory.DukePrimeDegree.Dynamics.TwoBlockGaussChart

namespace OAI

/-!
# The neutral action on a cross-block root group

The actual block-diagonal subgroup normalizes the upper cross-block group.
We keep the matrix action explicit, so reordering the Gauss chart will put
the neutral factor last and expose actual right-translation covariance.
-/

noncomputable section
open Matrix
open scoped Topology Classical

namespace DukePrimeDegree

lemma twoBlockNeutral_matrix {a b : ℕ} (C : twoBlockNeutralGroup a b) :
    C.val.val = Matrix.fromBlocks C.val.val.toBlocks₁₁ 0 0 C.val.val.toBlocks₂₂ := by
  have hz := (mem_twoBlockNeutralGroup_iff C.val).mp C.property
  simpa only [hz.1, hz.2] using (Matrix.fromBlocks_toBlocks C.val.val).symm

lemma twoBlockNeutral_inverse_blocks {a b : ℕ} (C : twoBlockNeutralGroup a b) :
    C.val.val.toBlocks₁₁ * (C⁻¹).val.val.toBlocks₁₁ = 1 ∧
      C.val.val.toBlocks₂₂ * (C⁻¹).val.val.toBlocks₂₂ = 1 := by
  have he : C.val.val * (C⁻¹).val.val = 1 := by
    exact congrArg (fun g : TwoBlockSL a b => g.val) (mul_inv_cancel C.val)
  rw [twoBlockNeutral_matrix C, twoBlockNeutral_matrix C⁻¹] at he
  have h11 := congrArg Matrix.toBlocks₁₁ he
  have h22 := congrArg Matrix.toBlocks₂₂ he
  constructor
  · simpa only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, Matrix.toBlocks_fromBlocks₁₁, ← Matrix.fromBlocks_one] using h11
  · simpa only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      zero_add, Matrix.toBlocks_fromBlocks₂₂, ← Matrix.fromBlocks_one] using h22

def twoBlockUpperAction {a b : ℕ} (C : twoBlockNeutralGroup a b)
    (U : Matrix (Fin a) (Fin b) ℝ) : Matrix (Fin a) (Fin b) ℝ :=
  C.val.val.toBlocks₁₁ * U * (C⁻¹).val.val.toBlocks₂₂

lemma twoBlockUpper_injective {a b : ℕ} :
    Function.Injective (twoBlockUpper : Matrix (Fin a) (Fin b) ℝ → TwoBlockSL a b) := by
  intro U V he
  have hm := congrArg (fun g : TwoBlockSL a b => g.val.toBlocks₁₂) he
  exact hm

theorem twoBlockNeutral_conjugate_upper {a b : ℕ}
    (C : twoBlockNeutralGroup a b) (U : Matrix (Fin a) (Fin b) ℝ) :
    C.val * twoBlockUpper U * C.val⁻¹ = twoBlockUpper (twoBlockUpperAction C U) := by
  apply Subtype.ext
  change C.val.val * Matrix.fromBlocks 1 U 0 1 * (C⁻¹).val.val =
    Matrix.fromBlocks 1 (twoBlockUpperAction C U) 0 1
  have hi := twoBlockNeutral_inverse_blocks C
  rw [twoBlockNeutral_matrix C, twoBlockNeutral_matrix C⁻¹]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_one,
    Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
    twoBlockUpperAction, hi.1, hi.2]

theorem twoBlockNeutral_upper_reorder {a b : ℕ}
    (C : twoBlockNeutralGroup a b) (U : Matrix (Fin a) (Fin b) ℝ) :
    C.val * twoBlockUpper U = twoBlockUpper (twoBlockUpperAction C U) * C.val := by
  rw [← twoBlockNeutral_conjugate_upper]
  group

@[simp] theorem twoBlockUpperAction_inv_apply {a b : ℕ}
    (C : twoBlockNeutralGroup a b) (U : Matrix (Fin a) (Fin b) ℝ) :
    twoBlockUpperAction C⁻¹ (twoBlockUpperAction C U) = U := by
  apply twoBlockUpper_injective
  rw [← twoBlockNeutral_conjugate_upper, ← twoBlockNeutral_conjugate_upper]
  change C.val⁻¹ * (C.val * twoBlockUpper U * C.val⁻¹) * (C.val⁻¹)⁻¹ = _
  group

@[simp] theorem twoBlockUpperAction_apply_inv {a b : ℕ}
    (C : twoBlockNeutralGroup a b) (U : Matrix (Fin a) (Fin b) ℝ) :
    twoBlockUpperAction C (twoBlockUpperAction C⁻¹ U) = U := by
  simpa only [inv_inv] using twoBlockUpperAction_inv_apply C⁻¹ U

theorem twoBlockUpperAction_mul {a b : ℕ}
    (C D : twoBlockNeutralGroup a b) (U : Matrix (Fin a) (Fin b) ℝ) :
    twoBlockUpperAction (C * D) U = twoBlockUpperAction C (twoBlockUpperAction D U) := by
  apply twoBlockUpper_injective
  rw [← twoBlockNeutral_conjugate_upper, ← twoBlockNeutral_conjugate_upper,
    ← twoBlockNeutral_conjugate_upper]
  change (C.val * D.val) * twoBlockUpper U * (C.val * D.val)⁻¹ =
    C.val * (D.val * twoBlockUpper U * D.val⁻¹) * C.val⁻¹
  group

theorem continuous_twoBlockUpperAction (a b : ℕ) :
    Continuous (fun p : twoBlockNeutralGroup a b × Matrix (Fin a) (Fin b) ℝ =>
      twoBlockUpperAction p.1 p.2) := by
  have h11 : Continuous (fun p : twoBlockNeutralGroup a b × Matrix (Fin a) (Fin b) ℝ =>
      p.1.val.val.toBlocks₁₁) := by
    change Continuous (fun p : twoBlockNeutralGroup a b × Matrix (Fin a) (Fin b) ℝ =>
      fun i j => p.1.val.val (Sum.inl i) (Sum.inl j))
    fun_prop
  have h22 : Continuous (fun p : twoBlockNeutralGroup a b × Matrix (Fin a) (Fin b) ℝ =>
      (p.1⁻¹).val.val.toBlocks₂₂) := by
    change Continuous (fun p : twoBlockNeutralGroup a b × Matrix (Fin a) (Fin b) ℝ =>
      fun i j => (p.1⁻¹).val.val (Sum.inr i) (Sum.inr j))
    fun_prop
  exact (h11.matrix_mul continuous_snd).matrix_mul h22

theorem continuous_twoBlockUpperAction_inv (a b : ℕ) :
    Continuous (fun p : twoBlockNeutralGroup a b × Matrix (Fin a) (Fin b) ℝ =>
      twoBlockUpperAction p.1⁻¹ p.2) := by
  have h11 : Continuous (fun p : twoBlockNeutralGroup a b × Matrix (Fin a) (Fin b) ℝ =>
      (p.1⁻¹).val.val.toBlocks₁₁) := by
    change Continuous (fun p : twoBlockNeutralGroup a b × Matrix (Fin a) (Fin b) ℝ =>
      fun i j => (p.1⁻¹).val.val (Sum.inl i) (Sum.inl j))
    fun_prop
  have h22 : Continuous (fun p : twoBlockNeutralGroup a b × Matrix (Fin a) (Fin b) ℝ =>
      p.1.val.val.toBlocks₂₂) := by
    change Continuous (fun p : twoBlockNeutralGroup a b × Matrix (Fin a) (Fin b) ℝ =>
      fun i j => p.1.val.val (Sum.inr i) (Sum.inr j))
    fun_prop
  simpa only [twoBlockUpperAction, inv_inv] using
    (h11.matrix_mul continuous_snd).matrix_mul h22

end DukePrimeDegree

end

end OAI
