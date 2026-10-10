import OAI.NumberTheory.Ostmann.Tree.TwoVertexReindex
import OAI.NumberTheory.Ostmann.Construction.FiniteProductPrior

namespace OAI

/-! # Integrating the selected pair inside the unchanged original product prior -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def twoCoordinateAssignment {V A : Type*} (a b : V) (hab : a ≠ b)
    (outside : OtherVertices a b → A) (q p : A) : V → A :=
  fun v => Sum.elim (fun t => if t then q else p) outside ((twoVertexEquiv a b hab).symm v)

@[simp] theorem twoCoordinateAssignment_short {V A : Type*} (a b : V) (hab : a ≠ b)
    (outside : OtherVertices a b → A) (q p : A) :
    twoCoordinateAssignment a b hab outside q p a = q := by
  change Sum.elim _ outside ((twoVertexEquiv a b hab).symm (twoVertexEquiv a b hab (.inl true))) = q
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem twoCoordinateAssignment_long {V A : Type*} (a b : V) (hab : a ≠ b)
    (outside : OtherVertices a b → A) (q p : A) :
    twoCoordinateAssignment a b hab outside q p b = p := by
  change Sum.elim _ outside ((twoVertexEquiv a b hab).symm (twoVertexEquiv a b hab (.inl false))) = p
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem twoCoordinateAssignment_other {V A : Type*} (a b : V) (hab : a ≠ b)
    (outside : OtherVertices a b → A) (q p : A) (v : OtherVertices a b) :
    twoCoordinateAssignment a b hab outside q p v = outside v := by
  change Sum.elim _ outside ((twoVertexEquiv a b hab).symm (twoVertexEquiv a b hab (.inr v))) = outside v
  rw [Equiv.symm_apply_apply]
  rfl

theorem twoCoordinateAssignment_update_long {V A : Type*} (a b : V) (hab : a ≠ b)
    (outside : OtherVertices a b → A) (q p p' : A) :
    Function.update (twoCoordinateAssignment a b hab outside q p) b p' =
      twoCoordinateAssignment a b hab outside q p' := by
  funext v
  obtain ⟨w, rfl⟩ := (twoVertexEquiv a b hab).surjective v
  cases w with
  | inl t =>
    cases t
    · simp only [twoVertexEquiv_long, Function.update_self, twoCoordinateAssignment_long]
    · simp only [twoVertexEquiv_short, Function.update_of_ne hab, twoCoordinateAssignment_short]
  | inr v =>
    simp only [twoVertexEquiv_other, Function.update_of_ne v.property.2, twoCoordinateAssignment_other]

noncomputable def twoCoordinateEquiv {V A : Type*} (a b : V) (hab : a ≠ b) :
    ((OtherVertices a b → A) × (A × A)) ≃ (V → A) where
  toFun x := twoCoordinateAssignment a b hab x.1 x.2.1 x.2.2
  invFun x := (fun v => x v, x a, x b)
  left_inv x := by
    apply Prod.ext
    · funext v; exact twoCoordinateAssignment_other a b hab _ _ _ v
    · exact Prod.ext (twoCoordinateAssignment_short a b hab _ _ _)
        (twoCoordinateAssignment_long a b hab _ _ _)
  right_inv x := by
    funext v
    obtain ⟨w, rfl⟩ := (twoVertexEquiv a b hab).surjective v
    cases w with
    | inl t => cases t <;> simp
    | inr v => simp

theorem productPrior_twoCoordinates {V A : Type*} [Fintype V]
    (a b : V) (hab : a ≠ b) (μ : V → A → ℝ)
    (outside : OtherVertices a b → A) (q p : A) :
    (∏ v, μ v (twoCoordinateAssignment a b hab outside q p v)) =
      (∏ v : OtherVertices a b, μ v (outside v)) * (μ a q * μ b p) := by
  rw [← (twoVertexEquiv a b hab).prod_comp (fun v => μ v (twoCoordinateAssignment a b hab outside q p v))]
  rw [Fintype.prod_sum_type, Fintype.prod_bool]
  simp only [twoVertexEquiv_short, twoVertexEquiv_long, twoVertexEquiv_other,
    twoCoordinateAssignment_short, twoCoordinateAssignment_long, twoCoordinateAssignment_other]
  ring

theorem sum_productPrior_twoCoordinates {V A : Type*} [Fintype V] [Fintype A]
    (a b : V) (hab : a ≠ b) (μ : V → A → ℝ) (F : (V → A) → ℂ) :
    (∑ x, ((∏ v, μ v (x v) : ℝ) : ℂ) * F x) =
      ∑ outside : OtherVertices a b → A,
        ((∏ v : OtherVertices a b, μ v (outside v) : ℝ) : ℂ) *
          ∑ q, (μ a q : ℂ) * ∑ p, (μ b p : ℂ) *
            F (twoCoordinateAssignment a b hab outside q p) := by
  rw [← (twoCoordinateEquiv (A := A) a b hab).sum_comp
    (fun x => ((∏ v, μ v (x v) : ℝ) : ℂ) * F x)]
  simp only [Fintype.sum_prod_type, twoCoordinateEquiv]
  apply Finset.sum_congr rfl
  intro outside _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  change ((∏ v, μ v (twoCoordinateAssignment a b hab outside q p v) : ℝ) : ℂ) *
    F (twoCoordinateAssignment a b hab outside q p) = _
  rw [productPrior_twoCoordinates, Complex.ofReal_mul, Complex.ofReal_mul]
  ring

/-- The section bound is averaged under every remaining original coordinate
prior. All range, distinctness and history restrictions stay inside `F`. -/
theorem original_prior_twoCoordinate_bound {V A : Type*} [Fintype V] [Fintype A]
    (a b : V) (hab : a ≠ b) (μ : V → A → ℝ)
    (hμ : ∀ v x, 0 ≤ μ v x) (hmass : ∀ v, ∑ x, μ v x ≤ 1)
    (F : (V → A) → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsection : ∀ outside : OtherVertices a b → A,
      ‖∑ q, (μ a q : ℂ) * ∑ p, (μ b p : ℂ) *
        F (twoCoordinateAssignment a b hab outside q p)‖ ≤ δ) :
    ‖∑ x, ((∏ v, μ v (x v) : ℝ) : ℂ) * F x‖ ≤ δ := by
  have hprod (outside : OtherVertices a b → A) : 0 ≤ ∏ v : OtherVertices a b, μ v (outside v) :=
    Finset.prod_nonneg fun v _ => hμ v _
  have hm : (∑ outside : OtherVertices a b → A, ∏ v : OtherVertices a b, μ v (outside v)) ≤ 1 := by
    rw [← Fintype.prod_sum]
    exact Finset.prod_le_one₀ (fun v _ => Finset.sum_nonneg fun x _ => hμ v x)
      (fun v _ => hmass v)
  rw [sum_productPrior_twoCoordinates a b hab μ F]
  calc
    _ ≤ ∑ outside : OtherVertices a b → A,
        ‖((∏ v : OtherVertices a b, μ v (outside v) : ℝ) : ℂ) *
          ∑ q, (μ a q : ℂ) * ∑ p, (μ b p : ℂ) *
            F (twoCoordinateAssignment a b hab outside q p)‖ := norm_sum_le _ _
    _ ≤ ∑ outside : OtherVertices a b → A, (∏ v : OtherVertices a b, μ v (outside v)) * δ := by
      apply Finset.sum_le_sum
      intro outside _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hprod outside)]
      exact mul_le_mul_of_nonneg_left (hsection outside) (hprod outside)
    _ = (∑ outside : OtherVertices a b → A, ∏ v : OtherVertices a b, μ v (outside v)) * δ :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hm hδ
    _ = δ := one_mul _

end Ostmann

end OAI
