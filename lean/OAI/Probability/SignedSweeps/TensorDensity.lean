import OAI.Probability.SignedSweeps.PositiveRootTensor

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical

structure FiniteComplexHilbert where
  carrier : Type
  normedAddCommGroup : NormedAddCommGroup carrier
  innerProductSpace : InnerProductSpace ℂ carrier
  finiteDimensional : FiniteDimensional ℂ carrier

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
attribute [instance] FiniteComplexHilbert.normedAddCommGroup
  FiniteComplexHilbert.innerProductSpace FiniteComplexHilbert.finiteDimensional

instance : CoeSort FiniteComplexHilbert Type := ⟨FiniteComplexHilbert.carrier⟩

def scalarHilbert : FiniteComplexHilbert := ⟨ℂ, inferInstance, inferInstance, inferInstance⟩

def tensorHilbert (E F : FiniteComplexHilbert) : FiniteComplexHilbert :=
  ⟨E ⊗[ℂ] F, inferInstance, inferInstance, inferInstance⟩

def tensorHilbertPower (E : FiniteComplexHilbert) : ℕ → FiniteComplexHilbert
  | 0 => scalarHilbert
  | p + 1 => tensorHilbert E (tensorHilbertPower E p)

def tensorOperator (E : FiniteComplexHilbert) :
    {p : ℕ} → (Fin p → E →ₗ[ℂ] E) → tensorHilbertPower E p →ₗ[ℂ] tensorHilbertPower E p
  | 0, _ => 1
  | p + 1, A => TensorProduct.map (A 0) (tensorOperator E (fun i : Fin p => A i.succ))

lemma tensorOperator_mul (E : FiniteComplexHilbert) {p : ℕ}
    (A B : Fin p → E →ₗ[ℂ] E) :
    tensorOperator E (fun i => A i * B i) = tensorOperator E A * tensorOperator E B := by
  induction p with
  | zero => simp [tensorOperator]
  | succ p ih =>
    simp only [tensorOperator, ih, TensorProduct.map_mul]
    rfl

lemma tensorOperator_one (E : FiniteComplexHilbert) (p : ℕ) :
    tensorOperator E (fun _ : Fin p => (1 : E →ₗ[ℂ] E)) = 1 := by
  induction p with
  | zero => rfl
  | succ p ih =>
    simp only [tensorOperator, ih, TensorProduct.map_one]
    rfl

lemma tensorOperator_adjoint (E : FiniteComplexHilbert) {p : ℕ}
    (A : Fin p → E →ₗ[ℂ] E) :
    (tensorOperator E A).adjoint = tensorOperator E (fun i => (A i).adjoint) := by
  induction p with
  | zero => simp only [tensorOperator, LinearMap.adjoint_one]
  | succ p ih =>
    change (TensorProduct.map (A 0) (tensorOperator E (fun i : Fin p => A i.succ))).adjoint =
      TensorProduct.map (A 0).adjoint (tensorOperator E (fun i : Fin p => (A i.succ).adjoint))
    rw [TensorProduct.adjoint_map, ih]

lemma tensorOperator_positive (E : FiniteComplexHilbert) {p : ℕ}
    (A : Fin p → E →ₗ[ℂ] E) (hA : ∀ i, (A i).IsPositive) :
    (tensorOperator E A).IsPositive := by
  induction p with
  | zero => exact LinearMap.isPositive_one
  | succ p ih => exact tensor_map_positive _ _ (hA _) (ih _ (fun i => hA i.succ))

lemma positiveRoot_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] : positiveRoot (1 : E →ₗ[ℂ] E) LinearMap.isPositive_one = 1 := by
  apply positive_square_root_unique _ _ (positiveRoot_positive _ _) LinearMap.isPositive_one
  rw [positiveRoot_square, one_mul]

lemma tensorOperator_positiveRoot (E : FiniteComplexHilbert) {p : ℕ}
    (A : Fin p → E →ₗ[ℂ] E) (hA : ∀ i, (A i).IsPositive) :
    positiveRoot (tensorOperator E A) (tensorOperator_positive E A hA) =
      tensorOperator E (fun i => positiveRoot (A i) (hA i)) := by
  apply positive_square_root_unique _ _ (positiveRoot_positive _ _)
    (tensorOperator_positive _ _ (fun _ => positiveRoot_positive _ _))
  rw [positiveRoot_square, ← tensorOperator_mul]
  simp only [positiveRoot_square]

lemma tensorOperator_norm_sq_le (E : FiniteComplexHilbert) {p : ℕ}
    (A : Fin p → E →ₗ[ℂ] E) :
    ‖(tensorOperator E A).toContinuousLinearMap‖ ^ 2 ≤
      ∏ i, ‖(A i).toContinuousLinearMap‖ ^ 2 := by
  induction p with
  | zero =>
    change ‖(ContinuousLinearMap.id ℂ ℂ)‖ ^ 2 ≤ ∏ i : Fin 0, _
    rw [Fin.prod_univ_zero]
    exact (pow_le_pow_left₀ (norm_nonneg _) ContinuousLinearMap.norm_id_le 2).trans (by norm_num)
  | succ p ih =>
    rw [Fin.prod_univ_succ]
    exact (tensor_map_norm_sq_le _ _).trans
      (mul_le_mul_of_nonneg_left (ih _) (sq_nonneg _))

lemma tensor_normalized_density_bound {A B : Type} [Fintype A] [Fintype B]
    [Nonempty B] (E : FiniteComplexHilbert) (W : Finset (A × B))
    (e : Fin W.card ≃ {x // x ∈ W})
    (R : B → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    (S : A → E →ₗ[ℂ] E) (hS : ∀ i, (S i).IsPositive)
    (htrS : ∀ i, (LinearMap.trace ℂ E (S i)).re = 1) :
    ‖(tensorOperator E (fun k => positiveRoot (R (e k).1.2) (hR _) *
      supportInverseRoot (densityMean R) (densityMean_positive R hR) *
      positiveRoot (S (e k).1.1) (hS _))).toContinuousLinearMap‖ ^ 2 ≤
        missingCellFactor W := by
  apply (tensorOperator_norm_sq_le _ _).trans
  have hp := normalized_density_norm_product_bound W R hR S hS htrS
  have heq := Equiv.prod_comp e (fun c =>
    ‖(positiveRoot (R c.1.2) (hR _) *
      supportInverseRoot (densityMean R) (densityMean_positive R hR) *
      positiveRoot (S c.1.1) (hS _)).toContinuousLinearMap‖ ^ 2)
  rw [heq]
  have hw := Finset.prod_coe_sort W (fun c =>
    ‖(positiveRoot (R c.2) (hR _) *
      supportInverseRoot (densityMean R) (densityMean_positive R hR) *
      positiveRoot (S c.1) (hS _)).toContinuousLinearMap‖ ^ 2)
  exact hw.trans_le hp

end SignedSweeps
end

end OAI
