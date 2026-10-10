import OAI.LinearAlgebra.MatrixMultiplication.Completion.ProductLaws
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.UniformCoordinate

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualUniformProducts

open MatrixMultiplication.Foundation CompletionProductLaws CompletionLaws
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A X Y : I → Type*}
variable [∀ i, Fintype (A i)] [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

def supportWordEquiv (P : ∀ i, X i → Prop) :
    {x : ∀ i, X i // ∀ i, P i (x i)} ≃ ∀ i, {x : X i // P i x} where
  toFun x i := ⟨x.val i, x.property i⟩
  invFun x := ⟨fun i => (x i).val, fun i => (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem supportWord_card (P : ∀ i, X i → Prop) :
    Fintype.card {x : ∀ i, X i // ∀ i, P i (x i)} =
      ∏ i, Fintype.card {x : X i // P i x} := by
  rw [Fintype.card_congr (supportWordEquiv P), Fintype.card_pi]

theorem independentProduct_uniformCoordinate
    (p : ∀ i, FiniteLaw (A i)) (f : ∀ i, A i → X i)
    (P : ∀ i, X i → Prop)
    (h : ∀ i, UniformCoordinate (p i) (f i) (P i)) :
    UniformCoordinate (independentProduct p) (fun a i => f i (a i))
      (fun x => ∀ i, P i (x i)) := by
  have hmass (i : I) (x : X i) :
      ((p i).map (f i)).mass x =
        if P i x then (Fintype.card {x : X i // P i x} : ℝ)⁻¹ else 0 := h i x
  intro x
  rw [independentProduct_map_mass]
  simp_rw [hmass]
  by_cases hx : ∀ i, P i (x i)
  · rw [ite_eq_left hx]
    simp only [hx, ite_true]
    rw [supportWord_card]
    simp only [Nat.cast_prod, Finset.prod_inv_distrib]
  · rw [ite_eq_right hx]
    obtain ⟨i, hi⟩ := not_forall.mp hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem independentProduct_joint_mass
    (p : ∀ i, FiniteLaw (A i))
    (f : ∀ i, A i → X i) (g : ∀ i, A i → Y i)
    (x : ∀ i, X i) (y : ∀ i, Y i) :
    ((independentProduct p).map
      (fun a => ((fun i => f i (a i)), (fun i => g i (a i))))).mass (x, y) =
      ∏ i, ((p i).map (fun a => (f i a, g i a))).mass (x i, y i) := by
  calc
    _ = ((independentProduct p).map
        (fun a i => (f i (a i), g i (a i)))).mass (fun i => (x i, y i)) := by
      simp only [FiniteLaw.map_mass, Prod.mk.injEq, funext_iff, forall_and]
    _ = _ := independentProduct_map_mass p (fun i a => (f i a, g i a)) _

theorem independentProduct_independent
    (p : ∀ i, FiniteLaw (A i))
    (f : ∀ i, A i → X i) (g : ∀ i, A i → Y i)
    (h : ∀ i x y, ((p i).map (fun a => (f i a, g i a))).mass (x, y) =
      ((p i).map (f i)).mass x * ((p i).map (g i)).mass y)
    (x : ∀ i, X i) (y : ∀ i, Y i) :
    ((independentProduct p).map
      (fun a => ((fun i => f i (a i)), (fun i => g i (a i))))).mass (x, y) =
      ((independentProduct p).map (fun a i => f i (a i))).mass x *
        ((independentProduct p).map (fun a i => g i (a i))).mass y := by
  rw [independentProduct_joint_mass, independentProduct_map_mass,
    independentProduct_map_mass]
  simp_rw [h]
  exact Finset.prod_mul_distrib

end MatrixMultiplication.DualUniformProducts

end

end OAI
