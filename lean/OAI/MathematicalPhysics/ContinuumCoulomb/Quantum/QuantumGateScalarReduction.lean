import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAlgebraicHistory

namespace OAI

/-! Exact scalar reduction of a one-site gate tensor to its active entry
and spectator equality test. This avoids an ambient spin-basis sum in the
literal history-matrix evaluator. -/

noncomputable section
namespace ContinuumCoulomb.QuantumGateScalarReduction
open QuantumAlgebraicScalar QuantumFixedPauli QuantumAlgebraicHistory
open scoped Classical

@[simp] theorem mul_one (x : Scalar) : mul x (rat 1)=x := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp [mul,rat,realRat,realMul,realSub,realAdd,realNeg]

@[simp] theorem one_mul (x : Scalar) : mul (rat 1) x=x := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp [mul,rat,realRat,realMul,realSub,realAdd,realNeg]

@[simp] theorem mul_zero (x : Scalar) : mul x (rat 0)=rat 0 := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp [mul,rat,realRat,realMul,realSub,realAdd,realNeg]

@[simp] theorem zero_mul (x : Scalar) : mul (rat 0) x=rat 0 := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp [mul,rat,realRat,realMul,realSub,realAdd,realNeg]

theorem listProduct_single {α : Type} [DecidableEq α] (i : α) (z : Scalar)
    (xs : List α) (hx : xs.Nodup) :
    product (xs.map (fun j => if j=i then z else rat 1)) =
      if i ∈ xs then z else rat 1 := by
  induction xs with
  | nil => simp [product]
  | cons a xs ih =>
    by_cases ha : a=i
    · subst a
      have hn : i ∉ xs := (List.nodup_cons.mp hx).1
      simp [product,ih (List.nodup_cons.mp hx).2,hn]
    · simp [product,ha,ih (List.nodup_cons.mp hx).2,Ne.symm ha]

theorem listProduct_zero (xs : List Scalar) (h : rat 0 ∈ xs) : product xs=rat 0 := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with ha | hx
    · subst a
      simp [product]
    · simp [product,ih hx]

theorem finiteProduct_single {α : Type} [Fintype α] [DecidableEq α]
    (i : α) (z : Scalar) :
    finiteProduct (fun j => if j=i then z else rat 1)=z := by
  have hn : (enumerate α).Nodup :=
    List.nodup_ofFn.mpr (Fintype.equivFin α).symm.injective
  have hi : i ∈ enumerate α :=
    List.mem_ofFn.mpr ⟨(Fintype.equivFin α) i,(Fintype.equivFin α).symm_apply_apply i⟩
  rw [finiteProduct,listProduct_single i z _ hn,ite_eq_left hi]

theorem finiteProduct_zero {α : Type} [Fintype α] (f : α → Scalar)
    (i : α) (hi : f i=rat 0) : finiteProduct f=rat 0 := by
  apply listProduct_zero
  apply List.mem_map.mpr
  refine ⟨i,?_,hi⟩
  exact List.mem_ofFn.mpr
    ⟨(Fintype.equivFin α) i,(Fintype.equivFin α).symm_apply_apply i⟩

def sparseEntry {α : Type} [DecidableEq α] (i : α)
    (A : Fin 2 → Fin 2 → Scalar) (s t : α → Fin 2) : Scalar :=
  if ∀ j, j ≠ i → s j=t j then A (s i) (t i) else rat 0

theorem finiteProduct_sparse {α : Type} [Fintype α] [DecidableEq α]
    (i : α) (A : Fin 2 → Fin 2 → Scalar) (s t : α → Fin 2) :
    finiteProduct (fun j => if j=i then A (s j) (t j) else identity (s j) (t j)) =
      sparseEntry i A s t := by
  by_cases h : ∀ j, j ≠ i → s j=t j
  · have he : (fun j => if j=i then A (s j) (t j) else identity (s j) (t j)) =
        (fun j => if j=i then A (s i) (t i) else rat 1) := by
      funext j
      by_cases hj : j=i
      · simp [hj]
      · simp [hj,identity,h j hj]
    rw [he,finiteProduct_single]
    exact (ite_eq_left h).symm
  · obtain ⟨j,hj⟩ := not_forall.mp h
    have hji : j ≠ i := fun he => hj (by simp [he])
    have hst : s j ≠ t j := fun he => hj (fun _ => he)
    rw [finiteProduct_zero _ j (by simp [hji,identity,hst])]
    exact (ite_eq_right h).symm

theorem hadamard_entry (work j : ℕ) (s t : SourceSpinBasis (work+1)) :
    gate work (.hadamard j) s t=sparseEntry (qmaQubit work j) hadamard s t :=
  finiteProduct_sparse _ _ _ _

theorem phaseT_entry (work j : ℕ) (s t : SourceSpinBasis (work+1)) :
    gate work (.phaseT j) s t=sparseEntry (qmaQubit work j) phaseT s t :=
  finiteProduct_sparse _ _ _ _

end ContinuumCoulomb.QuantumGateScalarReduction

end

end OAI
