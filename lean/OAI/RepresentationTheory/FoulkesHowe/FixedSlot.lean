import OAI.RepresentationTheory.FoulkesHowe.FlattenedSwap
import OAI.RepresentationTheory.FoulkesHowe.Multiplication

namespace OAI

noncomputable section
namespace Problem346
universe u
variable {r b : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Flatten the remaining rows after fixing the first slot to a pure power. -/
def fixedSlotFlatten (T : SymmetricMultilinearForm (r+1) b V) (t : V) :
    MultilinearMap ℂ (fun _ : Fin r × Fin b => V) ℂ :=
  flattenedSymmetricForm (T.curryLeft (symMonomial b V (fun _ => t)))

@[simp] theorem fixedSlotFlatten_apply
    (T : SymmetricMultilinearForm (r+1) b V) (t : V) (v : Fin r × Fin b → V) :
    fixedSlotFlatten T t v =
      T (Fin.cons (symMonomial b V (fun _ => t))
        (fun i => symMonomial b V (fun j => v (i,j)))) := rfl

/-- Every row remains symmetric in its factors after fixing the first slot. -/
theorem fixedSlotFlatten_inner_permute
    (T : SymmetricMultilinearForm (r+1) b V) (t : V)
    (σ : Fin r → Equiv.Perm (Fin b)) (v : Fin r × Fin b → V) :
    fixedSlotFlatten T t (fun p => v (p.1, σ p.1 p.2)) = fixedSlotFlatten T t v :=
  flattenedSymmetricForm_inner_permute _ σ v

/-- Repeated vectors in the remaining rows are literal pure powers. -/
@[simp] theorem fixedSlotFlatten_constant_rows
    (T : SymmetricMultilinearForm (r+1) b V) (t : V) (v : Fin r → V) :
    fixedSlotFlatten T t (fun p => v p.1) =
      T (Fin.cons (symMonomial b V (fun _ => t))
        (fun i => symMonomial b V (fun _ => v i))) := rfl

/-- Concatenating factors in every unfixed row computes graded multiplication. -/
theorem fixedSlotFlatten_append {m n : ℕ}
    (T : SymmetricMultilinearForm (r+1) (m+n) V) (t : V)
    (v : Fin r → Fin m → V) (w : Fin r → Fin n → V) :
    fixedSlotFlatten T t (fun p => Fin.append (v p.1) (w p.1) p.2) =
      T (Fin.cons (symMonomial (m+n) V (fun _ => t))
        (fun i => symPowMul m n (symMonomial m V (v i)) (symMonomial n V (w i)))) := by
  simp only [fixedSlotFlatten_apply, symPowMul_symMonomial]

/-- The endpoint of the second shift chain has a common power factor in every row. -/
theorem fixedSlotFlatten_common_power {m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (x t : V) (v : Fin r → V) :
    fixedSlotFlatten T t
      (fun p => Fin.append (fun _ : Fin r => x) (fun _ : Fin m => v p.1) p.2) =
      T (Fin.cons (symMonomial (r+m) V (fun _ => t))
        (fun i => symPowMul r m (symMonomial r V (fun _ => x))
          (symMonomial m V (fun _ => v i)))) := by
  simp only [fixedSlotFlatten_apply, symPowMul_symMonomial]

/-- Swapping two factor slots in the same unfixed row changes no value. -/
theorem fixedSlotFlatten_swap_same_row
    (T : SymmetricMultilinearForm (r+1) b V) (t : V)
    (p q : Fin r × Fin b) (hpq : p.1=q.1) (v : Fin r × Fin b → V) :
    fixedSlotFlatten T t (v ∘ Equiv.swap p q) = fixedSlotFlatten T t v :=
  flattenedSymmetricForm_swap_same_row
    (T.curryLeft (symMonomial b V (fun _ => t))) p q hpq v

/-- The fixed-slot coefficient array meets the row-swap hypothesis of shift recurrence. -/
theorem fixedSlotFlatten_coeff_swap_same_row {I : Type*}
    (T : SymmetricMultilinearForm (r+1) b V) (t : V) (e : I → V)
    (p q : Fin r × Fin b) (hpq : p.1=q.1) (k : Fin r × Fin b → I) :
    fixedSlotFlatten T t (e ∘ (k ∘ Equiv.swap p q)) = fixedSlotFlatten T t (e ∘ k) :=
  fixedSlotFlatten_swap_same_row T t p q hpq (e ∘ k)

end Problem346

end

end OAI
