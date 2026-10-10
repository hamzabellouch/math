import OAI.RepresentationTheory.FoulkesHowe.FirstPolynomial
import OAI.RepresentationTheory.FoulkesHowe.Multiplication

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem346
universe u v
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {κ : Type v} [Fintype κ]

/-- Assign vector values to the three kinds of blocks in the first transfer. -/
def firstVectors {m : ℕ} (x t : V) (y : Fin m → V) : FirstBlock m → V
  | none => x
  | some none => t
  | some (some j) => y j

omit [AddCommGroup V] [Module ℂ V] in
@[simp] theorem firstVectors_x {m : ℕ} (x t : V) (y : Fin m → V) :
    firstVectors x t y none = x := rfl
omit [AddCommGroup V] [Module ℂ V] in
@[simp] theorem firstVectors_t {m : ℕ} (x t : V) (y : Fin m → V) :
    firstVectors x t y (some none) = t := rfl
omit [AddCommGroup V] [Module ℂ V] in
@[simp] theorem firstVectors_y {m : ℕ} (x t : V) (y : Fin m → V) (j : Fin m) :
    firstVectors x t y (some (some j)) = y j := rfl

@[simp] theorem firstLabel_initial_monomial (r m : ℕ) (x t : V) (y : Fin m → V) :
    symMonomial (r+m) V (fun j => firstVectors x t y (firstLabel r m 0 (0,j))) =
      symMonomial (r+m) V (fun _ => t) := by
  simp

@[simp] theorem firstLabel_other_monomial (r m k : ℕ) (x t : V)
    (y : Fin m → V) (i : Fin r) :
    symMonomial (r+m) V (fun j => firstVectors x t y (firstLabel r m k (i.succ,j))) =
      symPowMul r m (symMonomial r V (fun _ => x)) (symMonomial m V y) := by
  rw [symPowMul_symMonomial]
  congr 1
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro j
    simp [Fin.append]
  · intro j
    simp [Fin.append]

@[simp] theorem firstLabel_final_monomial (r m : ℕ) (x t : V) (y : Fin m → V) :
    symMonomial (r+m) V (fun j => firstVectors x t y (firstLabel r m m (0,j))) =
      symPowMul r m (symMonomial r V (fun _ => t)) (symMonomial m V y) := by
  apply Subtype.ext
  change (∏ j : Fin (r+m), SymmetricAlgebra.ι ℂ V
      (firstVectors x t y (firstLabel r m m (0,j)))) =
    (∏ _ : Fin r, SymmetricAlgebra.ι ℂ V t) * ∏ j : Fin m, SymmetricAlgebra.ι ℂ V (y j)
  rw [← (finCongr (Nat.add_comm m r)).prod_comp
    (fun j : Fin (r+m) => SymmetricAlgebra.ι ℂ V
      (firstVectors x t y (firstLabel r m m (0,j))))]
  rw [Fin.prod_univ_add]
  have hleft : (∏ j : Fin m, SymmetricAlgebra.ι ℂ V
      (firstVectors x t y (firstLabel r m m
        (0, (finCongr (Nat.add_comm m r)) (Fin.castAdd r j))))) =
      ∏ j : Fin m, SymmetricAlgebra.ι ℂ V (y j) := by
    apply Finset.prod_congr rfl
    intro j _
    simp [firstLabel]
  have hright : (∏ j : Fin r, SymmetricAlgebra.ι ℂ V
      (firstVectors x t y (firstLabel r m m
        (0, (finCongr (Nat.add_comm m r)) (Fin.natAdd m j))))) =
      ∏ _ : Fin r, SymmetricAlgebra.ι ℂ V t := by
    apply Finset.prod_congr rfl
    intro j _
    simp [firstLabel]
  rw [hleft, hright, mul_comm]

/-- Evaluation of the initial label configuration. -/
theorem firstLabel_initial_form {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (x t : V) (y : Fin m → V) :
    flattenedForm T (fun p => firstVectors x t y (firstLabel r m 0 p)) =
      T (Fin.cons (symMonomial (r+m) V (fun _ => t))
        (fun _ => symPowMul r m (symMonomial r V (fun _ => x)) (symMonomial m V y))) := by
  rw [flattenedForm_apply]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => exact firstLabel_initial_monomial r m x t y
  | succ i => exact firstLabel_other_monomial r m 0 x t y i

/-- Evaluation of the terminal label configuration, with t^r times the common product. -/
theorem firstLabel_final_form {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (x t : V) (y : Fin m → V) :
    flattenedForm T (fun p => firstVectors x t y (firstLabel r m m p)) =
      T (Fin.cons (symPowMul r m (symMonomial r V (fun _ => t)) (symMonomial m V y))
        (fun _ => symPowMul r m (symMonomial r V (fun _ => x)) (symMonomial m V y))) := by
  rw [flattenedForm_apply]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => exact firstLabel_final_monomial r m x t y
  | succ i => exact firstLabel_other_monomial r m m x t y i

/-- The binary identity makes the terminal polynomial zero. -/
theorem firstPolynomial_final_eq_zero {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : κ → V)
    (h : ∀ (x t : V) (y : Fin m → V),
      T (Fin.cons (symPowMul r m (symMonomial r V (fun _ => t)) (symMonomial m V y))
        (fun _ => symPowMul r m (symMonomial r V (fun _ => x)) (symMonomial m V y))) = 0) :
    firstPolynomial T e m = 0 := by
  apply multilinearPolynomial_eq_zero
  intro v
  have hv : firstVectors (v none) (v (some none)) (fun j => v (some (some j))) = v := by
    funext b
    cases b with
    | none => rfl
    | some b => cases b <;> rfl
  rw [← hv]
  rw [firstLabel_final_form]
  exact h _ _ _

/-- A zero initial polynomial gives the freed-last-slot identity. -/
theorem firstPolynomial_initial_vanishing {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : Module.Basis κ ℂ V)
    (h : firstPolynomial T e 0 = 0) (x t : V) (y : Fin m → V) :
    T (Fin.cons (symMonomial (r+m) V (fun _ => t))
      (fun _ => symPowMul r m (symMonomial r V (fun _ => x)) (symMonomial m V y))) = 0 := by
  rw [← firstLabel_initial_form]
  have hp := (multilinearPolynomial_eq_zero_iff (flattenedForm T) e
    (firstLabel r m 0)).mp h
  exact hp (firstVectors x t y)

end Problem346

end

end OAI
