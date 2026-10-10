import OAI.RepresentationTheory.FoulkesHowe.MonomialMultilinear

namespace OAI

noncomputable section

namespace Problem346

universe u

variable {a b : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- A form on symmetric powers, evaluated on products, is multilinear in all
of the underlying vector factors. -/
def flattenedSymmetricForm (T : SymmetricMultilinearForm a b V) :
    MultilinearMap ℂ (fun _ : Fin a × Fin b => V) ℂ :=
  (T.compMultilinearMap (fun _ => symMonomialMultilinear b V)).domDomCongr
    (Equiv.sigmaEquivProd (Fin a) (Fin b))

@[simp]
theorem flattenedSymmetricForm_apply (T : SymmetricMultilinearForm a b V)
    (v : Fin a × Fin b → V) :
    flattenedSymmetricForm T v =
      T (fun i => symMonomial b V (fun j => v (i, j))) := rfl

/-- Independent permutations within the rows preserve the flattened form. -/
theorem flattenedSymmetricForm_inner_permute
    (T : SymmetricMultilinearForm a b V)
    (σ : Fin a → Equiv.Perm (Fin b)) (v : Fin a × Fin b → V) :
    flattenedSymmetricForm T (fun p => v (p.1, σ p.1 p.2)) =
      flattenedSymmetricForm T v := by
  apply congrArg T
  funext i
  exact symMonomial_permute b V (σ i) (fun j => v (i, j))

/-- Symmetry of the original form permits permutation of the rows. -/
theorem flattenedSymmetricForm_outer_permute
    (T : SymmetricMultilinearForm a b V)
    (hT : IsSymmetricMultilinearForm a b V T)
    (σ : Equiv.Perm (Fin a)) (v : Fin a × Fin b → V) :
    flattenedSymmetricForm T (fun p => v (σ p.1, p.2)) =
      flattenedSymmetricForm T v := by
  exact hT σ (fun i => symMonomial b V (fun j => v (i, j)))

/-- Compatibility API for the same flattened form, with inferred degrees. -/
abbrev flattenedForm {a b : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]
    (T : SymmetricMultilinearForm a b V) :
    MultilinearMap ℂ (fun _ : Fin a × Fin b => V) ℂ :=
  flattenedSymmetricForm T

@[simp]
theorem flattenedForm_apply {a b : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]
    (T : SymmetricMultilinearForm a b V) (x : Fin a × Fin b → V) :
    flattenedForm T x = T (fun i => symMonomial b V (fun j => x (i, j))) := rfl

theorem flattenedForm_permute_factors (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (T : SymmetricMultilinearForm a b V)
    (σ : Fin a → Equiv.Perm (Fin b)) (x : Fin a × Fin b → V) :
    flattenedForm T (fun p => x (p.1, σ p.1 p.2)) =
      flattenedForm T x :=
  flattenedSymmetricForm_inner_permute T σ x

theorem flattenedForm_permute_slots (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (T : SymmetricMultilinearForm a b V)
    (hT : IsSymmetricMultilinearForm a b V T)
    (σ : Equiv.Perm (Fin a)) (x : Fin a × Fin b → V) :
    flattenedForm T (fun p => x (σ p.1, p.2)) =
      flattenedForm T x :=
  flattenedSymmetricForm_outer_permute T hT σ x

/-- Simultaneous row and independent within-row permutation invariance. -/
theorem flattenedForm_permute (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (T : SymmetricMultilinearForm a b V)
    (hT : IsSymmetricMultilinearForm a b V T)
    (σ : Equiv.Perm (Fin a)) (τ : Fin a → Equiv.Perm (Fin b))
    (x : Fin a × Fin b → V) :
    flattenedForm T (fun p => x (σ p.1, τ p.1 p.2)) =
      flattenedForm T x :=
  (flattenedForm_permute_factors a b V T τ (fun p => x (σ p.1, p.2))).trans
    (flattenedForm_permute_slots a b V T hT σ x)

/-- Implicit-parameter factor symmetry used by the transfer sequences. -/
theorem flattenedForm_factor_perm (T : SymmetricMultilinearForm a b V)
    (σ : Fin a → Equiv.Perm (Fin b)) (v : Fin a × Fin b → V) :
    flattenedForm T (fun p => v (p.1, σ p.1 p.2)) = flattenedForm T v :=
  flattenedSymmetricForm_inner_permute T σ v

/-- Implicit-parameter row symmetry used by the transfer sequences. -/
theorem flattenedForm_row_perm (T : SymmetricMultilinearForm a b V)
    (hT : IsSymmetricMultilinearForm a b V T) (σ : Equiv.Perm (Fin a))
    (v : Fin a × Fin b → V) :
    flattenedForm T (fun p => v (σ p.1, p.2)) = flattenedForm T v :=
  flattenedSymmetricForm_outer_permute T hT σ v

@[simp] theorem flattenedForm_constant_rows (T : SymmetricMultilinearForm a b V)
    (v : Fin a → V) :
    flattenedForm T (fun p => v p.1) =
      T (fun i => symMonomial b V (fun _ => v i)) := rfl

@[simp] theorem flattenedForm_constant_columns (T : SymmetricMultilinearForm a b V)
    (v : Fin b → V) :
    flattenedForm T (fun p => v p.2) =
      T (fun _ => symMonomial b V v) := rfl

end Problem346

end

end OAI
