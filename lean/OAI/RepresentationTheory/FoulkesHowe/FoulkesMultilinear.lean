import OAI.RepresentationTheory.FoulkesHowe.Model

namespace OAI

noncomputable section

open scoped BigOperators
universe u

namespace Problem346

private def monomialMultilinearAux (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] :
    MultilinearMap ℂ (fun _ : Fin n => V) (SymPow n V) :=
  ((MultilinearMap.mkPiAlgebra ℂ (Fin n) (SymmetricAlgebra ℂ V)).compLinearMap
    (fun _ => SymmetricAlgebra.ι ℂ V)).codRestrict (symPowSubmodule n V)
      (fun v => Submodule.subset_span (Set.mem_range_self v))

private theorem monomialMultilinearAux_apply (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (v : Fin n → V) :
    monomialMultilinearAux n V v = symMonomial n V v := rfl

/-- Reindex the slots in a transposed grid, allowing an independent permutation
in each original row. -/
def foulkesIndexEquiv (a b : ℕ) (σ : Fin b → Equiv.Perm (Fin a)) :
    (Σ _ : Fin a, Fin b) ≃ (Fin b × Fin a) where
  toFun p := (p.2, σ p.2 p.1)
  invFun p := ⟨(σ p.1).symm p.2, p.1⟩
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp

/-- A summand of the Foulkes--Howe formula, viewed as a multilinear map in
all entries of the input grid. -/
def foulkesSummandMultilinear (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (σ : Fin b → Equiv.Perm (Fin a)) :
    MultilinearMap ℂ (fun _ : Fin b × Fin a => V) (SymPow a (SymPow b V)) :=
  ((monomialMultilinearAux a (SymPow b V)).compMultilinearMap
      (fun _ => monomialMultilinearAux b V)).domDomCongr (foulkesIndexEquiv a b σ)

@[simp] theorem foulkesSummandMultilinear_apply (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (σ : Fin b → Equiv.Perm (Fin a))
    (v : Fin b × Fin a → V) :
    foulkesSummandMultilinear a b V σ v =
      symMonomial a (SymPow b V)
        (fun i => symMonomial b V (fun j => v (j, σ j i))) := rfl

/-- The canonical Foulkes--Howe expression is multilinear in its `a * b`
individual vector arguments. -/
def foulkesMultilinear (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] :
    MultilinearMap ℂ (fun _ : Fin b × Fin a => V) (SymPow a (SymPow b V)) := by
  classical
  exact ((a.factorial : ℂ) ^ b)⁻¹ •
    ∑ σ : Fin b → Equiv.Perm (Fin a), foulkesSummandMultilinear a b V σ

@[simp] theorem foulkesMultilinear_apply (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (v : Fin b × Fin a → V) :
    foulkesMultilinear a b V v = foulkesFormula a b V (fun j i => v (j, i)) := by
  classical
  simp [foulkesMultilinear, foulkesFormula]

end Problem346

end

end OAI
