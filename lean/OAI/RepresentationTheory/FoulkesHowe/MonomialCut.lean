import OAI.RepresentationTheory.FoulkesHowe.Multiplication

namespace OAI

noncomputable section

namespace Problem346

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Splitting a list of equal factors at a cutoff is graded multiplication of two pure powers. -/
theorem symMonomial_cut (r m : ℕ) (x y : V) :
    symMonomial (r+m) V (fun j => if j.val < r then x else y) =
      symPowMul r m (symMonomial r V (fun _ => x))
        (symMonomial m V (fun _ => y)) := by
  rw [symPowMul_symMonomial]
  congr 1
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp
  · simp

/-- Cast-free raw form of the cutoff identity. -/
theorem symMonomialRaw_cut (r m : ℕ) (x y : V) :
    symMonomialRaw (r+m) V (fun j => if j.val < r then x else y) =
      SymmetricAlgebra.ι ℂ V x ^ r * SymmetricAlgebra.ι ℂ V y ^ m := by
  have h := congrArg (fun z : SymPow (r+m) V => (z : SymmetricAlgebra ℂ V))
    (symMonomial_cut r m x y)
  simpa [symMonomial, symPowMul_coe, symMonomialRaw_const] using h

/-- The all-row terminal cutoff in the second transfer matches its common-power product form. -/
theorem multilinear_cut_endpoint (r m : ℕ)
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (x t : V) (v : Fin r → V) :
    T (Fin.cons (symMonomial (r+m) V (fun _ => t))
      (fun i => symMonomial (r+m) V (fun j => if j.val < r then x else v i))) =
    T (Fin.cons (symMonomial (r+m) V (fun _ => t))
      (fun i => symPowMul r m (symMonomial r V (fun _ => x))
        (symMonomial m V (fun _ => v i)))) := by
  simp only [symMonomial_cut]

/-- Vanishing on arbitrary residual products gives vanishing on the terminal cutoff. -/
theorem multilinear_cut_endpoint_zero (r m : ℕ)
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (h : ∀ x t : V, ∀ Q : Fin r → SymPow m V,
      T (Fin.cons (symMonomial (r+m) V (fun _ => t))
        (fun i => symPowMul r m (symMonomial r V (fun _ => x)) (Q i))) = 0)
    (x t : V) (v : Fin r → V) :
    T (Fin.cons (symMonomial (r+m) V (fun _ => t))
      (fun i => symMonomial (r+m) V (fun j => if j.val < r then x else v i))) = 0 := by
  rw [multilinear_cut_endpoint]
  exact h x t (fun i => symMonomial m V (fun _ => v i))

end Problem346

end

end OAI
