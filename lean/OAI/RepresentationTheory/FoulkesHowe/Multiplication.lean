import OAI.RepresentationTheory.FoulkesHowe.Model

namespace OAI

noncomputable section
open scoped BigOperators Pointwise
universe u

namespace Problem346

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- Concatenating two lists of factors multiplies their symmetric monomials. -/
theorem symMonomialRaw_append (m n : ℕ) (v : Fin m → V) (w : Fin n → V) :
    symMonomialRaw (m + n) V (Fin.append v w) =
      symMonomialRaw m V v * symMonomialRaw n V w := by
  simp [symMonomialRaw, Fin.prod_univ_add]

/-- Products of homogeneous spans have the sum of their degrees. -/
theorem symPowSubmodule_mul (m n : ℕ) :
    symPowSubmodule m V * symPowSubmodule n V = symPowSubmodule (m + n) V := by
  unfold symPowSubmodule
  rw [Submodule.span_mul_span]
  apply congrArg (Submodule.span ℂ)
  ext z
  constructor
  · rintro ⟨x, ⟨v, rfl⟩, y, ⟨w, rfl⟩, rfl⟩
    exact ⟨Fin.append v w, symMonomialRaw_append m n v w⟩
  · rintro ⟨v, rfl⟩
    refine ⟨symMonomialRaw m V (fun i => v (Fin.castAdd n i)),
      ⟨_, rfl⟩, symMonomialRaw n V (fun i => v (Fin.natAdd m i)), ⟨_, rfl⟩, ?_⟩
    simp [symMonomialRaw, Fin.prod_univ_add]

/-- The product of two elements of the indicated homogeneous pieces. -/
theorem symPow_mul_mem (m n : ℕ) (x : SymPow m V) (y : SymPow n V) :
    (x : SymmetricAlgebra ℂ V) * (y : SymmetricAlgebra ℂ V) ∈
      symPowSubmodule (m+n) V := by
  rw [← symPowSubmodule_mul]
  exact Submodule.mul_mem_mul x.property y.property

/-- Graded multiplication in the symmetric algebra, as a bilinear map. -/
def symPowMul (m n : ℕ) :
    SymPow m V →ₗ[ℂ] SymPow n V →ₗ[ℂ] SymPow (m+n) V :=
  LinearMap.mk₂ ℂ
    (fun x y => ⟨(x : SymmetricAlgebra ℂ V) * (y : SymmetricAlgebra ℂ V),
      symPow_mul_mem m n x y⟩)
    (by intros; apply Subtype.ext; exact add_mul _ _ _)
    (by intros; apply Subtype.ext; exact smul_mul_assoc _ _ _)
    (by intros; apply Subtype.ext; exact mul_add _ _ _)
    (by intros; apply Subtype.ext; exact mul_smul_comm _ _ _)

@[simp] theorem symPowMul_coe (m n : ℕ) (x : SymPow m V) (y : SymPow n V) :
    (symPowMul m n x y : SymmetricAlgebra ℂ V) =
      (x : SymmetricAlgebra ℂ V) * (y : SymmetricAlgebra ℂ V) := rfl

@[simp] theorem symPowMul_symMonomial (m n : ℕ) (v : Fin m → V) (w : Fin n → V) :
    symPowMul m n (symMonomial m V v) (symMonomial n V w) =
      symMonomial (m+n) V (Fin.append v w) := by
  apply Subtype.ext
  exact (symMonomialRaw_append m n v w).symm

/-- Transport a homogeneous element across an equality of degrees. -/
def symPowCast {m n : ℕ} (h : m = n) : SymPow m V ≃ₗ[ℂ] SymPow n V :=
  LinearEquiv.ofEq _ _ (congrArg (fun k => symPowSubmodule k V) h)

@[simp] theorem symPowCast_coe {m n : ℕ} (h : m = n) (x : SymPow m V) :
    (symPowCast h x : SymmetricAlgebra ℂ V) = x := rfl

@[simp] theorem symPowCast_symMonomial {m n : ℕ} (h : m = n) (v : Fin m → V) :
    symPowCast h (symMonomial m V v) =
      symMonomial n V (fun i => v (Fin.cast h.symm i)) := by
  subst h
  rfl

/-- Multiplication followed by transport to a specified total degree. -/
def symPowMulCast (m n b : ℕ) (h : m+n=b) :
    SymPow m V →ₗ[ℂ] SymPow n V →ₗ[ℂ] SymPow b V :=
  (LinearMap.llcomp ℂ (SymPow n V) (SymPow (m+n) V) (SymPow b V)
    (symPowCast h).toLinearMap).comp (symPowMul m n)

@[simp] theorem symPowMulCast_coe (m n b : ℕ) (h : m+n=b)
    (x : SymPow m V) (y : SymPow n V) :
    (symPowMulCast m n b h x y : SymmetricAlgebra ℂ V) =
      (x : SymmetricAlgebra ℂ V) * (y : SymmetricAlgebra ℂ V) := rfl

/-- The raw monomial of a constant tuple is a power. -/
theorem symMonomialRaw_const (n : ℕ) (v : V) :
    symMonomialRaw n V (fun _ => v) = SymmetricAlgebra.ι ℂ V v ^ n := by
  simp [symMonomialRaw]

end Problem346

end

end OAI
