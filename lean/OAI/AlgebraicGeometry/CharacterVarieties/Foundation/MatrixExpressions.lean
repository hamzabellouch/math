import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.MatrixPresentation

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.MatrixExpression
open scoped Classical Matrix
variable {R : Type*} [CommRing R]

/-- Fixed coordinate identification for a rank sum. The choice is retained uniformly throughout the finite incidence presentation. -/
def blockIndex {k : ℕ} (d : Fin k → ℕ) : Fin (∑ j, d j) ≃ ((j : Fin k) × Fin (d j)) :=
  (Fintype.equivFinOfCardEq (by simp [Fintype.card_sigma])).symm

/-- Direct-sum transport, with all summand indices retained. -/
def blockUnit {k : ℕ} (d : Fin k → ℕ) (g : (j : Fin k) → (Matrix (Fin (d j)) (Fin (d j)) R)ˣ) :
    (Matrix (Fin (∑ j, d j)) (Fin (∑ j, d j)) R)ˣ where
  val := (Matrix.blockDiagonal' (fun j => (g j : Matrix _ _ R))).submatrix (blockIndex d) (blockIndex d)
  inv := (Matrix.blockDiagonal' (fun j => (↑(g j)⁻¹ : Matrix _ _ R))).submatrix (blockIndex d) (blockIndex d)
  val_inv := by
    rw [Matrix.submatrix_mul_equiv]
    rw [← Matrix.blockDiagonal'_mul]
    simp only [Units.mul_inv]
    change (Matrix.blockDiagonal' (1 : (j : Fin k) → Matrix (Fin (d j)) (Fin (d j)) R)).submatrix
      (blockIndex d) (blockIndex d) = 1
    rw [Matrix.blockDiagonal'_one]
    exact Matrix.submatrix_one_equiv _
  inv_val := by
    rw [Matrix.submatrix_mul_equiv]
    rw [← Matrix.blockDiagonal'_mul]
    simp only [Units.inv_mul]
    change (Matrix.blockDiagonal' (1 : (j : Fin k) → Matrix (Fin (d j)) (Fin (d j)) R)).submatrix
      (blockIndex d) (blockIndex d) = 1
    rw [Matrix.blockDiagonal'_one]
    exact Matrix.submatrix_one_equiv _

/-- Ring change on an GL transport. -/
def mapUnit {S : Type*} [CommRing S] (φ : R →+* S) {n : ℕ}
    (g : (Matrix (Fin n) (Fin n) R)ˣ) : (Matrix (Fin n) (Fin n) S)ˣ :=
  Units.map (RingHom.mapMatrix φ).toMonoidHom g

@[simp] lemma mapUnit_val {S : Type*} [CommRing S] (φ : R →+* S) {n : ℕ}
    (g : (Matrix (Fin n) (Fin n) R)ˣ) :
    (mapUnit φ g : Matrix (Fin n) (Fin n) S)=(g : Matrix (Fin n) (Fin n) R).map φ := rfl

variable (R) (E : Type*) (rank : E → ℕ)

/-- Concrete words used at seams, corners, coarsened swaps, split vertices and surface relations. A block is an direct sum, not an abstract map between unnamed quotient modules. All inverses are the preserved GL inverse variables. -/
inductive Term : ℕ → Type _
  | generator (e : E) : Term (rank e)
  | constant {n : ℕ} (g : (Matrix (Fin n) (Fin n) R)ˣ) : Term n
  | mul {n : ℕ} (x y : Term n) : Term n
  | inv {n : ℕ} (x : Term n) : Term n
  | block {k : ℕ} (d : Fin k → ℕ) (x : (j : Fin k) → Term (d j)) : Term (∑ j, d j)

variable {R E rank}

def Term.eval {S : Type*} [CommRing S] (φ : R →+* S)
    (g : (e : E) → (Matrix (Fin (rank e)) (Fin (rank e)) S)ˣ) :
    {n : ℕ} → Term R E rank n → (Matrix (Fin n) (Fin n) S)ˣ
  | _, .generator e => g e
  | _, .constant h => mapUnit φ h
  | _, .mul x y => x.eval φ g * y.eval φ g
  | _, .inv x => (x.eval φ g)⁻¹
  | _, .block d x => blockUnit d (fun j => (x j).eval φ g)

end IntegralCharacterVarieties.MatrixExpression
namespace IntegralCharacterVarieties.MatrixExpression
open scoped Classical Matrix
open FiniteMatrixPresentation
variable {R : Type*} [CommRing R] {E : Type*} {rank : E → ℕ}

/-- The polynomial matrix expression, before imposing any inverses or incidence conditions. The sign retains both orientations of every transport. -/
def Term.raw : {n : ℕ} → Term R E rank n → Bool →
    Matrix (Fin n) (Fin n) (Polynomial R E (fun e => Fin (rank e)))
  | _, .generator e, b => variableMatrix R E (fun e => Fin (rank e)) e b
  | _, .constant h, b =>
    (if b then (↑h⁻¹ : Matrix _ _ R) else (h : Matrix _ _ R)).map MvPolynomial.C
  | _, .mul x y, b => if b then y.raw b*x.raw b else x.raw b*y.raw b
  | _, .inv x, b => x.raw (!b)
  | _, .block d x, b =>
    (Matrix.blockDiagonal' (fun j => (x j).raw b)).submatrix (blockIndex d) (blockIndex d)

def signed {S : Type*} [CommRing S] {n : ℕ}
    (g : (Matrix (Fin n) (Fin n) S)ˣ) (b : Bool) : Matrix (Fin n) (Fin n) S :=
  if b then (↑g⁻¹ : Matrix _ _ S) else (g : Matrix _ _ S)

variable {S : Type*} [CommRing S] [Algebra R S]

/-- Polynomial expression evaluation is exactly the corresponding composition, inversion and direct sum of local-system transports. -/
theorem Term.raw_evaluation {n : ℕ} (t : Term R E rank n)
    (g : (e : E) → (Matrix (Fin (rank e)) (Fin (rank e)) S)ˣ) (b : Bool) :
    (t.raw b).map (matrixEvaluation g).toRingHom=signed (t.eval (algebraMap R S) g) b := by
  induction t generalizing b with
  | generator e => exact matrixEvaluation_variable g e b
  | constant h =>
    cases b <;> ext i j <;>
      simp [Term.raw,Term.eval,signed,mapUnit,Matrix.map_apply,matrixEvaluation]
  | mul x y hx hy =>
    cases b <;> simp only [Term.raw,Bool.false_eq_true,↓reduceIte,Term.eval,signed,
      Matrix.map_mul,Units.val_mul,mul_inv_rev,hx,hy]
  | inv x hx =>
    cases b <;> simp only [Term.raw,Bool.not_false,Bool.not_true,hx,Term.eval,signed,
      Bool.false_eq_true,↓reduceIte,inv_inv]
  | block d x hx =>
    cases b <;>
      simp only [Term.raw,← Matrix.submatrix_map,Matrix.blockDiagonal'_map _ _ (map_zero _),hx,
        Term.eval,signed,Bool.false_eq_true,↓reduceIte]
    all_goals rfl

end IntegralCharacterVarieties.MatrixExpression
namespace IntegralCharacterVarieties.FlagCircuit
open scoped Classical Matrix
open MatrixExpression FiniteMatrixPresentation HomTransport
variable (R : Type*) [CommRing R] (E : Type*) (rank : E → ℕ) (J : Type*)

/-- An incidence constraint compares transported flags with their named quotients. Constant grade zero imposes full equality (e.g. a surface relation). Coarsening the grade imposes the unchanged direct-sum block at an interchange. -/
structure Data where
  dim : J → ℕ
  grade : (j : J) → Fin (dim j) → ℕ
  left : (j : J) → Term R E rank (dim j)
  right : (j : J) → Term R E rank (dim j)

namespace Data
variable {R E rank J} (D : Data R E rank J)

abbrev Entry := (j : J) × {ij : Fin (D.dim j) × Fin (D.dim j) // D.grade j ij.2 ≤ D.grade j ij.1}

def difference (j : J) : Term R E rank (D.dim j) :=
  .mul (.inv (D.right j)) (D.left j)

def equation : D.Entry → Polynomial R E (fun e => Fin (rank e))
  | ⟨j,⟨(i,k),_⟩⟩ => ((D.difference j).raw false) i k-(1 : Matrix _ _ _) i k

abbrev Coordinate := FiniteMatrixPresentation.Coordinate R E (fun e => Fin (rank e)) D.equation

variable {S : Type*} [CommRing S] [Algebra R S]

/-- Geometric meaning, including the grade identifications, not just ranks or underlying flag subspaces. It is meaningful over full integer rings as well. -/
def Holds (g : (e : E) → (Matrix (Fin (rank e)) (Fin (rank e)) S)ˣ) : Prop :=
  ∀ j, SameFramedFlag (D.grade j)
    (matrixUnitEquiv ((D.left j).eval (algebraMap R S) g))
    (matrixUnitEquiv ((D.right j).eval (algebraMap R S) g))

abbrev Solution (S : Type*) [CommRing S] [Algebra R S] :=
  {g : (e : E) → (Matrix (Fin (rank e)) (Fin (rank e)) S)ˣ // D.Holds g}

lemma equation_evaluation (g : (e : E) → (Matrix (Fin (rank e)) (Fin (rank e)) S)ˣ)
    (j : J) (i k : Fin (D.dim j)) (hik : D.grade j k ≤ D.grade j i) :
    matrixEvaluation g (D.equation ⟨j,⟨(i,k),hik⟩⟩)=
      ((↑((D.right j).eval (algebraMap R S) g)⁻¹ : Matrix (Fin (D.dim j)) (Fin (D.dim j)) S)*
        ((D.left j).eval (algebraMap R S) g : Matrix (Fin (D.dim j)) (Fin (D.dim j)) S)) i k-
        (1 : Matrix _ _ S) i k := by
  have h := congrFun (congrFun ((D.difference j).raw_evaluation g false) i) k
  change matrixEvaluation g (((D.difference j).raw false) i k)=
    ((↑((D.right j).eval (algebraMap R S) g)⁻¹ : Matrix (Fin (D.dim j)) (Fin (D.dim j)) S)*
      ((D.left j).eval (algebraMap R S) g : Matrix (Fin (D.dim j)) (Fin (D.dim j)) S)) i k at h
  change matrixEvaluation g (((D.difference j).raw false) i k-(1 : Matrix _ _ _) i k)=_
  rw [map_sub,h]
  congr 1
  by_cases he : i=k
  · subst k; simp only [Matrix.one_apply_eq,map_one]
  · simp only [Matrix.one_apply_ne he,map_zero]

/-- These are precisely the finite polynomial equations for all identified-flag constraints. No event or wrap relation is omitted. -/
theorem holds_iff_equations (g : (e : E) → (Matrix (Fin (rank e)) (Fin (rank e)) S)ˣ) :
    D.Holds g ↔ ∀ z, matrixEvaluation g (D.equation z)=0 := by
  simp only [Holds,sameFramedFlag_matrix_iff]
  constructor
  · intro h
    rintro ⟨j,⟨⟨i,k⟩,hik⟩⟩
    rw [D.equation_evaluation g j i k hik,sub_eq_zero]
    exact h j i k hik
  · intro h j i k hik
    have hh := h ⟨j,⟨(i,k),hik⟩⟩
    rwa [D.equation_evaluation g j i k hik,sub_eq_zero] at hh

/-- The finite algebra representing the split-frame incidence scheme. This is not an abstract affine-bundle interface: all entries and all relations are in the explicit quotient algebra, and its ring-valued points are identified. -/
def pointsEquiv : D.Solution S ≃ (D.Coordinate →ₐ[R] S) :=
  (Equiv.subtypeEquivRight (fun g => D.holds_iff_equations g)).trans
    (FiniteMatrixPresentation.pointsEquiv D.equation)

instance finiteType [Finite E] : Algebra.FiniteType R D.Coordinate := inferInstance
instance finiteEntry [Finite J] : Finite D.Entry := inferInstance

end Data
end IntegralCharacterVarieties.FlagCircuit


open scoped Classical

end

end OAI
