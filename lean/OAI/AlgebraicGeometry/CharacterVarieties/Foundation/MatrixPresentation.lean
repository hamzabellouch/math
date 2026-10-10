import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.Flags
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Finiteness.Basic

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.FiniteMatrixPresentation

variable (R : Type*) [CommRing R] (E : Type*) (ι : E → Type*)
variable [∀ e, Fintype (ι e)] [∀ e, DecidableEq (ι e)]

/-- Every transport and every chosen split frame has its own occurrence index. The sign distinguishes its matrix from its inverse, not a second occurrence. -/
abbrev Entry := (e : E) × Bool × (ι e × ι e)
abbrev Polynomial := MvPolynomial (Entry E ι) R

def variableMatrix (e : E) (b : Bool) : Matrix (ι e) (ι e) (Polynomial R E ι) :=
  fun i j => MvPolynomial.X ⟨e,b,i,j⟩

variable {J : Type*} (equation : J → Polynomial R E ι)

/-- The inverse equations are imposed in both directions over the full ring. Every incidence equation is included individually, even for repeated sides. -/
inductive Relation : Polynomial R E ι → Prop
  | inverse (e : E) (b : Bool) (i j : ι e) : Relation
      ((variableMatrix R E ι e b * variableMatrix R E ι e (!b)) i j -
        (1 : Matrix (ι e) (ι e) (Polynomial R E ι)) i j)
  | incidence (j : J) : Relation (equation j)

def relationIdeal : Ideal (Polynomial R E ι) :=
  Ideal.span {f | Relation R E ι equation f}

abbrev Coordinate := Polynomial R E ι ⧸ relationIdeal R E ι equation

variable {R E ι}

def universalMatrix (e : E) (b : Bool) : Matrix (ι e) (ι e) (Coordinate R E ι equation) :=
  (variableMatrix R E ι e b).map (Ideal.Quotient.mk (relationIdeal R E ι equation))

lemma relation_zero (f : Polynomial R E ι) (hf : Relation R E ι equation f) :
    Ideal.Quotient.mk (relationIdeal R E ι equation) f = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hf)

lemma universal_inverse (e : E) (b : Bool) :
    universalMatrix equation e b * universalMatrix equation e (!b) = 1 := by
  ext i j
  have h := relation_zero equation _ (Relation.inverse e b i j)
  rw [map_sub,sub_eq_zero] at h
  change ((variableMatrix R E ι e b * variableMatrix R E ι e (!b)).map
    (Ideal.Quotient.mk (relationIdeal R E ι equation))) i j =
    ((1 : Matrix (ι e) (ι e) (Polynomial R E ι)).map
    (Ideal.Quotient.mk (relationIdeal R E ι equation))) i j at h
  rw [Matrix.map_mul,Matrix.map_one _ (map_zero _) (map_one _)] at h
  exact h

/-- These are general linear transports, not only matrices with nonvanishing determinant at complex points. -/
def universalUnit (e : E) : (Matrix (ι e) (ι e) (Coordinate R E ι equation))ˣ where
  val := universalMatrix equation e false
  inv := universalMatrix equation e true
  val_inv := universal_inverse equation e false
  inv_val := universal_inverse equation e true

variable {S : Type*} [CommRing S] [Algebra R S]

/-- Evaluation retains every occurrence's forward and backward transport. -/
def matrixEvaluation (g : (e : E) → (Matrix (ι e) (ι e) S)ˣ) :
    Polynomial R E ι →ₐ[R] S :=
  MvPolynomial.aeval (fun ⟨e,b,i,j⟩ => if b then (↑(g e)⁻¹ : Matrix _ _ S) i j
    else (↑(g e) : Matrix _ _ S) i j)

@[simp] lemma matrixEvaluation_variable (g : (e : E) → (Matrix (ι e) (ι e) S)ˣ)
    (e : E) (b : Bool) :
    (variableMatrix R E ι e b).map (matrixEvaluation g).toRingHom =
      if b then (↑(g e)⁻¹ : Matrix _ _ S) else (↑(g e) : Matrix _ _ S) := by
  ext i j
  cases b <;> simp [variableMatrix,matrixEvaluation]

/-- A split-frame solution of the finite incidence equations over S. -/
abbrev Solution (S : Type*) [CommRing S] [Algebra R S] :=
  {g : (e : E) → (Matrix (ι e) (ι e) S)ˣ // ∀ j, matrixEvaluation g (equation j)=0}

lemma ideal_le_ker (g : Solution equation S) :
    relationIdeal R E ι equation ≤ RingHom.ker (matrixEvaluation g.val).toRingHom := by
  apply Ideal.span_le.mpr
  intro f hf
  change matrixEvaluation g.val f=0
  cases hf with
  | incidence j => exact g.property j
  | inverse e b i j =>
    rw [map_sub,sub_eq_zero]
    have hinv : ((variableMatrix R E ι e b * variableMatrix R E ι e (!b)).map
        (matrixEvaluation g.val).toRingHom) = 1 := by
      rw [Matrix.map_mul,matrixEvaluation_variable,matrixEvaluation_variable]
      cases b <;> simp
    have he := congrFun (congrFun hinv i) j
    change matrixEvaluation g.val
      ((variableMatrix R E ι e b * variableMatrix R E ι e (!b)) i j) = (1 : Matrix _ _ S) i j at he
    rw [he]
    by_cases hij : i=j
    · subst j
      simp only [Matrix.one_apply_eq,map_one]
    · simp only [Matrix.one_apply_ne hij,map_zero]

def solutionToPoint (g : Solution equation S) : Coordinate R E ι equation →ₐ[R] S :=
  Ideal.Quotient.liftₐ (relationIdeal R E ι equation) (matrixEvaluation g.val) (ideal_le_ker equation g)

@[simp] lemma solutionToPoint_mk (g : Solution equation S) (f : Polynomial R E ι) :
    solutionToPoint equation g (Ideal.Quotient.mk (relationIdeal R E ι equation) f) =
      matrixEvaluation g.val f := rfl

/-- Reading the universal transports along an ring-valued point. -/
def pointMatrices (φ : Coordinate R E ι equation →ₐ[R] S) (e : E) :
    (Matrix (ι e) (ι e) S)ˣ :=
  Units.map (RingHom.mapMatrix φ.toRingHom).toMonoidHom (universalUnit equation e)

@[simp] lemma pointMatrices_val (φ : Coordinate R E ι equation →ₐ[R] S) (e : E) :
    (↑(pointMatrices equation φ e) : Matrix _ _ S) =
      (universalMatrix equation e false).map φ.toRingHom := rfl

@[simp] lemma pointMatrices_inv (φ : Coordinate R E ι equation →ₐ[R] S) (e : E) :
    (↑(pointMatrices equation φ e)⁻¹ : Matrix _ _ S) =
      (universalMatrix equation e true).map φ.toRingHom := rfl

lemma point_evaluation (φ : Coordinate R E ι equation →ₐ[R] S) :
    matrixEvaluation (pointMatrices equation φ) =
      φ.comp (Ideal.Quotient.mkₐ R (relationIdeal R E ι equation)) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨e,b,i,j⟩
  simp only [matrixEvaluation,MvPolynomial.aeval_X]
  cases b <;> rfl

def pointToSolution (φ : Coordinate R E ι equation →ₐ[R] S) : Solution equation S :=
  ⟨pointMatrices equation φ,by
    intro j
    rw [point_evaluation]
    change φ (Ideal.Quotient.mk (relationIdeal R E ι equation) (equation j))=0
    rw [relation_zero equation _ (Relation.incidence j),map_zero]⟩

/-- Exact representability over arbitrary coefficient rings, including the full ring of integers. No reduction, localization or rank condition is dropped. -/
def pointsEquiv : Solution equation S ≃ (Coordinate R E ι equation →ₐ[R] S) where
  toFun := solutionToPoint equation
  invFun := pointToSolution equation
  left_inv g := by
    apply Subtype.ext
    funext e
    apply Units.ext
    ext i j
    change matrixEvaluation g.val (MvPolynomial.X ⟨e,false,i,j⟩) = _
    simp [matrixEvaluation]
  right_inv φ := by
    apply Ideal.Quotient.algHom_ext
    rw [show (solutionToPoint equation (pointToSolution equation φ)).comp
      (Ideal.Quotient.mkₐ R (relationIdeal R E ι equation)) =
        matrixEvaluation (pointMatrices equation φ) from rfl]
    exact point_evaluation equation φ

/-- There are finitely many matrix entries when the diagram is finite. -/
instance finiteEntry [Finite E] [∀ e, Finite (ι e)] : Finite (Entry E ι) := inferInstance

instance finiteType [Finite E] [∀ e, Finite (ι e)] :
    Algebra.FiniteType R (Coordinate R E ι equation) := by
  infer_instance

end IntegralCharacterVarieties.FiniteMatrixPresentation

end

end OAI
