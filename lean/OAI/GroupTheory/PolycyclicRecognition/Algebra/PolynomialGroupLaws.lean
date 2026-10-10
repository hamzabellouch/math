import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoordinateLieBrackets
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinWords

namespace OAI

/-! # Polynomial group laws in a fixed coordinate space

The binary Dynkin coefficients are fixed once in the original nilpotent
group. Changing its basis changes only the bracket. The group identities and
the straight-line one-parameter identities are closed conditions on this
finite-dimensional bracket parameter.
-/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped BigOperators

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The finite Dynkin expression evaluated with a variable bilinear law. -/
def bilinearDynkinPolynomial {c n : ℕ} (a : DynkinCoefficients c n)
    (B : V →L[ℝ] V →L[ℝ] V) (X : Fin n → V) : V :=
  ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
    a d w • evalBilinearWord B X (rightNestedWord d.val w)

/-- The binary multiplication polynomial, with fixed coefficients. -/
def dynkinProduct {c : ℕ} (a : DynkinCoefficients c 2)
    (B : V →L[ℝ] V →L[ℝ] V) (x y : V) : V :=
  bilinearDynkinPolynomial a B ![x, y]

theorem contDiff_bilinearDynkinPolynomial {c n : ℕ} {k : ℕ∞}
    (a : DynkinCoefficients c n) (B : P → V →L[ℝ] V →L[ℝ] V)
    (X : P → Fin n → V) (hB : ContDiff ℝ k B)
    (hX : ∀ i, ContDiff ℝ k (fun p => X p i)) :
    ContDiff ℝ k (fun p => bilinearDynkinPolynomial a (B p) (X p)) := by
  apply ContDiff.sum
  intro d _
  apply ContDiff.sum
  intro w _
  exact (contDiff_evalBilinearWord B X hB hX _).const_smul _

@[fun_prop] theorem contDiff_dynkinProduct {c : ℕ} {k : ℕ∞}
    (a : DynkinCoefficients c 2) (B : P → V →L[ℝ] V →L[ℝ] V)
    (x y : P → V) (hB : ContDiff ℝ k B)
    (hx : ContDiff ℝ k x) (hy : ContDiff ℝ k y) :
    ContDiff ℝ k (fun p => dynkinProduct a (B p) (x p) (y p)) := by
  apply contDiff_bilinearDynkinPolynomial a B (fun p => ![x p, y p]) hB
  intro i
  fin_cases i
  · exact hx
  · exact hy

@[fun_prop] theorem continuous_dynkinProduct {c : ℕ}
    (a : DynkinCoefficients c 2) (B : P → V →L[ℝ] V →L[ℝ] V)
    (x y : P → V) (hB : Continuous B) (hx : Continuous x) (hy : Continuous y) :
    Continuous (fun p => dynkinProduct a (B p) (x p) (y p)) := by
  exact (contDiff_dynkinProduct (k := 0) a B x y
    (contDiff_zero.mpr hB) (contDiff_zero.mpr hx) (contDiff_zero.mpr hy)).continuous

/-- Identities obeyed by a group in exponential coordinates, including its
actual straight-line one-parameter subgroups. -/
def PolynomialGroupLaws (m : V → V → V) : Prop :=
  (∀ x y z, m (m x y) z = m x (m y z)) ∧
  (∀ x, m 0 x = x) ∧ (∀ x, m x 0 = x) ∧
  (∀ x, m (-x) x = 0) ∧
  (∀ x (s t : ℝ), m (s • x) (t • x) = (s + t) • x)

/-- Exponential coordinates transfer the genuine group axioms, rather than
postulating them for a limiting polynomial. -/
theorem polynomialGroupLaws_of_exp {G : Type*} [Group G]
    (m : V → V → V) (Exp : V → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    (hm : ∀ x y, Exp (m x y) = Exp x * Exp y) : PolynomialGroupLaws m := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y z
    apply hinj
    simp only [hm, mul_assoc]
  · intro x
    apply hinj
    rw [hm, hzero, one_mul]
  · intro x
    apply hinj
    rw [hm, hzero, mul_one]
  · intro x
    apply hinj
    rw [hm, hneg, inv_mul_cancel, hzero]
  · intro x s t
    apply hinj
    rw [hm, hadd]

/-- These group identities persist under convergence of the bracket data. -/
theorem isClosed_dynkinGroupLaws {c : ℕ} (a : DynkinCoefficients c 2) :
    IsClosed {B : V →L[ℝ] V →L[ℝ] V | PolynomialGroupLaws (dynkinProduct a B)} := by
  have hc (x y : V) : Continuous (fun B : V →L[ℝ] V →L[ℝ] V =>
      dynkinProduct a B x y) :=
    continuous_dynkinProduct a id (fun _ => x) (fun _ => y)
      continuous_id continuous_const continuous_const
  simp only [PolynomialGroupLaws, ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro z
    exact isClosed_eq
      (continuous_dynkinProduct (V := V) a id _ _ continuous_id (hc x y) continuous_const)
      (continuous_dynkinProduct (V := V) a id _ _ continuous_id continuous_const (hc y z))
  refine (isClosed_iInter (fun x => isClosed_eq (hc 0 x) continuous_const)).inter ?_
  refine (isClosed_iInter (fun x => isClosed_eq (hc x 0) continuous_const)).inter ?_
  refine (isClosed_iInter (fun x => isClosed_eq (hc (-x) x) continuous_const)).inter ?_
  exact isClosed_iInter (fun x => isClosed_iInter (fun s =>
    isClosed_iInter (fun t => isClosed_eq (hc (s • x) (t • x)) continuous_const)))

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}

/-- Exact coordinate transport of the fixed binary polynomial. -/
theorem basis_dynkinProduct (b : Module.Basis (Fin n) ℝ L)
    {c : ℕ} (a : DynkinCoefficients c 2) (x y : L) :
    dynkinProduct a (basisBracket b) (b.equivFun x) (b.equivFun y) =
      b.equivFun (finiteDynkinPolynomial a ![x, y]) := by
  simp only [dynkinProduct, bilinearDynkinPolynomial, finiteDynkinPolynomial,
    map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  have hX : (![b.equivFun x, b.equivFun y] : Fin 2 → (Fin n → ℝ)) =
      fun i => b.equivFun (![x, y] i) := by
    funext i
    fin_cases i <;> rfl
  rw [hX]
  exact evalBilinearWord_basisBracket b ![x, y] (rightNestedWord d.val w)

end PolycyclicRecognition

end

end OAI
