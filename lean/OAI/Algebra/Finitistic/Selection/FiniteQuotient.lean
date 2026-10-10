import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

namespace OAI
/-!
Exact prerequisites for Section 2 of v5s9.15.

These are the variable-coefficient elementary-matrix calculations in the
finite-quotient construction, over the actual rings F₂[t]/(t^m - 1).
They do not establish the paper's main homological theorem.
-/

open Matrix Polynomial

namespace LittleFinitistic

section ElementaryMatrices

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def transvection (i j : ι) (a : R) : Matrix ι ι R := 1 + Matrix.single i j a

theorem single_square_zero (i j : ι) (hij : i ≠ j) (a : R) :
    (Matrix.single i j a : Matrix ι ι R) * Matrix.single i j a = 0 := by
  exact Matrix.single_mul_single_of_ne a i j i (Ne.symm hij) a

theorem transvection_mul_neg (i j : ι) (hij : i ≠ j) (a : R) :
    transvection i j a * transvection i j (-a) = 1 := by
  simp only [transvection, ← Matrix.single_neg, mul_add, add_mul, mul_one, one_mul,
    mul_neg, single_square_zero i j hij]
  abel

def transvectionUnit (i j : ι) (hij : i ≠ j) (a : R) : (Matrix ι ι R)ˣ where
  val := transvection i j a
  inv := transvection i j (-a)
  val_inv := transvection_mul_neg i j hij a
  inv_val := by simpa using transvection_mul_neg i j hij (-a)

theorem transvection_same (i j : ι) (hij : i ≠ j) (a b : R) :
    transvection i j a * transvection i j b = transvection i j (a + b) := by
  simp only [transvection, mul_add, add_mul, mul_one, one_mul,
    Matrix.single_mul_single_of_ne a i j i (Ne.symm hij) b, Matrix.single_add]
  abel

theorem nilpotent_commutator {A : Type*} [Ring A] (a b : A)
    (haa : a * a = 0) (hbb : b * b = 0) (hba : b * a = 0) :
    (1+a)*(1+b)*(1-a)*(1-b) = 1+a*b := by
  calc
    (1+a)*(1+b)*(1-a)*(1-b) =
        1 + a*b - a*a - b*a - a*b*a - b*b - a*b*b + a*a*b + b*a*b + a*b*a*b := by
          noncomm_ring
    _ = 1 + a*b := by
      simp [haa, hbb, hba, mul_assoc]

theorem transvection_commutator (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    transvection i j a * transvection j k b *
      transvection i j (-a) * transvection j k (-b) =
      transvection i k (a*b) := by
  have haa := single_square_zero i j hij a
  have hbb := single_square_zero j k hjk b
  have hba : (Matrix.single j k b : Matrix ι ι R) * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne b j k i (Ne.symm hik) a
  simpa [transvection, ← Matrix.single_neg, sub_eq_add_neg] using
    nilpotent_commutator (Matrix.single i j a) (Matrix.single j k b) haa hbb hba

theorem transvection_commute (i j k l : ι)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
    Commute (transvection i j a) (transvection k l b) := by
  show transvection i j a * transvection k l b =
    transvection k l b * transvection i j a
  simp only [transvection, mul_add, add_mul, mul_one, one_mul,
    Matrix.single_mul_single_of_ne a i j k hjk b,
    Matrix.single_mul_single_of_ne b k l i hli a]
  abel

omit [Fintype ι] in
theorem transvection_injective (i j : ι) (hij : i ≠ j) :
    Function.Injective (transvection (R := R) i j) := by
  intro a b h
  have := congrArg (fun M : Matrix ι ι R => M i j) h
  simpa [transvection, Matrix.single, Matrix.one_apply, hij] using this

def diagonalUnit (d : ι → Rˣ) : (Matrix ι ι R)ˣ where
  val := Matrix.diagonal (fun i => (d i : R))
  inv := Matrix.diagonal (fun i => ((d i)⁻¹ : Rˣ))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp

theorem diagonal_single_conjugation (d : ι → Rˣ) (i j : ι) (a : R) :
    (diagonalUnit d : Matrix ι ι R) * Matrix.single i j a *
      ((diagonalUnit d)⁻¹ : (Matrix ι ι R)ˣ) =
      Matrix.single i j ((d i : R) * a * ((d j)⁻¹ : Rˣ)) := by
  ext k l
  change (Matrix.diagonal (fun s => (d s : R)) * Matrix.single i j a *
      Matrix.diagonal (fun s => (((d s)⁻¹ : Rˣ) : R))) k l = _
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases hi : i=k <;> by_cases hj : j=l <;>
    simp [hi, hj]

theorem diagonal_transvection_conjugation (d : ι → Rˣ) (i j : ι) (a : R) :
    (diagonalUnit d : Matrix ι ι R) * transvection i j a *
      ((diagonalUnit d)⁻¹ : (Matrix ι ι R)ˣ) =
      transvection i j ((d i : R) * a * ((d j)⁻¹ : Rˣ)) := by
  simp only [transvection,mul_add,add_mul,mul_one,Units.mul_inv,diagonal_single_conjugation]

theorem diagonalUnit_commute (d e : ι → Rˣ) : Commute (diagonalUnit d) (diagonalUnit e) := by
  apply Units.ext
  exact (Matrix.commute_diagonal (d₁ := fun i => (d i : R))
    (d₂ := fun i => (e i : R))).eq

theorem transvectionUnit_commute (i j k l : ι) (hij : i≠j) (hkl : k≠l)
    (hjk : j≠k) (hli : l≠i) (a b : R) :
    Commute (transvectionUnit i j hij a) (transvectionUnit k l hkl b) := by
  apply Units.ext
  exact (transvection_commute i j k l hjk hli a b).eq

open scoped commutatorElement in
theorem transvectionUnit_commutator (i j k : ι)
    (hij : i≠j) (hjk : j≠k) (hik : i≠k) (a b : R) :
    ⁅transvectionUnit i j hij a,transvectionUnit j k hjk b⁆ =
      transvectionUnit i k hik (a*b) := by
  apply Units.ext
  exact transvection_commutator i j k hij hjk hik a b

theorem transvectionUnit_conjugation (d : ι → Rˣ) (i j : ι) (hij : i≠j) (a : R) :
    diagonalUnit d * transvectionUnit i j hij a * (diagonalUnit d)⁻¹ =
      transvectionUnit i j hij ((d i : R) * a * ((d j)⁻¹ : Rˣ)) := by
  apply Units.ext
  exact diagonal_transvection_conjugation d i j a

end ElementaryMatrices

noncomputable def cyclicPolynomial (m : ℕ) : Polynomial (ZMod 2) := X^m - C 1
abbrev CyclicRing (m : ℕ) := AdjoinRoot (cyclicPolynomial m)

theorem cyclicPolynomial_monic (m : ℕ) (hm : m ≠ 0) :
    (cyclicPolynomial m).Monic := Polynomial.monic_X_pow_sub_C 1 hm

theorem cyclicPolynomial_degree (m : ℕ) :
    (cyclicPolynomial m).natDegree = m := Polynomial.natDegree_X_pow_sub_C

noncomputable def cyclicBasis (m : ℕ) (hm : m ≠ 0) :
    Module.Basis (Fin m) (ZMod 2) (CyclicRing m) :=
  ((AdjoinRoot.powerBasis' (cyclicPolynomial_monic m hm)).basis).reindex
    (finCongr (cyclicPolynomial_degree m))

theorem cyclicRing_finite (m : ℕ) (hm : m ≠ 0) : Finite (CyclicRing m) := by
  exact Finite.of_injective (cyclicBasis m hm).repr (cyclicBasis m hm).repr.injective

theorem cyclic_root_pow (m : ℕ) :
    AdjoinRoot.root (cyclicPolynomial m) ^ m = (1 : CyclicRing m) := by
  have h : AdjoinRoot.mk (cyclicPolynomial m) (X^m - C 1) = 0 :=
    AdjoinRoot.mk_eq_zero.mpr (dvd_refl _)
  rw [map_sub, map_pow, AdjoinRoot.mk_X, Polynomial.C_1, map_one] at h
  exact sub_eq_zero.mp h

theorem cyclic_root_isUnit (m : ℕ) (hm : 0 < m) :
    IsUnit (AdjoinRoot.root (cyclicPolynomial m)) := by
  exact IsUnit.of_pow_eq_one (cyclic_root_pow m) (Nat.ne_of_gt hm)

theorem cyclicBasis_apply (m : ℕ) (hm : m ≠ 0) (i : Fin m) :
    cyclicBasis m hm i = AdjoinRoot.root (cyclicPolynomial m) ^ (i : ℕ) := by
  simp only [cyclicBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen]
  rfl

theorem cyclic_powers_independent (m : ℕ) (hm : m ≠ 0) :
    LinearIndependent (ZMod 2)
      (fun i : Fin m => AdjoinRoot.root (cyclicPolynomial m) ^ (i : ℕ)) := by
  have h : (fun i : Fin m => cyclicBasis m hm i) =
      (fun i : Fin m => AdjoinRoot.root (cyclicPolynomial m) ^ (i : ℕ)) :=
    funext (cyclicBasis_apply m hm)
  rw [← h]
  exact (cyclicBasis m hm).linearIndependent

/-- The central coefficient embedding in the displayed 5-by-5 matrix model. -/
noncomputable def centralMatrix (m : ℕ) (c : Fin m → ZMod 2) :
    Matrix (Fin 5) (Fin 5) (CyclicRing m) :=
  transvection 0 4 (∑ i, c i • AdjoinRoot.root (cyclicPolynomial m) ^ (i : ℕ))

theorem centralMatrix_zero (m : ℕ) : centralMatrix m 0 = 1 := by
  simp [centralMatrix, transvection]

theorem centralMatrix_add (m : ℕ) (c d : Fin m → ZMod 2) :
    centralMatrix m (c + d) = centralMatrix m c * centralMatrix m d := by
  rw [centralMatrix, centralMatrix, centralMatrix,
    transvection_same 0 4 (by decide)]
  congr 1
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem centralMatrix_injective (m : ℕ) (hm : m ≠ 0) :
    Function.Injective (centralMatrix m) := by
  intro c d h
  have hs := transvection_injective (R := CyclicRing m) (0 : Fin 5) 4 (by decide) h
  have hz : ∑ i : Fin m, (c i - d i) •
      AdjoinRoot.root (cyclicPolynomial m) ^ (i : ℕ) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hs, sub_self]
  have hc := (linearIndependent_iff'.mp (cyclic_powers_independent m hm))
    Finset.univ (fun i => c i - d i) (by simpa using hz)
  funext i
  exact sub_eq_zero.mp (hc i (Finset.mem_univ i))

theorem centralMatrix_involution (m : ℕ) (c : Fin m → ZMod 2) :
    centralMatrix m c * centralMatrix m c = 1 := by
  rw [← centralMatrix_add]
  have h : c + c = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (c i)
  rw [h, centralMatrix_zero]

/-- This is the concrete copy of the elementary abelian 2-group used by the
paper's finite matrix quotient. Its realization as a quotient of the presented
group remains separate from the verified embedding below. -/
noncomputable def centralEmbedding (m : ℕ) :
    Multiplicative (Fin m → ZMod 2) →* (Matrix (Fin 5) (Fin 5) (CyclicRing m))ˣ where
  toFun c :=
    { val := centralMatrix m c.toAdd
      inv := centralMatrix m c.toAdd
      val_inv := centralMatrix_involution m c.toAdd
      inv_val := centralMatrix_involution m c.toAdd }
  map_one' := by
    apply Units.ext
    exact centralMatrix_zero m
  map_mul' c d := by
    apply Units.ext
    exact centralMatrix_add m c.toAdd d.toAdd

theorem centralEmbedding_injective (m : ℕ) (hm : m ≠ 0) :
    Function.Injective (centralEmbedding m) := by
  intro c d h
  exact (centralMatrix_injective m hm) (congrArg Units.val h)

end LittleFinitistic

end OAI
