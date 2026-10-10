import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Quotient

namespace OAI

namespace PiExponentSiegel.W08

open Polynomial

variable {K : Type*} [Field K]

noncomputable def coordinatePolynomialSplit (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] Polynomial (MvPolynomial (Fin n) K) :=
  MvPolynomial.finSuccEquiv K n

noncomputable def coordinateCoefficientSplit (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin n) K[X] :=
  (MvPolynomial.renameEquiv K (_root_.finSuccEquiv n)).trans
    (MvPolynomial.optionEquivRight K (Fin n))

@[simp] theorem coordinateCoefficientSplit_X_zero (n : ℕ) :
    coordinateCoefficientSplit (K := K) n (MvPolynomial.X 0) = MvPolynomial.C Polynomial.X := by
  simp [coordinateCoefficientSplit]

@[simp] theorem coordinateCoefficientSplit_X_succ (n : ℕ) (i : Fin n) :
    coordinateCoefficientSplit (K := K) n (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [coordinateCoefficientSplit]

@[simp] theorem coordinateCoefficientSplit_C (n : ℕ) (a : K) :
    coordinateCoefficientSplit n (MvPolynomial.C a) = MvPolynomial.C (Polynomial.C a) := by
  simp [coordinateCoefficientSplit]

theorem coordinateCoefficientSplit_aeval (n : ℕ) (f : K[X]) :
    coordinateCoefficientSplit n (Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1))) f) =
      MvPolynomial.C f := by
  have h : (coordinateCoefficientSplit (K := K) n).toAlgHom.comp
      (Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1)))) =
      IsScalarTower.toAlgHom K K[X] (MvPolynomial (Fin n) K[X]) := by
    apply Polynomial.algHom_ext
    change coordinateCoefficientSplit n
      (Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1))) Polynomial.X) =
      MvPolynomial.C Polynomial.X
    rw [Polynomial.aeval_X, coordinateCoefficientSplit_X_zero]
  exact AlgHom.congr_fun h f

noncomputable def coordinateMinpolyIdeal (n : ℕ) (f : K[X]) :
    Ideal (MvPolynomial (Fin (n + 1)) K) :=
  Ideal.span {Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1))) f}

theorem coordinateMinpolyIdeal_map (n : ℕ) (f : K[X]) :
    (coordinateMinpolyIdeal n f).map (coordinateCoefficientSplit n).toRingEquiv.toRingHom =
      (Ideal.span {f}).map (MvPolynomial.C : K[X] →+* MvPolynomial (Fin n) K[X]) := by
  simp only [coordinateMinpolyIdeal, Ideal.map_span, Set.image_singleton]
  congr 1
  exact congrArg Set.singleton (coordinateCoefficientSplit_aeval n f)

noncomputable def coefficientAdjoinRootQuotientEquiv (n : ℕ) (f : K[X]) :
    (MvPolynomial (Fin n) K[X] ⧸
      (Ideal.span {f}).map (MvPolynomial.C : K[X] →+* MvPolynomial (Fin n) K[X])) ≃ₐ[K]
      MvPolynomial (Fin n) (AdjoinRoot f) :=
  ((MvPolynomial.quotientEquivQuotientMvPolynomial
    (σ := Fin n) (Ideal.span {f} : Ideal K[X])).symm).restrictScalars K

@[simp] theorem coefficientAdjoinRootQuotientEquiv_mk (n : ℕ) (f : K[X])
    (p : MvPolynomial (Fin n) K[X]) :
    coefficientAdjoinRootQuotientEquiv n f (Ideal.Quotient.mk _ p) =
      MvPolynomial.map (AdjoinRoot.mk f) p := by
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]
  rfl

noncomputable def coordinateMinpolyQuotientEquiv (n : ℕ) (f : K[X]) :
    (MvPolynomial (Fin (n + 1)) K ⧸ coordinateMinpolyIdeal n f) ≃ₐ[K]
      MvPolynomial (Fin n) (AdjoinRoot f) :=
  (Ideal.quotientEquivAlg (coordinateMinpolyIdeal n f) _
    (coordinateCoefficientSplit n) (coordinateMinpolyIdeal_map n f).symm).trans
      (coefficientAdjoinRootQuotientEquiv n f)

theorem coordinateMinpolyQuotientEquiv_mk (n : ℕ) (f : K[X])
    (p : MvPolynomial (Fin (n+1)) K) :
    coordinateMinpolyQuotientEquiv n f (Ideal.Quotient.mk _ p) =
      MvPolynomial.map (AdjoinRoot.mk f) (coordinateCoefficientSplit n p) := by
  change coefficientAdjoinRootQuotientEquiv n f
    (Ideal.Quotient.mk _ (coordinateCoefficientSplit n p)) = _
  exact coefficientAdjoinRootQuotientEquiv_mk n f (coordinateCoefficientSplit n p)

@[simp] theorem coordinateMinpolyQuotientEquiv_X_zero (n : ℕ) (f : K[X]) :
    coordinateMinpolyQuotientEquiv n f (Ideal.Quotient.mk _ (MvPolynomial.X 0)) =
      MvPolynomial.C (AdjoinRoot.root f) := by
  rw [coordinateMinpolyQuotientEquiv_mk, coordinateCoefficientSplit_X_zero]
  simp

@[simp] theorem coordinateMinpolyQuotientEquiv_X_succ (n : ℕ) (f : K[X]) (i : Fin n) :
    coordinateMinpolyQuotientEquiv n f (Ideal.Quotient.mk _ (MvPolynomial.X i.succ)) =
      MvPolynomial.X i := by
  rw [coordinateMinpolyQuotientEquiv_mk, coordinateCoefficientSplit_X_succ]
  simp

@[simp] theorem coordinateMinpolyQuotientEquiv_C (n : ℕ) (f : K[X]) (a : K) :
    coordinateMinpolyQuotientEquiv n f (Ideal.Quotient.mk _ (MvPolynomial.C a)) =
      MvPolynomial.C (algebraMap K (AdjoinRoot f) a) := by
  rw [coordinateMinpolyQuotientEquiv_mk, coordinateCoefficientSplit_C]
  simp

theorem coordinateMinpolyIdeal_le_of_mem_contraction (n : ℕ) (f : K[X])
    (m : Ideal (MvPolynomial (Fin (n+1)) K))
    (hf : f ∈ m.comap (Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1)))).toRingHom) :
    coordinateMinpolyIdeal n f ≤ m := by
  apply Ideal.span_le.mpr
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  exact hf

end PiExponentSiegel.W08

end OAI
