import Mathlib

namespace OAI

noncomputable section

namespace PiExponent.FormalMatrixBridge

def nestedPolynomialSwap (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin m) (Polynomial R) ≃ₐ[R] Polynomial (MvPolynomial (Fin m) R) :=
  (MvPolynomial.mapAlgEquiv (Fin m) (MvPolynomial.uniqueAlgEquiv R Unit).symm).trans
    ((MvPolynomial.commAlgEquiv R (Fin m) Unit).trans
      ((MvPolynomial.uniqueAlgEquiv (MvPolynomial (Fin m) R) Unit).restrictScalars R))

theorem coeff_commAlgEquiv {R σ τ : Type*} [CommRing R]
    (p : MvPolynomial σ (MvPolynomial τ R)) (b : σ →₀ ℕ) (c : τ →₀ ℕ) :
    ((MvPolynomial.commAlgEquiv R σ τ p).coeff c).coeff b = (p.coeff b).coeff c := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
  | monomial d a =>
    induction a using MvPolynomial.induction_on' with
    | add a e ha he =>
      simpa only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
        using congrArg₂ (· + ·) ha he
    | monomial e r =>
      have hs : MvPolynomial.commAlgEquiv R σ τ
          (MvPolynomial.monomial d (MvPolynomial.monomial e r)) =
          MvPolynomial.monomial e (MvPolynomial.monomial d r) :=
        AddMonoidAlgebra.commAlgEquiv_single_single (R := R) d e r
      rw [hs]
      simp only [MvPolynomial.coeff_monomial]
      split_ifs <;> simp_all

theorem coeff_nestedPolynomialSwap {R : Type*} [CommRing R] {m : ℕ}
    (p : MvPolynomial (Fin m) (Polynomial R)) (s : ℕ) (b : Fin m →₀ ℕ) :
    ((nestedPolynomialSwap R m p).coeff s).coeff b = (p.coeff b).coeff s := by
  change ((MvPolynomial.uniqueAlgEquiv (MvPolynomial (Fin m) R) Unit
    (MvPolynomial.commAlgEquiv R (Fin m) Unit
      (MvPolynomial.mapAlgEquiv (Fin m) (MvPolynomial.uniqueAlgEquiv R Unit).symm p))).coeff s).coeff b = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv, coeff_commAlgEquiv]
  rw [MvPolynomial.mapAlgEquiv_apply, MvPolynomial.coeff_map]
  change (((MvPolynomial.uniqueAlgEquiv R Unit).symm (p.coeff b)).coeff
    (Finsupp.single () s)) = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv_symm]
  simp

end PiExponent.FormalMatrixBridge

end

end OAI
