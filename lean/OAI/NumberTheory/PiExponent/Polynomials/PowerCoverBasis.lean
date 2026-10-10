import OAI.NumberTheory.PiExponent.Polynomials.PowerCoverSubstitution

namespace OAI

namespace PiExponent.PowerCover
noncomputable section

variable {σ : Type*} [Fintype σ] {k : Type*} [CommSemiring k]

def decompositionAddEquiv (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    MvPolynomial σ k ≃+ ((∀ i, Fin (w i)) →₀ MvPolynomial σ k) :=
  (AddMonoidAlgebra.coeffAddEquiv : MvPolynomial σ k ≃+ ((σ →₀ ℕ) →₀ k)).trans <|
    (Finsupp.domCongr ((exponentEquiv w hw).trans (Equiv.prodComm _ _))).trans <|
      Finsupp.curryAddEquiv.trans <|
        Finsupp.mapRange.addEquiv AddMonoidAlgebra.coeffAddEquiv.symm

@[simp] theorem decompositionAddEquiv_monomial (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a : σ →₀ ℕ) (c : k) :
    decompositionAddEquiv w hw (MvPolynomial.monomial a c) =
      Finsupp.single (residue w hw a) (MvPolynomial.monomial (quotient w a) c) := by
  classical
  simp [decompositionAddEquiv, MvPolynomial.monomial, Finsupp.curry_single]

theorem decompositionAddEquiv_power_mul (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p q : MvPolynomial σ k) :
    decompositionAddEquiv w hw (powerSubstitution w p * q) =
      p • decompositionAddEquiv w hw q := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    induction q using MvPolynomial.induction_on' with
    | monomial b d =>
      simp only [powerSubstitution_monomial, MvPolynomial.monomial_mul_monomial,
        decompositionAddEquiv_monomial]
      rw [add_comm (scale w a) b, quotient_add_scale w hw, residue_add_scale]
      simp [Finsupp.smul_single, smul_eq_mul, MvPolynomial.monomial_mul_monomial, add_comm]
    | add q r hq hr =>
      simp only [mul_add, map_add, smul_add, hq, hr]
  | add p r hp hr =>
    simp only [map_add, add_mul, add_smul, hp, hr]

def PowerModule (_weights : σ → ℕ) (k : Type*) [CommSemiring k] := MvPolynomial σ k

instance (w : σ → ℕ) : CommSemiring (PowerModule w k) :=
  inferInstanceAs (CommSemiring (MvPolynomial σ k))

def toPolynomial (w : σ → ℕ) : PowerModule w k ≃+* MvPolynomial σ k :=
  RingEquiv.refl _

instance powerAlgebra (w : σ → ℕ) : Algebra (MvPolynomial σ k) (PowerModule w k) :=
  ((toPolynomial w).symm.toRingHom.comp
    (powerSubstitution w).toRingHom).toAlgebra

omit [Fintype σ] in
@[simp] theorem toPolynomial_smul (w : σ → ℕ) (p : MvPolynomial σ k)
    (q : PowerModule w k) :
    toPolynomial w (p • q) =
      powerSubstitution w p * toPolynomial w q := rfl

def decomposition (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    PowerModule w k ≃ₗ[MvPolynomial σ k] ((∀ i, Fin (w i)) →₀ MvPolynomial σ k) :=
  ((toPolynomial w).toAddEquiv.trans (decompositionAddEquiv w hw)).toLinearEquiv <| by
    intro p q
    exact decompositionAddEquiv_power_mul w hw p (toPolynomial w q)

def basis (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    Module.Basis (∀ i, Fin (w i)) (MvPolynomial σ k) (PowerModule w k) where
  repr := decomposition w hw

theorem basis_toPolynomial (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (r : ∀ i, Fin (w i)) :
    toPolynomial w (basis (k := k) w hw r) = MvPolynomial.monomial (combine w (0, r)) 1 := by
  apply (decompositionAddEquiv w hw).injective
  rw [decompositionAddEquiv_monomial, quotient_combine w hw, residue_combine]
  change (basis (k := k) w hw).repr (basis w hw r) = _
  simp

theorem module_free (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    Module.Free (MvPolynomial σ k) (PowerModule w k) :=
  Module.Free.of_basis (basis w hw)

theorem module_finite (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    Module.Finite (MvPolynomial σ k) (PowerModule w k) := by
  classical
  exact Module.Finite.of_basis (basis w hw)

theorem finrank (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    [StrongRankCondition (MvPolynomial σ k)] :
    Module.finrank (MvPolynomial σ k) (PowerModule w k) = ∏ i, w i := by
  classical
  rw [Module.finrank_eq_card_basis (basis w hw)]
  simp [Fintype.card_pi]

end

noncomputable instance {σ k : Type*} [CommRing k] (w : σ → ℕ) :
    CommRing (PowerModule w k) :=
  inferInstanceAs (CommRing (MvPolynomial σ k))

end PiExponent.PowerCover

end OAI
