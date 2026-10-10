import OAI.NumberTheory.PiExponent.Polynomials.PowerCoverExponents

namespace OAI

namespace PiExponent.PowerCover

noncomputable section

variable {σ k : Type*} [Fintype σ] [CommSemiring k]

def scaleHom (w : σ → ℕ) : (σ →₀ ℕ) →+ (σ →₀ ℕ) where
  toFun := scale w
  map_zero' := scale_zero w
  map_add' := scale_add w

@[simp] theorem scaleHom_apply (w : σ → ℕ) (a : σ →₀ ℕ) :
    scaleHom w a = scale w a := rfl

@[simp] theorem scale_single (w : σ → ℕ) (i : σ) (n : ℕ) :
    scale w (Finsupp.single i n) = Finsupp.single i (w i * n) := by
  classical
  ext j
  by_cases h : i = j
  · subst j; simp
  · simp [h]

theorem scale_injective (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    Function.Injective (scale w) := by
  intro a b hab
  ext i
  have h := congrArg (fun c : σ →₀ ℕ => c i) hab
  simp only [scale_apply] at h
  exact Nat.eq_of_mul_eq_mul_left (hw i) h

def powerSubstitution (w : σ → ℕ) :
    MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun i => MvPolynomial.X i ^ w i)

omit [Fintype σ] in
@[simp] theorem powerSubstitution_X (w : σ → ℕ) (i : σ) :
    powerSubstitution (k := k) w (MvPolynomial.X i) = MvPolynomial.X i ^ w i := by
  simp [powerSubstitution]

theorem powerSubstitution_eq_mapDomainAlgHom (w : σ → ℕ) :
    powerSubstitution (k := k) w = AddMonoidAlgebra.mapDomainAlgHom k k (scaleHom w) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [powerSubstitution_X, MvPolynomial.X_pow_eq_monomial]
  change MvPolynomial.monomial (Finsupp.single i (w i)) (1 : k) =
    AddMonoidAlgebra.mapDomain (scaleHom w) (AddMonoidAlgebra.single (Finsupp.single i 1) 1)
  rw [AddMonoidAlgebra.mapDomain_single]
  simp [MvPolynomial.single_eq_monomial]

@[simp] theorem powerSubstitution_monomial (w : σ → ℕ) (a : σ →₀ ℕ) (c : k) :
    powerSubstitution w (MvPolynomial.monomial a c) =
      MvPolynomial.monomial (scale w a) c := by
  rw [powerSubstitution_eq_mapDomainAlgHom]
  change AddMonoidAlgebra.mapDomain (scaleHom w) (AddMonoidAlgebra.single a c) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

theorem powerSubstitution_injective (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    Function.Injective (powerSubstitution (k := k) w) := by
  rw [powerSubstitution_eq_mapDomainAlgHom]
  exact AddMonoidAlgebra.mapDomain_injective (scale_injective w hw)

end
end PiExponent.PowerCover

end OAI
