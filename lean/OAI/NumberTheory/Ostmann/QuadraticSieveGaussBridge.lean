import OAI.NumberTheory.Ostmann.QuadraticSieveGaussBridgeCRT

namespace OAI

namespace Ostmann.QuadraticSieve

theorem sum_addChar_sq_eq_jacobi_gauss (q : ℕ) [NeZero q]
    (hq : Odd q) (hsq : Squarefree q) (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) :
    (∑ a : ZMod q, ψ (a ^ 2)) = gaussSum (jacobiDirichletCharacter q) ψ := by
  revert hq hsq ψ hψ
  revert ‹NeZero q›
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero =>
    intro inst
    exact (NeZero.ne 0 rfl).elim
  | one =>
    intro inst hq hsq ψ hψ
    unfold gaussSum
    apply Finset.sum_congr rfl
    intro a ha
    have ha0 : a = 0 := Subsingleton.elim _ _
    have hχ0 : jacobiDirichletCharacter 1 (0 : ZMod 1) = 1 := by
      rw [Subsingleton.elim (0 : ZMod 1) (1 : ZMod 1), map_one]
    simp [hχ0, ha0]
  | prime_pow p k hp hk =>
    intro inst hq hsq
    have hk1 := ((Nat.squarefree_pow_iff hp.ne_one hk.ne').mp hsq).2
    subst k
    revert hq hsq
    revert inst
    rw [pow_one]
    intro inst hq hsq ψ hψ
    let : Fact p.Prime := ⟨hp⟩
    exact sum_addChar_sq_eq_jacobi_gauss_prime hq ψ hψ
  | coprime m n hm hn hmn ihm ihn =>
    intro inst hq hsq ψ hψ
    let : NeZero m := ⟨by omega⟩
    let : NeZero n := ⟨by omega⟩
    obtain ⟨hmo, hno⟩ := Nat.odd_mul.mp hq
    have hms := hsq.squarefree_of_dvd (dvd_mul_right m n)
    have hns := hsq.squarefree_of_dvd (dvd_mul_left n m)
    rw [quadratic_sum_crt hmn ψ, jacobi_gauss_crt hmn ψ,
      ihm hmo hms (crtLeftAddChar hmn ψ) (crtLeftAddChar_isPrimitive hmn ψ hψ),
      ihn hno hns (crtRightAddChar hmn ψ) (crtRightAddChar_isPrimitive hmn ψ hψ)]

theorem quadratic_sum_eq_jacobi_gauss {q : ℕ} [NeZero q]
    (hq : Odd q) (hsq : Squarefree q) :
    (∑ a : ZMod q, ZMod.stdAddChar (a ^ 2)) =
      gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar :=
  sum_addChar_sq_eq_jacobi_gauss q hq hsq ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar q)

end Ostmann.QuadraticSieve

end OAI
