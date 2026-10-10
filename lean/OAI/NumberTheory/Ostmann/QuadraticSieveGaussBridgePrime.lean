import OAI.NumberTheory.Ostmann.QuadraticSieveGauss

namespace OAI

namespace Ostmann.QuadraticSieve

theorem sum_addChar_sq_eq_quadratic_gauss {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    (∑ x : F, ψ (x ^ 2)) = ∑ a : F, (quadraticChar F a : ℂ) * ψ a := by
  classical
  calc
    _ = ∑ a : F, ∑ x ∈ Finset.univ.filter (fun x : F => x ^ 2 = a), ψ a :=
      (Finset.sum_fiberwise' Finset.univ (fun x : F => x ^ 2) ψ).symm
    _ = ∑ a : F, ((quadraticChar F a : ℂ) + 1) * ψ a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      have hc := quadraticChar_card_sqrts hF a
      have hf : Finset.univ.filter (fun x : F => x ^ 2 = a) = {x : F | x ^ 2 = a}.toFinset := by
        ext x
        simp
      rw [hf]
      exact_mod_cast hc
    _ = (∑ a : F, (quadraticChar F a : ℂ) * ψ a) + ∑ a : F, ψ a := by
      simp only [add_mul, one_mul, Finset.sum_add_distrib]
    _ = _ := by rw [AddChar.sum_eq_zero_of_ne_one hψ, add_zero]

theorem jacobiDirichletCharacter_prime {p : ℕ} [Fact p.Prime] (a : ZMod p) :
    jacobiDirichletCharacter p a = (quadraticChar (ZMod p) a : ℂ) := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
  rw [jacobiDirichletCharacter_intCast, ← jacobiSym.legendreSym.to_jacobiSym]
  rfl

theorem sum_addChar_sq_eq_jacobi_gauss_prime {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive) :
    (∑ x : ZMod p, ψ (x ^ 2)) = gaussSum (jacobiDirichletCharacter p) ψ := by
  have hψne : ψ ≠ 1 := by
    simpa only [AddChar.mulShift_one] using hψ (a := (1 : ZMod p)) one_ne_zero
  rw [sum_addChar_sq_eq_quadratic_gauss (by simpa only [ZMod.ringChar_zmod_n] using hodd.ne_two_of_dvd_nat (dvd_refl p)) ψ hψne]
  unfold gaussSum
  apply Finset.sum_congr rfl
  intro a ha
  rw [jacobiDirichletCharacter_prime]

end Ostmann.QuadraticSieve

end OAI
