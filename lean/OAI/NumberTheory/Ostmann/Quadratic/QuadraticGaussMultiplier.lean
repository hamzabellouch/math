import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGaussCRT

namespace OAI

/-! # Total quadratic Gauss multipliers and their elementary reciprocity sign -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticGaussMultiplier (n : ℕ) : ℂ :=
  if h : n = 0 then 0 else @jacobiGaussPhase n ⟨h⟩

 theorem quadraticGaussMultiplier_norm {n : ℕ} (hn : Squarefree n) (ho : Odd n) :
    ‖quadraticGaussMultiplier n‖ = 1 := by
  rw [quadraticGaussMultiplier, dite_eq_right hn.ne_zero]
  exact @jacobiGaussPhase_norm n ⟨hn.ne_zero⟩ hn ho

 theorem quadratic_jacobi_reciprocity_sign {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (hm : Odd m) (hn : Odd n) :
    jacobiComplex m (n : ZMod m) * jacobiComplex n (m : ZMod n) =
      if m % 4 = 3 ∧ n % 4 = 3 then (-1 : ℂ) else 1 := by
  have hc₁ : jacobiComplex m (n : ZMod m) = (jacobiSym (n : ℤ) m : ℂ) := by
    simpa only [Int.cast_natCast] using jacobiComplex_intCast m (n : ℤ)
  have hc₂ : jacobiComplex n (m : ZMod n) = (jacobiSym (m : ℤ) n : ℂ) := by
    simpa only [Int.cast_natCast] using jacobiComplex_intCast n (m : ℤ)
  rw [hc₁, hc₂, ← Int.cast_mul]
  have hs : jacobiSym (n : ℤ) m ^ 2 = 1 := jacobiSym.sq_one (by exact h.symm)
  by_cases hm3 : m % 4 = 3
  · by_cases hn3 : n % 4 = 3
    · rw [ite_eq_left ⟨hm3, hn3⟩,
        jacobiSym.quadratic_reciprocity_three_mod_four hm3 hn3]
      have hh : jacobiSym (n : ℤ) m * -jacobiSym (n : ℤ) m = -1 := by nlinarith
      rw [hh, Int.cast_neg, Int.cast_one]
    · have hn1 : n % 4 = 1 := by
        obtain hn1 | hn3' := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn)
        · exact hn1
        · exact (hn3 hn3').elim
      rw [ite_eq_right (fun hh => hn3 hh.2),
        jacobiSym.quadratic_reciprocity_one_mod_four' hm hn1, ← pow_two, hs, Int.cast_one]
  · have hm1 : m % 4 = 1 := by
      obtain hm1 | hm3' := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hm)
      · exact hm1
      · exact (hm3 hm3').elim
    rw [ite_eq_right (fun hh => hm3 hh.1),
      jacobiSym.quadratic_reciprocity_one_mod_four hm1 hn, ← pow_two, hs, Int.cast_one]

 theorem quadraticGaussMultiplier_mul {m n : ℕ} (h : m.Coprime n)
    (hm : Squarefree m) (hn : Squarefree n) (hom : Odd m) (hon : Odd n) :
    quadraticGaussMultiplier (m * n) =
      (if m % 4 = 3 ∧ n % 4 = 3 then (-1 : ℂ) else 1) *
        quadraticGaussMultiplier m * quadraticGaussMultiplier n := by
  let : NeZero m := ⟨hm.ne_zero⟩
  let : NeZero n := ⟨hn.ne_zero⟩
  rw [quadraticGaussMultiplier, dite_eq_right (mul_ne_zero hm.ne_zero hn.ne_zero),
    quadraticGaussMultiplier, dite_eq_right hm.ne_zero,
    quadraticGaussMultiplier, dite_eq_right hn.ne_zero,
    quadratic_gauss_phase_crt h hm hn hom hon, quadratic_jacobi_reciprocity_sign h hom hon]

end Ostmann

end OAI
