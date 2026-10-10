import OAI.NumberTheory.Ostmann.QuadraticSieve
import OAI.NumberTheory.Ostmann.QuadraticSieveGaussEvaluation

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def gaussPhaseA : ℂ := (1 + Complex.I) / 2
noncomputable def gaussPhaseB : ℂ := (1 - Complex.I) / 2

theorem gauss_phase_eq_two_characters {q : ℕ} (hq : Odd q) :
    (if q % 4 = 1 then (1 : ℂ) else Complex.I) =
      gaussPhaseA + gaussPhaseB * (jacobiSym (-1) q : ℂ) := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hq) with hm | hm
  · rw [ite_eq_left hm, jacobiSym.at_neg_one hq, ZMod.χ₄_nat_one_mod_four hm]
    norm_num [gaussPhaseA, gaussPhaseB]
    ring
  · rw [ite_eq_right (by omega), jacobiSym.at_neg_one hq, ZMod.χ₄_nat_three_mod_four hm]
    norm_num [gaussPhaseA, gaussPhaseB]
    ring

noncomputable def jacobiGaussRatio (q : ℕ) : ℂ :=
  if hq : q = 0 then 0 else by
    let : NeZero q := ⟨hq⟩
    exact gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar / (q : ℂ)

@[simp] theorem jacobiGaussRatio_eq (q : ℕ) [NeZero q] :
    jacobiGaussRatio q = gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar / (q : ℂ) := by
  simp only [jacobiGaussRatio, dite_eq_right (NeZero.ne q)]

theorem jacobiGaussRatio_eq_two_characters {q : ℕ} [NeZero q]
    (hq : Odd q) (hsq : Squarefree q) :
    jacobiGaussRatio q =
      (gaussPhaseA + gaussPhaseB * (jacobiSym (-1) q : ℂ)) / (Real.sqrt (q : ℝ) : ℂ) := by
  rw [jacobiGaussRatio_eq, jacobi_gauss_evaluation hq hsq, gauss_phase_eq_two_characters hq]
  have hqr : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hs0 : (Real.sqrt (q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hqr).ne'
  have hs2 : (Real.sqrt (q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  rw [← hs2]
  field_simp

noncomputable def gaussRowFactor (c : ℤ) (n : ℕ) : ℂ :=
  (jacobiSym c n : ℂ) / (Real.sqrt (n : ℝ) : ℂ)

theorem gaussRowFactor_mul (c : ℤ) {n t : ℕ} (hn : 0 < n) (ht : 0 < t) :
    gaussRowFactor c (n * t) = gaussRowFactor c n * gaussRowFactor c t := by
  unfold gaussRowFactor
  rw [jacobiSym.mul_right' c hn.ne' ht.ne', Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg n)]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem jacobiGaussRatio_mul_jacobi {q : ℕ} [NeZero q]
    (hq : Odd q) (hsq : Squarefree q) (c v : ℤ) :
    jacobiGaussRatio q * (jacobiSym (c * v) q : ℂ) =
      gaussPhaseA * gaussRowFactor c q * (jacobiSym v q : ℂ) +
      gaussPhaseB * gaussRowFactor (-c) q * (jacobiSym v q : ℂ) := by
  have hneg : jacobiSym (-c) q = jacobiSym (-1) q * jacobiSym c q := by
    rw [← jacobiSym.mul_left, neg_one_mul]
  rw [jacobiGaussRatio_eq_two_characters hq hsq, jacobiSym.mul_left]
  unfold gaussRowFactor
  rw [hneg]
  push_cast
  ring

theorem norm_gaussPhaseA_le_one : ‖gaussPhaseA‖ ≤ 1 := by
  have h := norm_add_le (1 : ℂ) Complex.I
  norm_num at h
  rw [gaussPhaseA, norm_div]
  norm_num
  linarith

theorem norm_gaussPhaseB_le_one : ‖gaussPhaseB‖ ≤ 1 := by
  have h := norm_sub_le (1 : ℂ) Complex.I
  norm_num at h
  rw [gaussPhaseB, norm_div]
  norm_num
  linarith

end Ostmann.QuadraticSieve

end OAI
