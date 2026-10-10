import OAI.NumberTheory.JointDickman.Analysis.SquarefreeCharacterEuler

namespace OAI

/-! # Euler products of the character-twisted squarefree coefficients -/
namespace JointDickman
open Finset

noncomputable def squarefreeCharacterDirichletSummand {q : ℕ}
    (χ : DirichletCharacter ℂ q) (z : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  squarefreeDirichletSummand z s n * χ (n:ZMod q)

theorem squarefreeCharacterDirichletSummand_term {q : ℕ}
    (χ : DirichletCharacter ℂ q) (z : ℝ) (s : ℂ) (n : ℕ) :
    squarefreeCharacterDirichletSummand χ z s n =
      LSeries.term (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s n := by
  rw [LSeries.term_def₀ (f := fun n : ℕ => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) (by simp)]
  dsimp [squarefreeCharacterDirichletSummand, squarefreeDirichletSummand]
  ring

theorem squarefreeCharacterDirichletSummand_summable {q : ℕ}
    (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => ‖squarefreeCharacterDirichletSummand χ z s n‖) := by
  apply (squarefreeDirichletSummand_summable hz hz1 hs).of_nonneg_of_le
    (fun n => norm_nonneg _)
  intro n
  rw [squarefreeCharacterDirichletSummand, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)

theorem squarefreeCharacterDirichletSeries_eulerProduct {q : ℕ}
    (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1+(z:ℂ)*characterPrimePower χ s p)
      (LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s) := by
  have hmul {m n : ℕ} (hmn : m.Coprime n) :
      squarefreeCharacterDirichletSummand χ z s (m*n) =
        squarefreeCharacterDirichletSummand χ z s m *
        squarefreeCharacterDirichletSummand χ z s n := by
    rw [squarefreeCharacterDirichletSummand, squarefreeDirichletSummand_mul z s hmn]
    simp only [Nat.cast_mul, map_mul, squarefreeCharacterDirichletSummand]
    ring
  have hone : squarefreeCharacterDirichletSummand χ z s 1 = 1 := by
    simp [squarefreeCharacterDirichletSummand, squarefreeDirichletSummand_one]
  have hzero : squarefreeCharacterDirichletSummand χ z s 0 = 0 := by
    simp [squarefreeCharacterDirichletSummand, squarefreeDirichletSummand_zero]
  have h := EulerProduct.eulerProduct_hasProd hone (fun {m n} hmn => hmul hmn)
    (squarefreeCharacterDirichletSummand_summable χ hz hz1 hs) hzero
  have he (p : Nat.Primes) :
      (∑' e : ℕ, squarefreeCharacterDirichletSummand χ z s (p.val^e)) =
        1+(z:ℂ)*characterPrimePower χ s p := by
    have hpw : squarefreeWeight z p.val = z := by
      simpa only [pow_one, ite_true] using
        squarefreeWeight_prime_pow z p.property (by omega : (1:ℕ) ≠ 0)
    rw [tsum_eq_sum (s := {0,1})]
    · simp [squarefreeCharacterDirichletSummand, squarefreeDirichletSummand,
        hpw, characterPrimePower]
      ring
    · intro e he
      have he0 : e ≠ 0 := by intro h; apply he; simp [h]
      have he1 : e ≠ 1 := by intro h; apply he; simp [h]
      simp [squarefreeCharacterDirichletSummand, squarefreeDirichletSummand,
        squarefreeWeight_prime_pow z p.property he0, he1]
  rw [show (fun p : Nat.Primes => ∑' e : ℕ,
    squarefreeCharacterDirichletSummand χ z s (p.val^e)) =
      (fun p => 1+(z:ℂ)*characterPrimePower χ s p) from funext he] at h
  simpa only [squarefreeCharacterDirichletSummand_term, LSeries] using h

end JointDickman

end OAI
