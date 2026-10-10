import OAI.NumberTheory.Ostmann.Characters.CharacterUnitParseval

namespace OAI

/-! # Simultaneous primitive-character energy at a fixed modulus -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

 theorem primitive_inverse_energy {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]
    (S : Finset (DirichletCharacter ℂ q)) (hS : ∀ χ ∈ S, χ.IsPrimitive)
    (c : ι → ℂ) (a : ι → ZMod q) :
    (q : ℝ) * ∑ χ ∈ S, ‖∑ j, c j * χ⁻¹ (a j)‖ ^ 2 ≤
      (q.totient : ℝ) * ∑ u : (ZMod q)ˣ,
        ‖∑ j, c j * ZMod.stdAddChar ((u : ZMod q) * a j)‖ ^ 2 := by
  let f : (ZMod q)ˣ → ℂ := fun u => ∑ j, c j * ZMod.stdAddChar ((u : ZMod q) * a j)
  have hid (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
      (q : ℝ) * ‖∑ j, c j * χ⁻¹ (a j)‖ ^ 2 = ‖∑ u : (ZMod q)ˣ, χ u * f u‖ ^ 2 := by
    have hg : (∑ u : (ZMod q)ˣ, χ u * f u) =
        (∑ j, c j * χ⁻¹ (a j)) * gaussSum χ ZMod.stdAddChar := by
      simp only [f, Finset.mul_sum]
      rw [Finset.sum_comm]
      calc
        _ = ∑ j, c j * ∑ u : (ZMod q)ˣ,
            χ u * ZMod.stdAddChar ((u : ZMod q) * a j) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro u _
          ring
        _ = _ := by
          simp_rw [primitive_unit_gauss χ hχ]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
    rw [hg, norm_mul, mul_pow, primitive_gauss_norm_sq χ hχ, mul_comm]
  calc
    _ = ∑ χ ∈ S, ‖∑ u : (ZMod q)ˣ, χ u * f u‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun χ hχ => hid χ (hS χ hχ))
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, χ u * f u‖ ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
    _ = _ := character_unit_parseval f

 theorem primitive_inverse_energy_le {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]
    (S : Finset (DirichletCharacter ℂ q)) (hS : ∀ χ ∈ S, χ.IsPrimitive)
    (c : ι → ℂ) (a : ι → ZMod q) :
    (∑ χ ∈ S, ‖∑ j, c j * χ⁻¹ (a j)‖ ^ 2) ≤
      ∑ u : (ZMod q)ˣ, ‖∑ j, c j * ZMod.stdAddChar ((u : ZMod q) * a j)‖ ^ 2 := by
  have ht : q.totient ≤ q := Nat.totient_le q
  have h := primitive_inverse_energy S hS c a
  have he : 0 ≤ ∑ u : (ZMod q)ˣ,
      ‖∑ j, c j * ZMod.stdAddChar ((u : ZMod q) * a j)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  exact (mul_le_mul_iff_right₀ hq).mp
    (h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast ht) he))

 theorem primitive_character_energy_le {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]
    (S : Finset (DirichletCharacter ℂ q)) (hS : ∀ χ ∈ S, χ.IsPrimitive)
    (c : ι → ℂ) (a : ι → ZMod q) :
    (∑ χ ∈ S, ‖∑ j, c j * χ (a j)‖ ^ 2) ≤
      ∑ u : (ZMod q)ˣ, ‖∑ j, star (c j) *
        ZMod.stdAddChar ((u : ZMod q) * a j)‖ ^ 2 := by
  have h := primitive_inverse_energy_le S hS (fun j => star (c j)) a
  have hn (χ : DirichletCharacter ℂ q) :
      ‖∑ j, star (c j) * χ⁻¹ (a j)‖ = ‖∑ j, c j * χ (a j)‖ := by
    calc
      _ = ‖star (∑ j, c j * χ (a j))‖ := by
        congr 1
        simp only [star_sum, star_mul, MulChar.star_apply', mul_comm]
      _ = _ := norm_star _
  simpa only [hn] using h

end Ostmann

end OAI
