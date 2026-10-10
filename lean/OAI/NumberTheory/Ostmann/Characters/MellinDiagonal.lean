import OAI.NumberTheory.Ostmann.Characters.MellinParseval

namespace OAI

/-!
# Mellin Parseval on a multiplicative diagonal

This is the finite interchange of Mellin expansion and a weighted sum
used at the beginning of the proof of the uniform estimate `src42`.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem mellinCoefficient_of_expansion {p : ℕ} [Fact p.Prime]
    (c : MulChar (ZMod p) ℂ → ℂ) (f : (ZMod p)ˣ → ℂ)
    (hf : ∀ z, f z = ∑ χ : MulChar (ZMod p) ℂ, c χ * χ z)
    (ρ : MulChar (ZMod p) ℂ) : mellinCoefficient f ρ = c ρ := by
  classical
  have hcard : (Fintype.card (ZMod p)ˣ : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold mellinCoefficient
  simp_rw [hf, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  calc
    _ = ∑ χ : MulChar (ZMod p) ℂ, (Fintype.card (ZMod p)ˣ : ℂ)⁻¹ *
        (c χ * ∑ z : (ZMod p)ˣ, χ z * conj (ρ z)) := by
      apply Finset.sum_congr rfl
      intro χ _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = c ρ := by
      simp_rw [mellin_orthogonality]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      field_simp

noncomputable def mellinDiagonal {p : ℕ} [Fact p.Prime]
    (H : (ZMod p)ˣ → (ZMod p)ˣ → ℂ) (v : (ZMod p)ˣ → ℂ)
    (lam : (ZMod p)ˣ) : ℂ :=
  (p : ℂ)⁻¹ * ∑ d : (ZMod p)ˣ, H d (lam * d) * v d

noncomputable def mellinDiagonalCoefficient {p : ℕ} [Fact p.Prime]
    (H : (ZMod p)ˣ → (ZMod p)ˣ → ℂ) (v : (ZMod p)ˣ → ℂ)
    (χ : MulChar (ZMod p) ℂ) : ℂ :=
  (p : ℂ)⁻¹ * ∑ d : (ZMod p)ˣ, mellinCoefficient (H d) χ * χ d * v d

theorem mellinDiagonal_expansion {p : ℕ} [Fact p.Prime]
    (H : (ZMod p)ˣ → (ZMod p)ˣ → ℂ) (v : (ZMod p)ˣ → ℂ) (lam : (ZMod p)ˣ) :
    mellinDiagonal H v lam = ∑ χ : MulChar (ZMod p) ℂ,
      mellinDiagonalCoefficient H v χ * χ lam := by
  have hH (d t : (ZMod p)ˣ) : H d t =
      ∑ χ : MulChar (ZMod p) ℂ, mellinCoefficient (H d) χ * χ t :=
    (mellin_inversion (H d) t).symm
  unfold mellinDiagonal mellinDiagonalCoefficient
  simp_rw [hH, Units.val_mul, map_mul, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem mellinDiagonal_coefficient {p : ℕ} [Fact p.Prime]
    (H : (ZMod p)ˣ → (ZMod p)ˣ → ℂ) (v : (ZMod p)ˣ → ℂ)
    (χ : MulChar (ZMod p) ℂ) :
    mellinCoefficient (mellinDiagonal H v) χ = mellinDiagonalCoefficient H v χ :=
  mellinCoefficient_of_expansion _ _ (mellinDiagonal_expansion H v) χ

theorem mellinDiagonal_parseval {p : ℕ} [Fact p.Prime]
    (H : (ZMod p)ˣ → (ZMod p)ˣ → ℂ) (v : (ZMod p)ˣ → ℂ) :
    (∑ χ : MulChar (ZMod p) ℂ, ‖mellinDiagonalCoefficient H v χ‖ ^ 2) =
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
        ∑ lam : (ZMod p)ˣ, ‖mellinDiagonal H v lam‖ ^ 2 := by
  simpa only [mellinDiagonal_coefficient] using mellin_parseval (mellinDiagonal H v)

end Ostmann

end OAI
