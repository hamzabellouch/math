import OAI.NumberTheory.Ostmann.Arithmetic.CompensatedPivotPrecision

namespace OAI

/-! # Prefix precision after retaining only the frequency congruences

The frequency model in the arithmetic replacement divides by compensation
factors modulo the remaining power. Its equations are congruences, with one
power lost at each branch level.
-/

namespace Ostmann
open scoped BigOperators

/-- The equation of the moving construction, keeping its compensation
product instead of replacing the new giant by a composite pivot. -/
def PivotDependencyScheme.modularCompensatedEquations {N : ℕ} (D : PivotDependencyScheme N)
    (M : ℤ) (k : ℕ) (U L R p : Fin N → ℤ) : Prop :=
  ∀ j, (D.frequencies j).left * D.leftCoefficient p j * R j -
    (D.frequencies j).right * D.rightCoefficient p j * L j ≡
      (D.frequencies j).root * U j * p j [ZMOD M ^ (k + 1 - D.depth j)]

theorem PivotDependencyScheme.modular_compensated_pivot_prefix_precision {N : ℕ} (D : PivotDependencyScheme N)
    (R k J : ℕ) (U : Fin N → ℤ) (hU : ∀ j, IsCoprime (U j) (R : ℤ)) (hdepth : ∀ j, D.depth j ≤ k)
    (hs : ∀ j, (D.frequencies j).root ≠ 0)
    (hsR : ∀ j, (D.frequencies j).root.natAbs ∣ R)
    (L₁ R₁ p₁ L₂ R₂ p₂ : Fin N → ℤ)
    (heq₁ : D.modularCompensatedEquations R k U L₁ R₁ p₁) (heq₂ : D.modularCompensatedEquations R k U L₂ R₂ p₂)
    (hL : ∀ j, j.val < J → L₁ j ≡ L₂ j [ZMOD (R : ℤ) ^ (k + 2)])
    (hR : ∀ j, j.val < J → R₁ j ≡ R₂ j [ZMOD (R : ℤ) ^ (k + 2)]) :
    ∀ j, j.val < J → p₁ j ≡ p₂ j [ZMOD (R : ℤ) ^ (k - D.depth j)] := by
  intro j hj
  have hall : ∀ a : ℕ, ∀ j : Fin N, j.val = a → j.val < J →
      p₁ j ≡ p₂ j [ZMOD (R : ℤ) ^ (k - D.depth j)] := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hja hj
      have hcoeff (C : ℤ) (A : Finset (Fin N))
          (hA : ∀ i ∈ A, i.val < j.val ∧ D.depth i < D.depth j) :
          ancestorCoefficient C A p₁ ≡ ancestorCoefficient C A p₂
            [ZMOD (R : ℤ) ^ (k + 1 - D.depth j)] := by
        apply ancestorCoefficient_modEq
        intro i hi
        obtain ⟨hij, hdij⟩ := hA i hi
        have hp := ih i.val (by omega) i rfl (by omega)
        exact hp.of_dvd (pow_dvd_pow (R : ℤ) (by have := hdepth i; have := hdepth j; omega))
      have hcL := hcoeff (D.fixedLeft j) (D.ancestorsLeft j) (D.earlierLeft j)
      have hcR := hcoeff (D.fixedRight j) (D.ancestorsRight j) (D.earlierRight j)
      have hlj := (hL j hj).of_dvd (pow_dvd_pow (R : ℤ) (by omega : k + 1 - D.depth j ≤ k + 2))
      have hrj := (hR j hj).of_dvd (pow_dvd_pow (R : ℤ) (by omega : k + 1 - D.depth j ≤ k + 2))
      have hnum := ((hcL.mul_left (D.frequencies j).left).mul hrj).sub
        ((hcR.mul_left (D.frequencies j).right).mul hlj)
      have hroot : (D.frequencies j).root ∣ (R : ℤ) :=
        Int.natAbs_dvd.mp (Int.natCast_dvd_natCast.mpr (hsR j))
      have hproducts := (heq₁ j).symm.trans (hnum.trans (heq₂ j))
      have hx := reversal_residue_precision (R : ℤ) (D.frequencies j).root (U j) (U j)
        ((D.frequencies j).root * U j * p₁ j)
        ((D.frequencies j).root * U j * p₂ j)
        (p₁ j) (p₂ j) (k - D.depth j) (hs j) hroot (hU j) rfl rfl
        (by
          have he : k - D.depth j + 1 = k + 1 - D.depth j := by
            have := hdepth j
            omega
          rw [he]
          exact hproducts) (.refl (U j))
      exact hx
  exact hall j.val j rfl hj

/-- Before the current split is exposed, both coefficients are already
known modulo its root frequency. This is the measurability step needed by
the sequential uniform-root count. -/
theorem PivotDependencyScheme.modular_compensated_coefficients_prefix_precision {N : ℕ}
    (D : PivotDependencyScheme N) (R k : ℕ) (U : Fin N → ℤ)
    (hU : ∀ i, IsCoprime (U i) (R : ℤ)) (j : Fin N)
    (hdepth : ∀ i, D.depth i ≤ k) (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (L₁ R₁ p₁ L₂ R₂ p₂ : Fin N → ℤ)
    (heq₁ : D.modularCompensatedEquations R k U L₁ R₁ p₁) (heq₂ : D.modularCompensatedEquations R k U L₂ R₂ p₂)
    (hL : ∀ i, i.val < j.val → L₁ i ≡ L₂ i [ZMOD (R : ℤ) ^ (k + 2)])
    (hR : ∀ i, i.val < j.val → R₁ i ≡ R₂ i [ZMOD (R : ℤ) ^ (k + 2)]) :
    D.leftCoefficient p₁ j ≡ D.leftCoefficient p₂ j [ZMOD (D.frequencies j).root.natAbs] ∧
      D.rightCoefficient p₁ j ≡ D.rightCoefficient p₂ j [ZMOD (D.frequencies j).root.natAbs] := by
  have hp := D.modular_compensated_pivot_prefix_precision R k j.val U hU hdepth hs hsR L₁ R₁ p₁ L₂ R₂ p₂ heq₁ heq₂ hL hR
  have hcoeff (C : ℤ) (A : Finset (Fin N))
      (hA : ∀ i ∈ A, i.val < j.val ∧ D.depth i < D.depth j) :
      ancestorCoefficient C A p₁ ≡ ancestorCoefficient C A p₂
        [ZMOD (D.frequencies j).root.natAbs] := by
    apply ancestorCoefficient_modEq
    intro i hi
    obtain ⟨hij, hdij⟩ := hA i hi
    apply (hp i hij).of_dvd
    exact (Int.natCast_dvd_natCast.mpr (hsR j)).trans
      (dvd_pow_self (R : ℤ) (by have := hdepth j; omega))
  exact ⟨hcoeff _ _ (D.earlierLeft j), hcoeff _ _ (D.earlierRight j)⟩

end Ostmann

end OAI
