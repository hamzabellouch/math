import Mathlib.Algebra.BigOperators.Ring.Finset
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticPrecision
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticSplitTreeSupport

namespace OAI

/-! # Exposed products determine all earlier ancestor pivots

A nonbulk coefficient is its fixed label product times a specified set of
inserted ancestor pivots. A division loses one power of the frequency product
along its branch, rather than one power for every node already visited.
-/

namespace Ostmann

open scoped BigOperators

def ancestorCoefficient {N : ℕ} (C : ℤ) (A : Finset (Fin N)) (p : Fin N → ℤ) : ℤ :=
  C * ∏ i ∈ A, p i

theorem ancestorCoefficient_modEq {N : ℕ} (m C : ℤ) (A : Finset (Fin N))
    (p q : Fin N → ℤ) (h : ∀ i ∈ A, p i ≡ q i [ZMOD m]) :
    ancestorCoefficient C A p ≡ ancestorCoefficient C A q [ZMOD m] := by
  have hp : (∏ i ∈ A, p i) ≡ (∏ i ∈ A, q i) [ZMOD m] := by
    induction A using Finset.induction_on with
    | empty => exact .rfl
    | @insert i A hi ih =>
      simp only [Finset.prod_insert hi]
      exact (h i (Finset.mem_insert_self i A)).mul
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
  exact hp.mul_left C

/-- Only ancestors occur in a coefficient; their depth is strictly smaller.
The order is the preorder in which split products are exposed. -/
structure PivotDependencyScheme (N : ℕ) where
  frequencies : Fin N → NodeFrequencies
  depth : Fin N → ℕ
  fixedLeft : Fin N → ℤ
  fixedRight : Fin N → ℤ
  ancestorsLeft : Fin N → Finset (Fin N)
  ancestorsRight : Fin N → Finset (Fin N)
  earlierLeft : ∀ j i, i ∈ ancestorsLeft j → i.val < j.val ∧ depth i < depth j
  earlierRight : ∀ j i, i ∈ ancestorsRight j → i.val < j.val ∧ depth i < depth j

def PivotDependencyScheme.leftCoefficient {N : ℕ} (D : PivotDependencyScheme N)
    (p : Fin N → ℤ) (j : Fin N) : ℤ := ancestorCoefficient (D.fixedLeft j) (D.ancestorsLeft j) p

def PivotDependencyScheme.rightCoefficient {N : ℕ} (D : PivotDependencyScheme N)
    (p : Fin N → ℤ) (j : Fin N) : ℤ := ancestorCoefficient (D.fixedRight j) (D.ancestorsRight j) p

/-- The literal integer reversal equation, with the two selected bulk products. -/
def PivotDependencyScheme.equations {N : ℕ} (D : PivotDependencyScheme N)
    (L R p : Fin N → ℤ) : Prop :=
  ∀ j, (D.frequencies j).left * D.leftCoefficient p j * R j -
    (D.frequencies j).right * D.rightCoefficient p j * L j = (D.frequencies j).root * p j

/-- Among already exposed nodes, all reconstructed pivots are determined
at a precision depending only on their own ancestor depth. -/
theorem PivotDependencyScheme.pivot_prefix_precision {N : ℕ} (D : PivotDependencyScheme N)
    (R k J : ℕ) (hdepth : ∀ j, D.depth j ≤ k)
    (hs : ∀ j, (D.frequencies j).root ≠ 0)
    (hsR : ∀ j, (D.frequencies j).root.natAbs ∣ R)
    (L₁ R₁ p₁ L₂ R₂ p₂ : Fin N → ℤ)
    (heq₁ : D.equations L₁ R₁ p₁) (heq₂ : D.equations L₂ R₂ p₂)
    (hL : ∀ j, j.val < J → L₁ j ≡ L₂ j [ZMOD (R : ℤ) ^ (k + 2)])
    (hR : ∀ j, j.val < J → R₁ j ≡ R₂ j [ZMOD (R : ℤ) ^ (k + 2)]) :
    ∀ j, j.val < J → p₁ j ≡ p₂ j [ZMOD (R : ℤ) ^ (k + 1 - D.depth j)] := by
  intro j hj
  have hall : ∀ a : ℕ, ∀ j : Fin N, j.val = a → j.val < J →
      p₁ j ≡ p₂ j [ZMOD (R : ℤ) ^ (k + 1 - D.depth j)] := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro j hja hj
      have hcoeff (C : ℤ) (A : Finset (Fin N))
          (hA : ∀ i ∈ A, i.val < j.val ∧ D.depth i < D.depth j) :
          ancestorCoefficient C A p₁ ≡ ancestorCoefficient C A p₂
            [ZMOD (R : ℤ) ^ (k + 2 - D.depth j)] := by
        apply ancestorCoefficient_modEq
        intro i hi
        obtain ⟨hij, hdij⟩ := hA i hi
        have hp := ih i.val (by omega) i rfl (by omega)
        exact hp.of_dvd (pow_dvd_pow (R : ℤ) (by have := hdepth i; have := hdepth j; omega))
      have hcL := hcoeff (D.fixedLeft j) (D.ancestorsLeft j) (D.earlierLeft j)
      have hcR := hcoeff (D.fixedRight j) (D.ancestorsRight j) (D.earlierRight j)
      have hlj := (hL j hj).of_dvd (pow_dvd_pow (R : ℤ) (Nat.sub_le (k + 2) (D.depth j)))
      have hrj := (hR j hj).of_dvd (pow_dvd_pow (R : ℤ) (Nat.sub_le (k + 2) (D.depth j)))
      have hnum := ((hcL.mul_left (D.frequencies j).left).mul hrj).sub
        ((hcR.mul_left (D.frequencies j).right).mul hlj)
      have hroot : (D.frequencies j).root ∣ (R : ℤ) :=
        Int.natAbs_dvd.mp (Int.natCast_dvd_natCast.mpr (hsR j))
      have hx := reversal_residue_precision (R : ℤ) (D.frequencies j).root 1 1
        ((D.frequencies j).left * D.leftCoefficient p₁ j * R₁ j -
          (D.frequencies j).right * D.rightCoefficient p₁ j * L₁ j)
        ((D.frequencies j).left * D.leftCoefficient p₂ j * R₂ j -
          (D.frequencies j).right * D.rightCoefficient p₂ j * L₂ j)
        (p₁ j) (p₂ j) (k + 1 - D.depth j) (hs j) hroot (isCoprime_one_left)
        (by simpa only [mul_one] using heq₁ j) (by simpa only [mul_one] using heq₂ j)
        (by
          have he : k + 1 - D.depth j + 1 = k + 2 - D.depth j := by have := hdepth j; omega
          rw [he]
          exact hnum) (.refl 1)
      exact hx
  exact hall j.val j rfl hj

/-- Before the current split is exposed, both coefficients are already
known modulo its root frequency. This is the measurability step needed by
the sequential uniform-root count. -/
theorem PivotDependencyScheme.coefficients_prefix_precision {N : ℕ}
    (D : PivotDependencyScheme N) (R k : ℕ) (j : Fin N)
    (hdepth : ∀ i, D.depth i ≤ k) (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (L₁ R₁ p₁ L₂ R₂ p₂ : Fin N → ℤ)
    (heq₁ : D.equations L₁ R₁ p₁) (heq₂ : D.equations L₂ R₂ p₂)
    (hL : ∀ i, i.val < j.val → L₁ i ≡ L₂ i [ZMOD (R : ℤ) ^ (k + 2)])
    (hR : ∀ i, i.val < j.val → R₁ i ≡ R₂ i [ZMOD (R : ℤ) ^ (k + 2)]) :
    D.leftCoefficient p₁ j ≡ D.leftCoefficient p₂ j [ZMOD (D.frequencies j).root.natAbs] ∧
      D.rightCoefficient p₁ j ≡ D.rightCoefficient p₂ j [ZMOD (D.frequencies j).root.natAbs] := by
  have hp := D.pivot_prefix_precision R k j.val hdepth hs hsR L₁ R₁ p₁ L₂ R₂ p₂ heq₁ heq₂ hL hR
  have hcoeff (C : ℤ) (A : Finset (Fin N))
      (hA : ∀ i ∈ A, i.val < j.val ∧ D.depth i < D.depth j) :
      ancestorCoefficient C A p₁ ≡ ancestorCoefficient C A p₂
        [ZMOD (D.frequencies j).root.natAbs] := by
    apply ancestorCoefficient_modEq
    intro i hi
    obtain ⟨hij, _⟩ := hA i hi
    apply (hp i hij).of_dvd
    exact (Int.natCast_dvd_natCast.mpr (hsR j)).trans
      (dvd_pow_self (R : ℤ) (by have := hdepth i; omega))
  exact ⟨hcoeff _ _ (D.earlierLeft j), hcoeff _ _ (D.earlierRight j)⟩

end Ostmann

end OAI
