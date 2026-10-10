import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters
open Construction Preliminaries

def characterDoubleShell {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q)) :
    Fin (b+b) → Finset (PrimeUpTo Q) := Fin.append E E

def characterDoubleChar {b : ℕ} (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ) :
    Fin (b+b) → (q : ℕ) → MulChar (ZMod q) ℂ :=
  Fin.append χ (fun i q => star (χ i q))

def characterDoubleCenter {b : ℕ} (a : Fin b → (q : ℕ) → ZMod q) :
    Fin (b+b) → (q : ℕ) → ZMod q := Fin.append a a

def characterDoublePhase {b : ℕ} (z : Fin b → ℕ → ℂ) : Fin (b+b) → ℕ → ℂ :=
  Fin.append z (fun i q => conj (z i q))

def characterDoubleMask {Q b : ℕ} (B : (Fin b → PrimeUpTo Q) → ℝ)
    (w : Fin (b+b) → PrimeUpTo Q) : ℝ :=
  B (fun i => w (Fin.castAdd b i))*B (fun i => w (Fin.natAdd b i))

def characterTupleSplit {κ : Type*} (b : ℕ) :
    (Fin (b+b) → κ) ≃ ((Fin b → κ) × (Fin b → κ)) where
  toFun w := (fun i => w (Fin.castAdd b i), fun i => w (Fin.natAdd b i))
  invFun w := Fin.append w.1 w.2
  left_inv w := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [Fin.append_left, Fin.append_right]
  right_inv w := by
    apply Prod.ext <;> funext i <;> simp only [Fin.append_left, Fin.append_right]

theorem characterDoubleShell_positive {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i)) :
    ∀ i, 0 < primeShellMass (characterDoubleShell E i) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simpa only [characterDoubleShell, Fin.append_left, Fin.append_right] using hE j

theorem characterDoublePrior_mass {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i)) (w : Fin (b+b) → PrimeUpTo Q) :
    (characterTuplePrior (characterDoubleShell E) (characterDoubleShell_positive E hE)).mass w =
      (characterTuplePrior E hE).mass (characterTupleSplit b w).1 *
      (characterTuplePrior E hE).mass (characterTupleSplit b w).2 := by
  simp only [characterTuplePrior, productPrior, Fin.prod_univ_add, characterDoubleShell,
    Fin.append_left, Fin.append_right, characterTupleSplit, Equiv.coe_fn_mk]

theorem characterDoubleTest_eq {Q b : ℕ}
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (w : Fin (b+b) → PrimeUpTo Q) (n : ℤ) :
    characterTupleTest (characterDoubleChar χ) (characterDoubleCenter a) (characterDoublePhase z) w n =
      characterTupleTest χ a z (characterTupleSplit b w).1 n *
        conj (characterTupleTest χ a z (characterTupleSplit b w).2 n) := by
  simp only [characterTupleTest, Fin.prod_univ_add, characterDoubleChar, characterDoubleCenter,
    characterDoublePhase, Fin.append_left, Fin.append_right, phasedCharacter,
    characterTupleSplit, Equiv.coe_fn_mk, map_prod, map_mul, MulChar.star_apply, RCLike.star_def]
  rfl

theorem characterDoubleMean_eq_norm_sq {Q b : ℕ}
    (E : Fin b → Finset (PrimeUpTo Q)) (hE : ∀ i, 0 < primeShellMass (E i))
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (a : Fin b → (q : ℕ) → ZMod q) (z : Fin b → ℕ → ℂ)
    (B : (Fin b → PrimeUpTo Q) → ℝ) (n : ℤ) :
    initialCharacterMean (characterDoubleShell E) (characterDoubleShell_positive E hE)
      (characterDoubleChar χ) (characterDoubleCenter a) (characterDoublePhase z)
      (characterDoubleMask B) n = (‖initialCharacterMean E hE χ a z B n‖^2 : ℝ) := by
  let μ := characterTuplePrior E hE
  let f := fun w : Fin b → PrimeUpTo Q => (B w : ℂ)*characterTupleTest χ a z w n
  have he : initialCharacterMean (characterDoubleShell E) (characterDoubleShell_positive E hE)
      (characterDoubleChar χ) (characterDoubleCenter a) (characterDoublePhase z)
      (characterDoubleMask B) n =
      ∑ y : (Fin b → PrimeUpTo Q) × (Fin b → PrimeUpTo Q),
        (μ.mass y.1 : ℂ)*(μ.mass y.2 : ℂ)*f y.1*conj (f y.2) := by
    unfold initialCharacterMean FinitePrior.cmean
    rw [← (characterTupleSplit b).sum_comp (fun y =>
      (μ.mass y.1 : ℂ)*(μ.mass y.2 : ℂ)*f y.1*conj (f y.2))]
    apply Finset.sum_congr rfl
    intro w hw
    dsimp only
    rw [characterDoublePrior_mass E hE, characterDoubleTest_eq]
    simp only [f, μ, characterDoubleMask, characterTupleSplit, Equiv.coe_fn_mk,
      Complex.ofReal_mul, map_mul, Complex.conj_ofReal]
    ring
  rw [he]
  have hs : (∑ y : (Fin b → PrimeUpTo Q) × (Fin b → PrimeUpTo Q),
      (μ.mass y.1 : ℂ)*(μ.mass y.2 : ℂ)*f y.1*conj (f y.2)) =
      μ.cmean f*conj (μ.cmean f) := by
    simp only [Fintype.sum_prod_type, FinitePrior.cmean, map_sum, map_mul,
      Complex.conj_ofReal]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  rw [hs, Complex.mul_conj']
  simp only [Complex.ofReal_pow]
  rfl

end Ostmann.Characters

end

end OAI
