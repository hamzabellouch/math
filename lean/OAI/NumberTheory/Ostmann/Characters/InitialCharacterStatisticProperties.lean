import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticDouble

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters
open Construction Preliminaries

theorem characterDoubleChar_nonprincipal {Q b : ℕ}
    (E : Fin b → Finset (PrimeUpTo Q))
    (χ : Fin b → (q : ℕ) → MulChar (ZMod q) ℂ)
    (hχ : ∀ i, ∀ p ∈ E i, χ i p.val ≠ 1) :
    ∀ i, ∀ p ∈ characterDoubleShell E i, characterDoubleChar χ i p.val ≠ 1 := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [characterDoubleShell, characterDoubleChar, Fin.append_left] using hχ j
  · intro p hp
    simp only [characterDoubleShell, Fin.append_right] at hp
    simp only [characterDoubleChar, Fin.append_right]
    intro he
    have hh := congrArg star he
    simp only [star_star, star_one] at hh
    exact hχ j p hp hh

theorem characterDoublePhase_bound {Q b : ℕ}
    (E : Fin b → Finset (PrimeUpTo Q)) (z : Fin b → ℕ → ℂ)
    (hz : ∀ i, ∀ p ∈ E i, ‖z i p.val‖ ≤ 1) :
    ∀ i, ∀ p ∈ characterDoubleShell E i, ‖characterDoublePhase z i p.val‖ ≤ 1 := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [characterDoubleShell, characterDoublePhase, Fin.append_left] using hz j
  · simpa only [characterDoubleShell, characterDoublePhase, Fin.append_right, Complex.norm_conj] using hz j

theorem characterDoubleMask_bounds {Q b : ℕ} (B : (Fin b → PrimeUpTo Q) → ℝ)
    (hB : ∀ w, 0 ≤ B w ∧ B w ≤ 1) :
    ∀ w, 0 ≤ characterDoubleMask B w ∧ characterDoubleMask B w ≤ 1 := by
  intro w
  exact ⟨mul_nonneg (hB _).1 (hB _).1,
    (mul_le_mul (hB _).2 (hB _).2 (hB _).1 zero_le_one).trans_eq (one_mul 1)⟩

theorem characterDoubleShell_min {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q))
    {R : ℝ} (hmin : ∀ i, ∀ p ∈ E i, R ≤ (p.val : ℝ)) :
    ∀ i, ∀ p ∈ characterDoubleShell E i, R ≤ (p.val : ℝ) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simpa only [characterDoubleShell, Fin.append_left, Fin.append_right] using hmin j

theorem characterDoubleShell_normalization {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q)) :
    (∏ i, (primeShellMass (characterDoubleShell E i))⁻¹) =
      (∏ i, (primeShellMass (E i))⁻¹)^2 := by
  simp only [Fin.prod_univ_add, characterDoubleShell, Fin.append_left, Fin.append_right, pow_two]

theorem characterDoubleShell_union {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q)) :
    Finset.univ.biUnion (characterDoubleShell E) = Finset.univ.biUnion E := by
  classical
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i,hi⟩
    revert hi
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> intro hj <;>
      exact ⟨j,by simpa only [characterDoubleShell, Fin.append_left, Fin.append_right] using hj⟩
  · rintro ⟨i,hi⟩
    exact ⟨Fin.castAdd b i,by simpa only [characterDoubleShell, Fin.append_left] using hi⟩

end Ostmann.Characters

end

end OAI
