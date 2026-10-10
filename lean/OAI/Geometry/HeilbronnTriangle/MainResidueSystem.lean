import OAI.Geometry.HeilbronnTriangle.NormEncoding
import OAI.Geometry.HeilbronnTriangle.LabelResidues
import OAI.Geometry.HeilbronnTriangle.Parameters

namespace OAI


noncomputable section
namespace Problem355.MainResidueSystem

open FiniteFieldLabels

variable (p : ℕ) [Fact p.Prime]

def prescribedResidue (i : Fin 3) (v : ℕ) (x : Label p) : ZMod p :=
  LabelResidues.residue heilbronnT (NormEncoding.normRowFunctions p) i v x

theorem norm_rows_separate (hp : 2 < p) (labels : Fin 3 → Label p)
    (hinj : Function.Injective labels) :
    (∑ a : Fin heilbronnT,
      Matrix.det (fun i j => NormEncoding.normRowFunctions p i a (labels j))) ≠ 0 := by
  have h01 : labels 0 ≠ labels 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h)
  have h02 : labels 0 ≠ labels 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h)
  have h12 : labels 1 ≠ labels 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h)
  have hlabels : (![labels 0, labels 1, labels 2] : Fin 3 → Label p) = labels := by
    funext i
    fin_cases i <;> rfl
  simpa only [hlabels] using NormEncoding.sum_normRowFunctions_ne_zero p hp h01 h02 h12

theorem small_det_forces_repeated_labels (hp : 2 < p)
    (B : ℕ) (L : ℤ) (hB : 2 ≤ B) (hL : 0 ≤ L)
    (hbase : 100 * (heilbronnK : ℤ) ^ 2 * L ^ 3 < B)
    (labels : Fin 3 → Label p) (d : Fin 3 → Fin 3 → ℕ → ℤ)
    (hd : ∀ i j v, v < heilbronnK → |d i j v| ≤ L)
    (hresidue : ∀ i j v, v < heilbronnK →
      (Int.castRingHom (ZMod p)) (d i j v) = prescribedResidue p i v (labels j))
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (h : ℕ) (hh : h = B ^ heilbronnK)
    (G : Matrix.SpecialLinearGroup (Fin 3) (ZMod h))
    (hAC : A.map (Int.castRingHom (ZMod h)) =
      (G : Matrix (Fin 3) (Fin 3) (ZMod h)) *
        (Matrix.map (fun i j => ∑ v ∈ Finset.range heilbronnK, d i j v * (B : ℤ) ^ v)
          (Int.castRingHom (ZMod h))))
    (hsmall : |A.det| ≤ (B : ℤ) ^ (heilbronnK - 1) / 2) :
    ∃ i j : Fin 3, i ≠ j ∧ labels i = labels j := by
  classical
  by_contra hn
  have hinj : Function.Injective labels := by
    intro i j hij
    by_contra hne
    exact hn ⟨i, j, hne, hij⟩
  have hmod := DigitEncoding.determinant_modEq_of_specialLinear h G A
    (fun i j => ∑ v ∈ Finset.range heilbronnK, d i j v * (B : ℤ) ^ v) hAC
  have hpoly : A.det ≡ (DigitCoefficients.determinantPolynomial heilbronnK d).eval
      (B : ℤ) [ZMOD (B : ℤ) ^ heilbronnK] := by
    suffices ∀ (length modulus : ℕ), modulus = B ^ length →
        A.det ≡ Matrix.det (fun i j => ∑ v ∈ Finset.range length,
          d i j v * (B : ℤ) ^ v) [ZMOD modulus] →
        A.det ≡ (DigitCoefficients.determinantPolynomial length d).eval
          (B : ℤ) [ZMOD (B : ℤ) ^ length] from this heilbronnK h hh hmod
    intro length modulus hmodulus hdet
    rw [DigitCoefficients.eval_determinantPolynomial]
    change A.det ≡ Matrix.det (fun i j => ∑ v ∈ Finset.range length,
      d i j v * (B : ℤ) ^ v) [ZMOD (B : ℤ) ^ length]
    simpa only [hmodulus, Nat.cast_pow] using hdet
  have hout := LabelResidues.labeled_polynomial_obstruction_of_length
    (Int.castRingHom (ZMod p)) heilbronnT heilbronnK heilbronnK_eq (B : ℤ) L (by exact_mod_cast hB) hL hbase
    (NormEncoding.normRowFunctions p) labels d hd hresidue
    (norm_rows_separate p hp labels hinj) hpoly
  apply (not_lt_of_ge hsmall)
  exact hout

def finiteResidue (i : Fin 3) (v : Fin heilbronnK) (x : Label p) : ZMod p :=
  prescribedResidue p i v.val x

end Problem355.MainResidueSystem

end

end OAI
