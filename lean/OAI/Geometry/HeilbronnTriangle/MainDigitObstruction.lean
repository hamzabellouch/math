import OAI.Geometry.HeilbronnTriangle.MainResidueSystem
import OAI.Geometry.HeilbronnTriangle.ParameterSequence
import OAI.Geometry.HeilbronnTriangle.DigitColumnLaw

namespace OAI


noncomputable section

namespace Problem355.MainDigitObstruction

open FiniteFieldLabels Parameters

def extendDigits {k : ℕ} (d : Fin k → ℕ) (v : ℕ) : ℤ :=
  if hv : v < k then d ⟨v, hv⟩ else 0

lemma extendDigits_at {k : ℕ} (d : Fin k → ℕ) (v : Fin k) :
    extendDigits d v.val = (d v : ℤ) := by
  simp only [extendDigits, dite_eq_left v.isLt]

lemma sum_extendDigits {B k : ℕ} (d : Fin k → ℕ) :
    (∑ v ∈ Finset.range k, extendDigits d v * (B : ℤ) ^ v) =
      ((∑ v : Fin k, d v * B ^ v.val : ℕ) : ℤ) := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [extendDigits_at, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]

theorem finite_small_det_forces_repeated_labels
    {r : ℕ} [Fact r.Prime] (hr : 2 < r)
    (D : PrimeParameterData heilbronnK r)
    (h : ℕ) (hh : h = D.h)
    (labels : Fin 3 → Label r)
    (d : Fin 3 → Fin 3 → Fin heilbronnK → ℕ)
    (hd : ∀ i j v, d i j v ≤ r ^ 10)
    (hresidue : ∀ i j v, (d i j v : ZMod r) =
      MainResidueSystem.finiteResidue r i v (labels j))
    (A : Matrix (Fin 3) (Fin 3) ℤ)
    (G : Matrix.SpecialLinearGroup (Fin 3) (ZMod h))
    (hAC : A.map (Int.castRingHom (ZMod h)) =
      G.val * (Matrix.of (fun i j =>
        ((∑ v : Fin heilbronnK, d i j v * D.B ^ v.val : ℕ) : ZMod h)) :
          Matrix (Fin 3) (Fin 3) (ZMod h)))
    (hsmall : |A.det| ≤ (D.tau : ℤ)) :
    ∃ i j : Fin 3, i ≠ j ∧ labels i = labels j := by
  let ds : Fin 3 → Fin 3 → ℕ → ℤ := fun i j => extendDigits (d i j)
  refine MainResidueSystem.small_det_forces_repeated_labels r hr D.B
    (r ^ 10 : ℕ) (by have := D.base_ge_three; omega) (by positivity)
    (by exact_mod_cast D.base_lower_original) labels ds ?_ ?_ A h hh G ?_ ?_
  · intro i j v hv
    change |extendDigits (d i j) v| ≤ ((r ^ 10 : ℕ) : ℤ)
    rw [show extendDigits (d i j) v = (d i j ⟨v, hv⟩ : ℤ) by
      simp only [extendDigits, dite_eq_left hv]]
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast hd i j ⟨v, hv⟩
  · intro i j v hv
    change ((extendDigits (d i j) v : ℤ) : ZMod r) = _
    simpa only [extendDigits, dite_eq_left hv, Int.cast_natCast,
      MainResidueSystem.finiteResidue] using hresidue i j ⟨v, hv⟩
  · have hmatrix :
        Matrix.map (fun i j => ∑ v ∈ Finset.range heilbronnK,
          ds i j v * (D.B : ℤ) ^ v) (Int.castRingHom (ZMod h)) =
          Matrix.of (fun i j =>
            ((∑ v : Fin heilbronnK, d i j v * D.B ^ v.val : ℕ) : ZMod h)) := by
      ext i j
      change (((∑ v ∈ Finset.range heilbronnK,
        extendDigits (d i j) v * (D.B : ℤ) ^ v) : ℤ) : ZMod h) = _
      rw [sum_extendDigits]
      simp only [Int.cast_natCast, Matrix.of_apply]
    rw [hmatrix]
    exact hAC
  · simpa only [PrimeParameterData.tau, threshold, Int.natCast_div,
      Nat.cast_pow, Nat.cast_ofNat] using hsmall

end Problem355.MainDigitObstruction

end

end OAI
