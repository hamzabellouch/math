import OAI.Analysis.MutuallyUnbiased.Matrix.Equivalence

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem isHadamard_of_row_gram (H : CMatrix)
    (hu : ∀ i j, Complex.normSq (H i j) = 1)
    (hr : H * H.conjTranspose = (6 : ℂ) • (1 : CMatrix)) : IsHadamard H := by
  refine ⟨hu, ?_⟩
  have hi : H * ((6 : ℂ)⁻¹ • H.conjTranspose) = (1 : CMatrix) := by
    rw [Matrix.mul_smul, hr, smul_smul]
    norm_num
  have hc := mul_eq_one_comm.mp hi
  rw [Matrix.smul_mul] at hc
  have hs := congrArg (fun M : CMatrix => (6 : ℂ) • M) hc
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0), one_smul]
    using hs

def doubleDifference (i j : Coord) : Charge := difference i j + difference i j

theorem character_doubleDifference (x : Coord → ℂ)
    (hx : ∀ k, Complex.normSq (x k) = 1) (i j : Coord) :
    character x (doubleDifference i j) = x i ^ 2 * conj (x j ^ 2) := by
  rw [doubleDifference, character_add x (fun k => unit_ne_zero (hx k)),
    character_difference x hx, map_pow]
  ring

theorem g_doubleDifference {H : CMatrix} (hH : IsHadamard H) (i j : Coord) :
    g H (doubleDifference i j) =
      (6 : ℂ)⁻¹ * ∑ k, H i k ^ 2 * conj (H j k ^ 2) := by
  simp only [g, character_doubleDifference _ (fun k => hH.1 k _) i j]

theorem square_isHadamard_of_doubleDifference_zero {H : CMatrix} (hH : IsHadamard H)
    (hz : ∀ i j, i ≠ j → g H (doubleDifference i j) = 0) :
    IsHadamard (fun i j => H i j ^ 2) := by
  have hu : ∀ i j, Complex.normSq (H i j ^ 2) = 1 := by
    intro i j
    simp [map_pow, hH.1]
  apply isHadamard_of_row_gram _ hu
  ext i j
  change (∑ k, H i k ^ 2 * conj (H j k ^ 2)) =
    (6 : ℂ) * (if i = j then 1 else 0)
  by_cases hij : i = j
  · subst j
    simp only [Complex.mul_conj, hu, Complex.ofReal_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one, ite_true]
  · have h := hz i j hij
    rw [g_doubleDifference hH] at h
    have hs : (∑ k, H i k ^ 2 * conj (H j k ^ 2)) = 0 :=
      (mul_eq_zero.mp h).resolve_left (by norm_num)
    simpa only [hij, ite_false, mul_zero] using hs

end MUB6

end

end OAI
