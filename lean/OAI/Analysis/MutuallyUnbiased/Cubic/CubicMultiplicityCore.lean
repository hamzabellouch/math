import OAI.Analysis.MutuallyUnbiased.Cubic.CubicSymmetric

namespace OAI

/-! Multiplicity counting once the two possible cubed values are known. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_cube_mul_conj_square {z : ℂ} (hz : Complex.normSq z = 1) :
    z ^ 3 * (conj z) ^ 2 = z := by
  calc
    z ^ 3 * (conj z) ^ 2 = z * (z * conj z) ^ 2 := by ring
    _ = z := by simp [Complex.mul_conj, hz]

def cubeClass (v : (Fin 6) → ℂ) (a : ℂ) : Finset (Fin 6) := by
  classical
  exact Finset.univ.filter (fun i => v i ^ 3 = a)

/-- A nonempty zero-sum collection of nonzero numbers with the same cube has
at least three members: one term cannot vanish, and two opposite terms have
opposite cubes. -/
theorem same_cube_zero_sum_card_ge_three (v : (Fin 6) → ℂ) (s : Finset (Fin 6))
    (a : ℂ) (ha : a ≠ 0) (hne : s.Nonempty)
    (hcube : ∀ i ∈ s, v i ^ 3 = a) (hsum : ∑ i ∈ s, v i = 0) :
    3 ≤ s.card := by
  by_contra h
  have hp := hne.card_pos
  have hc : s.card = 1 ∨ s.card = 2 := by omega
  rcases hc with hc | hc
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
    have hi := hcube i (by simp)
    simp only [Finset.sum_singleton] at hsum
    exact ha (by simpa [hsum] using hi.symm)
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hc
    have hi := hcube i (by simp)
    have hj := hcube j (by simp)
    have hsum' : v i + v j = 0 := by simpa [hij] using hsum
    have hneg : v i = -v j := eq_neg_of_add_eq_zero_left hsum'
    have hanti : -a = a := by
      calc
        -a = -(v j ^ 3) := by rw [hj]
        _ = (-v j) ^ 3 := by ring
        _ = a := by simpa only [hneg] using hi
    apply ha
    linear_combination -(1 / 2 : ℂ) * hanti

theorem two_cube_classes_card_three (v : (Fin 6) → ℂ)
    (hv : ∀ i, Complex.normSq (v i) = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0)
    (a b : ℂ) (hab : a ≠ b)
    (hvalues : ∀ i, v i ^ 3 = a ∨ v i ^ 3 = b)
    (ia ib : (Fin 6)) (hia : v ia ^ 3 = a) (hib : v ib ^ 3 = b) :
    (cubeClass v a).card = 3 ∧ (cubeClass v b).card = 3 ∧
      (∑ i ∈ cubeClass v a, v i) = 0 ∧ (∑ i ∈ cubeClass v b, v i) = 0 := by
  classical
  let A := cubeClass v a
  have hAcube : ∀ i ∈ A, v i ^ 3 = a := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hBcube : ∀ i ∈ Aᶜ, v i ^ 3 = b := by
    intro i hi
    have hnot : v i ^ 3 ≠ a := by simpa [A, cubeClass] using hi
    exact (hvalues i).resolve_left hnot
  have hB : Aᶜ = cubeClass v b := by
    ext i
    simp only [cubeClass, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact hBcube i
    · intro hi
      have hnot : v i ^ 3 ≠ a := by
        intro heq
        exact hab (heq.symm.trans hi)
      simpa [A, cubeClass] using hnot
  let qa := ∑ i ∈ A, (conj (v i)) ^ 2
  let qb := ∑ i ∈ Aᶜ, (conj (v i)) ^ 2
  have hqa : (∑ i ∈ A, v i) = a * qa := by
    dsimp [qa]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hu := unit_cube_mul_conj_square (hv i)
    rw [hAcube i hi] at hu
    exact hu.symm
  have hqb : (∑ i ∈ Aᶜ, v i) = b * qb := by
    dsimp [qb]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hu := unit_cube_mul_conj_square (hv i)
    rw [hBcube i hi] at hu
    exact hu.symm
  have hq : qa + qb = 0 := by
    calc
      qa + qb = ∑ i, (conj (v i)) ^ 2 :=
        Finset.sum_add_sum_compl A (fun i => (conj (v i)) ^ 2)
      _ = conj (∑ i, v i ^ 2) := by simp
      _ = 0 := by rw [h2, map_zero]
  have hp : a * qa + b * qb = 0 := by
    rw [← hqa, ← hqb, Finset.sum_add_sum_compl, h1]
  have hprod : (a - b) * qa = 0 := by linear_combination hp - b * hq
  have hqa0 : qa = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hab)
  have hqb0 : qb = 0 := by linear_combination hq - hqa0
  have hsumA : (∑ i ∈ A, v i) = 0 := by rw [hqa, hqa0, mul_zero]
  have hsumB : (∑ i ∈ Aᶜ, v i) = 0 := by rw [hqb, hqb0, mul_zero]
  have hia0 : v ia ≠ 0 := by
    intro h
    have hunit := hv ia
    simp [h] at hunit
  have hib0 : v ib ≠ 0 := by
    intro h
    have hunit := hv ib
    simp [h] at hunit
  have ha : a ≠ 0 := hia ▸ pow_ne_zero 3 hia0
  have hb : b ≠ 0 := hib ▸ pow_ne_zero 3 hib0
  have hneA : A.Nonempty := ⟨ia, by simp [A, cubeClass, hia]⟩
  have hneB : (Aᶜ).Nonempty := by
    refine ⟨ib, ?_⟩
    simp [A, cubeClass, hib, Ne.symm hab]
  have hcardA := same_cube_zero_sum_card_ge_three v A a ha hneA hAcube hsumA
  have hcardB := same_cube_zero_sum_card_ge_three v Aᶜ b hb hneB hBcube hsumB
  have hbound : A.card ≤ 6 := by simpa using Finset.card_le_univ A
  have hcompl : (Aᶜ).card = 6 - A.card := by simpa using Finset.card_compl A
  have heqA : A.card = 3 := by omega
  have heqB : (Aᶜ).card = 3 := by omega
  exact ⟨heqA, hB ▸ heqB, hsumA, hB ▸ hsumB⟩

end MUB6

end

end OAI
