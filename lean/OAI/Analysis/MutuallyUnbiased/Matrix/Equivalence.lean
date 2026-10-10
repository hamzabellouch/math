import OAI.Analysis.MutuallyUnbiased.Matrix.Hadamard

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def phaseTransform (H : CMatrix) (u v : Coord → ℂ) : CMatrix :=
  fun i j => u i * H i j * v j

theorem IsHadamard.phaseTransform {H : CMatrix} (hH : IsHadamard H)
    (u v : Coord → ℂ) (hu : ∀ i, Complex.normSq (u i) = 1)
    (hv : ∀ j, Complex.normSq (v j) = 1) : IsHadamard (phaseTransform H u v) := by
  refine ⟨?_, ?_⟩
  · intro i j
    change Complex.normSq (u i * H i j * v j) = 1
    simp [map_mul, hu, hv, hH.1]
  · ext i j
    have hsum : (∑ k, conj (MUB6.phaseTransform H u v k i) * MUB6.phaseTransform H u v k j) =
        conj (v i) * v j * ∑ k, conj (H k i) * H k j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have huk : conj (u k) * u k = 1 := by
        rw [mul_comm, Complex.mul_conj, hu]
        rfl
      simp only [MUB6.phaseTransform, map_mul]
      calc
        _ = (conj (u k) * u k) *
          (conj (v i) * v j * (conj (H k i) * H k j)) := by ring
        _ = _ := by rw [huk, one_mul]
    change (∑ k, conj (MUB6.phaseTransform H u v k i) * MUB6.phaseTransform H u v k j) =
      (6 : ℂ) * (if i = j then 1 else 0)
    rw [hsum, hH.column_orthogonal]
    by_cases hij : i = j
    · subst j
      rw [mul_comm (conj (v i)) (v i), Complex.mul_conj, hv]
      simp
    · simp [hij]

theorem IsHadamard.permutations {H : CMatrix} (hH : IsHadamard H)
    (r c : Equiv.Perm Coord) : IsHadamard (fun i j => H (r i) (c j)) := by
  refine ⟨fun i j => hH.1 _ _, ?_⟩
  ext i j
  change (∑ k, conj (H (r k) (c i)) * H (r k) (c j)) =
    (6 : ℂ) * (if i = j then 1 else 0)
  rw [Equiv.sum_comp r (fun k => conj (H k (c i)) * H k (c j)), hH.column_orthogonal]
  simp only [Equiv.apply_eq_iff_eq]
  split_ifs <;> norm_num

theorem Equivalent.isHadamard {H K : CMatrix} (h : Equivalent H K)
    (hH : IsHadamard H) : IsHadamard K := by
  rcases h with ⟨r, c, u, v, hu, hv, he⟩
  have hK : K = phaseTransform (fun i j => H (r i) (c j)) u v := by
    ext i j
    exact he i j
  rw [hK]
  exact (hH.permutations r c).phaseTransform u v hu hv

def dephase (H : CMatrix) : CMatrix :=
  phaseTransform H (fun i => (H i 0)⁻¹) (fun j => H 0 0 * (H 0 j)⁻¹)

theorem dephase_equivalent {H : CMatrix} (hH : IsHadamard H) :
    Equivalent H (dephase H) := by
  refine ⟨Equiv.refl _, Equiv.refl _, (fun i => (H i 0)⁻¹),
    (fun j => H 0 0 * (H 0 j)⁻¹), ?_, ?_, ?_⟩
  · intro i
    simp [hH.1]
  · intro j
    simp [map_mul, hH.1]
  · intro i j
    rfl

theorem dephase_isHadamard {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard (dephase H) := (dephase_equivalent hH).isHadamard hH

theorem dephase_row_zero {H : CMatrix} (hH : IsHadamard H) (j : Coord) :
    dephase H 0 j = 1 := by
  unfold dephase phaseTransform
  field_simp [unit_ne_zero (hH.1 0 0), unit_ne_zero (hH.1 0 j)]

theorem dephase_column_zero {H : CMatrix} (hH : IsHadamard H) (i : Coord) :
    dephase H i 0 = 1 := by
  unfold dephase phaseTransform
  field_simp [unit_ne_zero (hH.1 0 0), unit_ne_zero (hH.1 i 0)]

theorem equivalent_squares {H K : CMatrix} (h : Equivalent H K) :
    Equivalent (fun i j => H i j ^ 2) (fun i j => K i j ^ 2) := by
  rcases h with ⟨r, c, u, v, hu, hv, he⟩
  refine ⟨r, c, (fun i => u i ^ 2), (fun j => v j ^ 2), ?_, ?_, ?_⟩
  · intro i
    simp [map_pow, hu]
  · intro j
    simp [map_pow, hv]
  · intro i j
    change K i j ^ 2 = u i ^ 2 * H (r i) (c j) ^ 2 * v j ^ 2
    rw [he]
    ring

theorem dephase_square_isHadamard {H : CMatrix} (hH : IsHadamard H)
    (hH2 : IsHadamard (fun i j => H i j ^ 2)) :
    IsHadamard (fun i j => dephase H i j ^ 2) :=
  (equivalent_squares (dephase_equivalent hH)).isHadamard hH2

end MUB6

end

end OAI
