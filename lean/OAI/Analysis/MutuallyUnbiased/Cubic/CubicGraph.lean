import OAI.Analysis.MutuallyUnbiased.Cubic.CubicMatching
import OAI.Analysis.MutuallyUnbiased.Cubic.FiveCycle

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def cubicGraph (H : CMatrix) (i j : Fin 5) : Bool := by
  classical
  exact decide (H i.succ j.succ = omega)

theorem cubic_graph_entry {H : CMatrix} (hcube : ∀ i j, H i j ^ 3 = 1)
    (hdiag : ∀ i j : Fin 5, H i.succ j.succ = 1 ↔ i = j) (i j : Fin 5) :
    H i.succ j.succ = if i = j then 1 else
      if cubicGraph H i j then omega else omega ^ 2 := by
  classical
  by_cases hij : i = j
  · simp [hij, (hdiag j j).mpr rfl]
  · have hne : H i.succ j.succ ≠ 1 := fun h => hij ((hdiag i j).mp h)
    rcases cube_roots_three _ (hcube i.succ j.succ) with h | h | h
    · exact False.elim (hne h)
    · simp [hij, cubicGraph, h]
    · simp [hij, cubicGraph, h, omega_sq_ne_omega]

theorem cubic_graph_degree {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1)
    (h0row : ∀ j, H 0 j = 1) (h0col : ∀ i, H i 0 = 1) (i : Fin 5) :
    (Finset.univ.filter (fun j => cubicGraph H i j = true)).card = 2 := by
  classical
  have hc := cube_roots_each_count (fun j => H i.succ j) (hcube i.succ)
    (cubic_hadamard_row_sum hH h0row i.succ (Fin.succ_ne_zero _)) omega omega_cube
  rw [Fin.card_filter_univ_succ] at hc
  simpa [h0col, Ne.symm omega_ne_one, cubicGraph] using hc

theorem cubic_rows_agree_two {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1) (r s : Coord) (hrs : r ≠ s) :
    (Finset.univ.filter (fun j => H r j = H s j)).card = 2 := by
  classical
  have hv : ∀ j, (H r j / H s j) ^ 3 = 1 := by intro j; simp [div_pow, hcube]
  have hs : (∑ j, H r j / H s j) = 0 := by
    simp_rw [div_eq_mul_inv, unit_inv_eq_conj (hH.1 s _)]
    simpa [hrs] using hH.row_orthogonal r s
  have hc := cube_roots_one_count (fun j => H r j / H s j) hv hs
  simpa only [div_eq_one_iff_eq (unit_ne_zero (hH.1 s _))] using hc

theorem cubic_graph_agreement {H : CMatrix} (hcube : ∀ i j, H i j ^ 3 = 1)
    (hdiag : ∀ i j : Fin 5, H i.succ j.succ = 1 ↔ i = j)
    (i j : Fin 5) (hij : i ≠ j) (k : Fin 5) :
    H i.succ k.succ = H j.succ k.succ ↔
      k ≠ i ∧ k ≠ j ∧ cubicGraph H i k = cubicGraph H j k := by
  by_cases hki : k = i
  · subst k
    have hji : H j.succ i.succ ≠ 1 := fun h => hij ((hdiag j i).mp h).symm
    simp [(hdiag i i).mpr rfl, Ne.symm hji]
  by_cases hkj : k = j
  · subst k
    simp [(hdiag j j).mpr rfl, (hdiag i j), hij]
  rw [cubic_graph_entry hcube hdiag i k, cubic_graph_entry hcube hdiag j k]
  cases hi : cubicGraph H i k <;> cases hj : cubicGraph H j k <;>
    simp [hki, hkj, Ne.symm hki, Ne.symm hkj,
      omega_sq_ne_omega, Ne.symm omega_sq_ne_omega]

theorem cubic_graph_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (hcube : ∀ i j, H i j ^ 3 = 1) (h0col : ∀ i, H i 0 = 1)
    (hdiag : ∀ i j : Fin 5, H i.succ j.succ = 1 ↔ i = j)
    (i j : Fin 5) (hij : i ≠ j) :
    (Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j ∧
      cubicGraph H i k = cubicGraph H j k)).card = 1 := by
  classical
  have hc := cubic_rows_agree_two hH hcube i.succ j.succ
    (fun h => hij (Fin.succ_injective _ h))
  rw [Fin.card_filter_univ_succ] at hc
  simp only [h0col, ite_true] at hc
  simp_rw [cubic_graph_agreement hcube hdiag i j hij] at hc
  omega

theorem tao_noninitial (i j : Fin 5) :
    tao i.succ j.succ = if i = j then 1 else
      if canonicalFiveCycle i j then omega else omega ^ 2 := by
  fin_cases i <;> fin_cases j <;>
    simp [tao, taoExponent, canonicalFiveCycle, fiveGraph]

end MUB6

end

end OAI
