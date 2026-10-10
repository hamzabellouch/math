import OAI.Probability.ContinuumTransition.GridBoundary

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

noncomputable def gridIndices (m q : ℕ) : Finset Lattice :=
  Fintype.piFinset (fun _ : Fin 3 => indexInterval m q)

noncomputable def boundaryIndices (m q H : ℕ) : Finset Lattice :=
  Finset.univ.biUnion (fun i : Fin 3 => Fintype.piFinset
    (fun j : Fin 3 => if j = i then edgeIndices m q H else indexInterval m q))

theorem card_gridIndices (m q : ℕ) : (gridIndices m q).card = (2*m*q+1)^3 := by
  simp only [gridIndices, Fintype.card_piFinset, card_indexInterval, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem card_boundaryIndices_le (m q H : ℕ) (hq : 0 < q) :
    (boundaryIndices m q H).card ≤ 3*((2*m+1)*(2*H))*(2*m*q+1)^2 := by
  have hc (i : Fin 3) : (Fintype.piFinset (fun j : Fin 3 =>
      if j = i then edgeIndices m q H else indexInterval m q)).card ≤
      ((2*m+1)*(2*H))*(2*m*q+1)^2 := by
    rw [Fintype.card_piFinset]
    have he : (∏ j : Fin 3, (if j = i then edgeIndices m q H else indexInterval m q).card) =
        (edgeIndices m q H).card*(indexInterval m q).card^2 := by
      fin_cases i <;> simp [Fin.prod_univ_succ] <;> ring
    rw [he, card_indexInterval]
    exact Nat.mul_le_mul_right _ (card_edgeIndices_le m q H hq)
  have hh := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin 3)))
    (t := fun i : Fin 3 => Fintype.piFinset
      (fun j : Fin 3 => if j = i then edgeIndices m q H else indexInterval m q))
  have hh' := hh.trans (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hc i))
  simpa only [boundaryIndices, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_assoc] using hh'

theorem mem_boundaryIndices {m q H : ℕ} {k : Lattice} (hk : k ∈ gridIndices m q)
    (he : ∃ i, k i ∈ edgeIndices m q H) : k ∈ boundaryIndices m q H := by
  obtain ⟨i, hi⟩ := he
  apply Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
  apply Fintype.mem_piFinset.mpr
  intro j
  by_cases hj : j = i
  · simpa only [ite_eq_left hj, hj, ite_true] using hi
  · simpa only [ite_eq_right hj] using (Fintype.mem_piFinset.mp hk j)

theorem cellIndex_mem_gridIndices {m q : ℕ} {x : Space}
    (hx : x ∈ cube ((m : ℝ)*(q : ℝ)/2)) : cellIndex x ∈ gridIndices m q := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  have hxi := hx i
  change -↑m*↑q ≤ ⌊4*x i⌋ ∧ ⌊4*x i⌋ ≤ ↑m*↑q
  constructor
  · apply Int.le_floor.mpr
    push_cast
    change -((m : ℝ)*(q : ℝ)/2)/2 ≤ x i ∧ x i ≤ ((m : ℝ)*(q : ℝ)/2)/2 at hxi
    linarith [hxi.1]
  · apply Int.floor_le_iff.mpr
    push_cast
    change -((m : ℝ)*(q : ℝ)/2)/2 ≤ x i ∧ x i ≤ ((m : ℝ)*(q : ℝ)/2)/2 at hxi
    linarith [hxi.2]

theorem boundary_of_close_crossing {q H : ℕ} (hq : 0 < q) {m : ℕ} {x y : Space}
    (hx : x ∈ cube ((m : ℝ)*(q : ℝ)/2))
    (hd : ∀ i, |cellIndex x i-cellIndex y i| ≤ (H : ℤ))
    (hc : gridIndex ((q : ℝ)/4) x ≠ gridIndex ((q : ℝ)/4) y) :
    cellIndex x ∈ boundaryIndices m q H := by
  have hk := cellIndex_mem_gridIndices hx
  apply mem_boundaryIndices hk
  rw [gridIndex_quarter_nat, gridIndex_quarter_nat] at hc
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
  refine ⟨i, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mp hk i, ?_⟩⟩
  exact edgeResidue_of_crossing hq (hd i) hi

end ContinuumTemperature
end

end OAI
