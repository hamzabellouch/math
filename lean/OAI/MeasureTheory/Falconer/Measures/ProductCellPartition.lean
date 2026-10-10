import OAI.MeasureTheory.Falconer.Estimates.DyadicTree

namespace OAI

/-! # The finite product-cell count in the starting-pair preparation -/
namespace Falconer
open Set MeasureTheory

theorem DyadicCube.product_cells_disjoint {d J : ℕ} (Q : DyadicCube d)
    {p q : List (Fin d → Bool) × List (Fin d → Bool)}
    (hp : p ∈ (cubePaths d J).product (cubePaths d J))
    (hq : q ∈ (cubePaths d J).product (cubePaths d J)) (hne : p ≠ q) :
    Disjoint ((Q.descendant p.1).carrier ×ˢ (Q.descendant p.2).carrier)
      ((Q.descendant q.1).carrier ×ˢ (Q.descendant q.2).carrier) := by
  obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨hq1,hq2⟩ := Finset.mem_product.mp hq
  apply Set.disjoint_left.mpr
  intro z hz hz'
  by_cases he : p.1 = q.1
  · have he2 : p.2 ≠ q.2 := fun hh => hne (Prod.ext he hh)
    exact Set.disjoint_left.mp (Q.descendants_disjoint
      (((mem_cubePaths d J p.2).mp hp2).trans ((mem_cubePaths d J q.2).mp hq2).symm) he2) hz.2 hz'.2
  · exact Set.disjoint_left.mp (Q.descendants_disjoint
      (((mem_cubePaths d J p.1).mp hp1).trans ((mem_cubePaths d J q.1).mp hq1).symm) he) hz.1 hz'.1

theorem dyadic_product_card_bound {d N : ℕ} {ω : ℝ} (hω : 0 ≤ ω)
    (T : Finset (List (Fin d → Bool) × List (Fin d → Bool)))
    (hT : T ⊆ (cubePaths d ⌊ω*(N:ℝ)⌋₊).product (cubePaths d ⌊ω*(N:ℝ)⌋₊)) :
    (T.card : ℝ) ≤ (2:ℝ)^(2*(d:ℝ)*ω*(N:ℝ)) := by
  let J := ⌊ω*(N:ℝ)⌋₊
  have hc := Finset.card_le_card hT
  rw [Finset.product_eq_sprod,Finset.card_product,card_cubePaths,← pow_add] at hc
  have he : d*J+d*J = 2*d*J := by ring
  change T.card ≤ 2^(d*J+d*J) at hc
  rw [he] at hc
  have hreal : (T.card:ℝ) ≤ (2:ℝ)^(2*d*J) := by exact_mod_cast hc
  have hf : (J:ℝ) ≤ ω*(N:ℝ) := Nat.floor_le (mul_nonneg hω (Nat.cast_nonneg N))
  have hpower : ((2*d*J:ℕ):ℝ) ≤ 2*(d:ℝ)*ω*(N:ℝ) := by
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hf (show 0 ≤ 2*(d:ℝ) by positivity)]
  exact hreal.trans ((Real.rpow_natCast (2:ℝ) (2*d*J)).symm.le.trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hpower))

end Falconer

end OAI
