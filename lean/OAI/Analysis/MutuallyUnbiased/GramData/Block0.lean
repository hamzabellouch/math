import OAI.Analysis.MutuallyUnbiased.Certificate.Gram

namespace OAI

/-!
Exact integer matrix for λ = (1, 1, 1, 2), m = 5, exponent = 14.
-/

namespace MUB6.Certificate.GramData.Block0

open Matrix
open scoped BigOperators

def Z : Matrix (Fin 5) (Fin 5) ℚ := ![
  ![7856995, -2793048, 8971673, 4076125, -23581960],
  ![-2793048, 5486181, -1693736, -2967341, 9048932],
  ![8971673, -1693736, 37455549, -242661, -37895129],
  ![4076125, -2967341, -242661, 7655001, -9254062],
  ![-23581960, 9048932, -37895129, -9254062, 86753990]
]

def entries : Matrix (Fin 5) (Fin 5) ℚ := ![
  ![0, 0, 0, 0, 0],
  ![(1603752121147568130199833465 / 40829555837800662670634310286), 0, 0, 0, 0],
  ![(-62916225621601789934 / 3499499328906931120789), (562467881435179530688 / 10498497986720793362367), 0, 0, 0],
  ![(67695593783615 / 289232108352073), (-86844646839403 / 289232108352073), (-185867841615694 / 289232108352073), 0, 0],
  ![(-2358196 / 8675399), (4524466 / 43376995), (-37895129 / 86753990), (-4627031 / 43376995), 0]
]

def D : Fin 5 → ℚ := ![(43674396936336248004625370017787053 / 40829555837800662670634310286), (40829555837800662670634310286 / 10498497986720793362367), (10498497986720793362367 / 578464216704146), (289232108352073 / 43376995), 86753990]

theorem pivot_0 : 40000 < D 0 := by decide +kernel

theorem pivot_1 : 40000 < D 1 := by decide +kernel

theorem pivot_2 : 40000 < D 2 := by decide +kernel

theorem pivot_3 : 40000 < D 3 := by decide +kernel

theorem pivot_4 : 40000 < D 4 := by decide +kernel

theorem entry_0_0 : Z 0 0 =
    ∑ k : Fin 5, lowerUnit entries k 0 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_0_1 : Z 0 1 =
    ∑ k : Fin 5, lowerUnit entries k 0 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_0_2 : Z 0 2 =
    ∑ k : Fin 5, lowerUnit entries k 0 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_0_3 : Z 0 3 =
    ∑ k : Fin 5, lowerUnit entries k 0 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_0_4 : Z 0 4 =
    ∑ k : Fin 5, lowerUnit entries k 0 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_1_0 : Z 1 0 =
    ∑ k : Fin 5, lowerUnit entries k 1 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_1_1 : Z 1 1 =
    ∑ k : Fin 5, lowerUnit entries k 1 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_1_2 : Z 1 2 =
    ∑ k : Fin 5, lowerUnit entries k 1 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_1_3 : Z 1 3 =
    ∑ k : Fin 5, lowerUnit entries k 1 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_1_4 : Z 1 4 =
    ∑ k : Fin 5, lowerUnit entries k 1 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_2_0 : Z 2 0 =
    ∑ k : Fin 5, lowerUnit entries k 2 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_2_1 : Z 2 1 =
    ∑ k : Fin 5, lowerUnit entries k 2 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_2_2 : Z 2 2 =
    ∑ k : Fin 5, lowerUnit entries k 2 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_2_3 : Z 2 3 =
    ∑ k : Fin 5, lowerUnit entries k 2 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_2_4 : Z 2 4 =
    ∑ k : Fin 5, lowerUnit entries k 2 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_3_0 : Z 3 0 =
    ∑ k : Fin 5, lowerUnit entries k 3 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_3_1 : Z 3 1 =
    ∑ k : Fin 5, lowerUnit entries k 3 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_3_2 : Z 3 2 =
    ∑ k : Fin 5, lowerUnit entries k 3 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_3_3 : Z 3 3 =
    ∑ k : Fin 5, lowerUnit entries k 3 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_3_4 : Z 3 4 =
    ∑ k : Fin 5, lowerUnit entries k 3 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_4_0 : Z 4 0 =
    ∑ k : Fin 5, lowerUnit entries k 4 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_4_1 : Z 4 1 =
    ∑ k : Fin 5, lowerUnit entries k 4 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_4_2 : Z 4 2 =
    ∑ k : Fin 5, lowerUnit entries k 4 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_4_3 : Z 4 3 =
    ∑ k : Fin 5, lowerUnit entries k 4 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_4_4 : Z 4 4 =
    ∑ k : Fin 5, lowerUnit entries k 4 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem pivots_pos : ∀ k : Fin 5, 0 < D k := by
  intro k
  fin_cases k
  · exact lt_trans (by norm_num) pivot_0
  · exact lt_trans (by norm_num) pivot_1
  · exact lt_trans (by norm_num) pivot_2
  · exact lt_trans (by norm_num) pivot_3
  · exact lt_trans (by norm_num) pivot_4

theorem gram : ∀ i j : Fin 5, Z i j =
    ∑ k, lowerUnit entries k i * D k * lowerUnit entries k j := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact entry_0_0
  · exact entry_0_1
  · exact entry_0_2
  · exact entry_0_3
  · exact entry_0_4
  · exact entry_1_0
  · exact entry_1_1
  · exact entry_1_2
  · exact entry_1_3
  · exact entry_1_4
  · exact entry_2_0
  · exact entry_2_1
  · exact entry_2_2
  · exact entry_2_3
  · exact entry_2_4
  · exact entry_3_0
  · exact entry_3_1
  · exact entry_3_2
  · exact entry_3_3
  · exact entry_3_4
  · exact entry_4_0
  · exact entry_4_1
  · exact entry_4_2
  · exact entry_4_3
  · exact entry_4_4

theorem positiveDefinite : (realMatrix Z).PosDef :=
  posDef_of_rational_gram Z entries D pivots_pos gram

end MUB6.Certificate.GramData.Block0

end OAI
