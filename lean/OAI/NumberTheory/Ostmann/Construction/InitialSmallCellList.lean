import OAI.NumberTheory.Ostmann.Construction.SelectedInitialTotal

namespace OAI

/-! # The three top labels and two labels of each compensation type -/
namespace Ostmann

def initialSmallCellList (top : ℕ) (centers : List ℕ) : List ℕ :=
  List.replicate 3 top ++ centers.flatMap (fun j => [j, j])

theorem initialSmallCellList_length (top : ℕ) (centers : List ℕ) :
    (initialSmallCellList top centers).length = 3 + 2 * centers.length := by
  unfold initialSmallCellList
  induction centers with
  | nil => simp
  | cons j js ih => simp_all; omega

theorem initialSmallCellList_sum (top : ℕ) (centers : List ℕ) :
    ((initialSmallCellList top centers).map (fun j : ℕ => (j : ℝ))).sum =
      3 * (top : ℝ) + 2 * (centers.map (fun j : ℕ => (j : ℝ))).sum := by
  unfold initialSmallCellList
  induction centers with
  | nil => simp; ring
  | cons j js ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil] at ih ⊢
    linarith only [ih]

end Ostmann

end OAI
