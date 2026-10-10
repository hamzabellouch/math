import OAI.Algebra.DepthFive.PathOccupationGroups
import OAI.Algebra.DepthFive.BidegreeOccupationSum

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable (side : σ → Bool) (a b : ℕ)
variable
  [Fintype {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a, b)}]
  [Fintype {d : {i // side i = true} → ℕ // ∑ i, d i = a}]
  [Fintype {d : {i // ¬side i = true} → ℕ // ∑ i, d i = b}]

/-- Exact source-index sum for a squarefree Fock path, expressed over the
independent derivative and multiplication occupation spaces. -/
theorem sum_pathAmplitude_sq_split (p : List σ) (hp : p.Nodup) :
    (∑ d : {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a, b)},
      ((p.map (occupationAmplitude side d.val)).prod) ^ 2) =
    (∑ d : {d : {i // side i = true} → ℕ // ∑ i, d i = a},
      ∏ i ∈ selectedPathCoordinates side p true, (d.val i : ℝ)) *
    (∑ d : {d : {i // ¬side i = true} → ℕ // ∑ i, d i = b},
      ∏ i ∈ complementaryPathCoordinates side p, ((d.val i : ℝ) + 1)) := by
  simp_rw [pathAmplitude_sq_split_complement side p hp]
  exact sum_bidegree_occupation_products side a b _ _

/-- The normalized squared amplitude is the product of the two uniform
squarefree occupation means, including every inactive ambient coordinate. -/
theorem mean_pathAmplitude_sq_split (p : List σ) (hp : p.Nodup) :
    (∑ d : {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a, b)},
      ((p.map (occupationAmplitude side d.val)).prod) ^ 2) /
      Fintype.card {d : σ →₀ ℕ // Finsupp.weight (bidegreeWeight side) d = (a, b)} =
    ((∑ d : {d : {i // side i = true} → ℕ // ∑ i, d i = a},
      ∏ i ∈ selectedPathCoordinates side p true, (d.val i : ℝ)) /
      Fintype.card {d : {i // side i = true} → ℕ // ∑ i, d i = a}) *
    ((∑ d : {d : {i // ¬side i = true} → ℕ // ∑ i, d i = b},
      ∏ i ∈ complementaryPathCoordinates side p, ((d.val i : ℝ) + 1)) /
      Fintype.card {d : {i // ¬side i = true} → ℕ // ∑ i, d i = b}) := by
  simp_rw [pathAmplitude_sq_split_complement side p hp]
  exact mean_bidegree_occupation_products side a b _ _

end Problem335

end

end OAI
