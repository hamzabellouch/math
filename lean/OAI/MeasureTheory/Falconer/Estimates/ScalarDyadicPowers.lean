import OAI.MeasureTheory.Falconer.Estimates.ScalarWeakScaleParameters
import OAI.MeasureTheory.Falconer.Incidence.ScalarWeakBlockProjection

namespace OAI

/-! Exact conversion between the dyadic scale and the exponential budgets
 used in the scalar projection proof. -/
namespace Falconer

 theorem scalar_dyadic_power (N : ℕ) (κ : ℝ) :
    ((1/2:ℝ)^N)^κ = Real.exp (-κ*(N:ℝ)*Real.log 2) := by
  have hh : Real.log (1/2:ℝ) = -Real.log 2 := by
    rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [Real.rpow_def_of_pos (by positivity),Real.log_pow,hh]
  congr 1
  ring

 theorem scalar_exp_dyadic_product (N : ℕ) (a κ : ℝ) :
    Real.exp (a*(N:ℝ)*Real.log 2)*((1/2:ℝ)^N)^κ =
      Real.exp ((a-κ)*(N:ℝ)*Real.log 2) := by
  rw [scalar_dyadic_power,← Real.exp_add]
  congr 1
  ring

namespace Regularization

 theorem scalar_leaf_cells_card {N : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) :
    (scalarCells ((1/2:ℝ)^N) (L.image scalarPathCenter)).card = L.card := by
  have hsep : ∀ x ∈ L.image scalarPathCenter, ∀ y ∈ L.image scalarPathCenter,
      x ≠ y → (1/2:ℝ)^N ≤ |x-y| := by
    intro x hx y hy hxy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
    exact scalarPathCenter_separated ((mem_cubePaths 1 N p).mp (hL hp))
      ((mem_cubePaths 1 N q).mp (hL hq)) (fun h => hxy (congrArg scalarPathCenter h))
  exact (Finset.card_image_of_injOn (scalarCells_injective (by positivity) hsep)).trans
    (scalar_leaf_center_card L hL)

end Regularization
end Falconer

end OAI
