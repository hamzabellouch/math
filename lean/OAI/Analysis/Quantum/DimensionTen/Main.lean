import OAI.Analysis.Quantum.DimensionTen.ExteriorEvaluation
import OAI.Analysis.Quantum.DimensionTen.FamilyGeometry
import OAI.Analysis.Quantum.DimensionTen.TwentyDirections

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma compositeChoi_veronese (x : Fin 4 → ℂ) :
    star (productVector (veronese x) (veronese x)) ⬝ᵥ
      (compositeChoi *ᵥ productVector (veronese x) (veronese x)) =
      6 * (pencilMap (pure x)).det := by
  rw [compositeChoi_pairing]
  unfold complementaryMap
  rw [exteriorMap_veronese, compound_trace]

lemma pencilMap_det_zero_of_rank {x : Fin 4 → ℂ} (hx : (pencil x).rank < 4) :
    (pencilMap (pure x)).det = 0 := by
  by_contra h
  have hr := Matrix.rank_of_det_ne_zero h
  have he : (pencilMap (pure x)).rank = (pencil x).rank := pencilMap_projector_rank x
  rw [he] at hr
  norm_num at hr
  omega

lemma compositeChoi_kernel_rank {x : Fin 4 → ℂ} (hx : (pencil x).rank < 4) :
    compositeChoi *ᵥ productVector (veronese x) (veronese x) = 0 := by
  apply compositeChoi_posSemidef.dotProduct_mulVec_zero_iff.mp
  rw [compositeChoi_veronese, pencilMap_det_zero_of_rank hx, mul_zero]

lemma pencilMap_ezero : pencilMap (pure (![1,0,0,0] : Fin 4 → ℂ)) =
    (36 : ℂ) • (1 : Mat 4) := by
  exact pencilMap_ezero_fast

lemma compositeChoi_ne : compositeChoi ≠ 0 := by
  intro hh
  have h := compositeChoi_veronese (![1,0,0,0] : Fin 4 → ℂ)
  rw [hh, Matrix.zero_mulVec, dotProduct_zero, pencilMap_ezero] at h
  norm_num [Matrix.det_smul] at h

lemma veronese_family_general_position (u : Fin 10 → ℂ) (hu : u ≠ 0) :
    (Finset.univ.filter (fun k : Fin 20 =>
      star u ⬝ᵥ veronese (chart (Border.points k)) = 0)).card ≤ 9 := by
  simp only [veronese_dot]
  exact Border.quadratic_zero_bound _ (veroneseCoeffs_ne hu)

lemma compositeChoi_productfree :
    ∀ u v : Fin 10 → ℂ, ∀ w : Fin 10 × Fin 10 → ℂ,
      compositeChoi *ᵥ w = productVector u v → u = 0 ∨ v = 0 := by
  exact productfree_of_kernel_family _ compositeChoi_posSemidef.isHermitian
    (fun k => veronese (chart (Border.points k))) veronese_family_general_position
    (fun k => compositeChoi_kernel_rank (Border.rank_points k))

lemma compositeChoi_not_separable : ¬ separable compositeChoi := by
  exact nonseparable_of_kernel_family _ compositeChoi_ne
    (fun k => veronese (chart (Border.points k))) veronese_family_general_position
    (fun k => compositeChoi_kernel_rank (Border.rank_points k))


theorem exactDimensionTenPair : ExactDimensionTenPair := by
  refine ⟨phiOne_ppt, phiTwo_ppt, compositeChoi_ne, compositeChoi_productfree, ?_⟩
  intro h
  exact compositeChoi_not_separable (eb_choi_separable _ h (by decide))

end DimensionTen

end
end
namespace DimensionTen

theorem twenty_directions : TwentyDirections := twentyDirections

theorem exact_dimension_ten_pair : ExactDimensionTenPair := exactDimensionTenPair
end DimensionTen


noncomputable section
open scoped Matrix ComplexOrder
open Matrix Complex
namespace DimensionTen





theorem main_pair :
    ∃ Φ₁ Φ₂ : Mat 10 → Mat 10,
      Φ₁ = phiOne ∧ Φ₂ = phiTwo ∧ PPT Φ₁ ∧ PPT Φ₂ ∧
      (let Z := choi (Φ₂ ∘ Φ₁)
       Z ≠ 0 ∧
       (∀ u v : Fin 10 → ℂ, ∀ w : Fin 10 × Fin 10 → ℂ,
         Z *ᵥ w = productVector u v → u = 0 ∨ v = 0) ∧
       ¬ EntanglementBreaking (Φ₂ ∘ Φ₁)) := by
  rcases exactDimensionTenPair with ⟨h₁, h₂, hn, hp, he⟩
  exact ⟨phiOne, phiTwo, rfl, rfl, h₁, h₂, hn, hp, he⟩

end DimensionTen
end

end OAI
