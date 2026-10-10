import OAI.Geometry.HeilbronnTriangle.LatticeBox

namespace OAI


namespace Problem355.DeterminantFibers

open scoped Matrix
open LatticeBox

@[simp] theorem realVector_sub {d : ℕ} (u v : Fin d → ℤ) :
    realVector (u - v) = realVector u - realVector v := by
  ext i
  simp [realVector]

theorem exists_translate_into_plane {d : ℕ} (S : Finset (Fin d → ℤ))
    (y : Fin d → ℤ) (c : ℤ) (R : ℝ)
    (hS : S.Nonempty)
    (hdot : ∀ u ∈ S, u ⬝ᵥ y = c)
    (hnorm : ∀ u ∈ S, ‖realVector u‖ ≤ R) :
    ∃ T : Finset (Fin d → ℤ), ∃ center : EuclideanSpace ℝ (Fin d),
      T.card = S.card ∧
      ∀ z ∈ T, z ⬝ᵥ y = 0 ∧ ‖realVector z - center‖ ≤ R := by
  classical
  obtain ⟨u₀, hu₀⟩ := hS
  refine ⟨S.image (fun u => u - u₀), -realVector u₀, ?_, ?_⟩
  · exact Finset.card_image_of_injective _ (fun u v h => sub_left_injective h)
  · intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    constructor
    · rw [sub_dotProduct, hdot u hu, hdot u₀ hu₀, sub_self]
    · simpa using hnorm u hu

theorem card_dot_fiber_le {d : ℕ} (S : Finset (Fin d → ℤ))
    (y : Fin d → ℤ) (c : ℤ) (R B : ℝ) (hB : 0 ≤ B)
    (hdot : ∀ u ∈ S, u ⬝ᵥ y = c)
    (hnorm : ∀ u ∈ S, ‖realVector u‖ ≤ R)
    (hplane : ∀ T : Finset (Fin d → ℤ), ∀ center : EuclideanSpace ℝ (Fin d),
      (∀ z ∈ T, z ⬝ᵥ y = 0 ∧ ‖realVector z - center‖ ≤ R) →
      (T.card : ℝ) ≤ B) :
    (S.card : ℝ) ≤ B := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · simpa [hS] using hB
  · obtain ⟨T, center, hcard, hT⟩ := exists_translate_into_plane S y c R hS hdot hnorm
    simpa only [hcard] using hplane T center hT

theorem dot_eq_of_fixed_triple_product
    (u u₀ v w y : Fin 3 → ℤ) (a : ℤ) (ha : a ≠ 0)
    (hcross : v ⨯₃ w = a • y)
    (hdet : u ⬝ᵥ (v ⨯₃ w) = u₀ ⬝ᵥ (v ⨯₃ w)) :
    u ⬝ᵥ y = u₀ ⬝ᵥ y := by
  rw [hcross, dotProduct_smul, dotProduct_smul] at hdet
  exact mul_left_cancel₀ ha hdet

theorem card_determinant_fiber_le
    (S : Finset (Fin 3 → ℤ)) (v w y : Fin 3 → ℤ) (a t : ℤ)
    (ha : a ≠ 0) (hcross : v ⨯₃ w = a • y)
    (R B : ℝ) (hB : 0 ≤ B)
    (hdet : ∀ u ∈ S, u ⬝ᵥ (v ⨯₃ w) = t)
    (hnorm : ∀ u ∈ S, ‖realVector u‖ ≤ R)
    (hplane : ∀ T : Finset (Fin 3 → ℤ), ∀ center : EuclideanSpace ℝ (Fin 3),
      (∀ z ∈ T, z ⬝ᵥ y = 0 ∧ ‖realVector z - center‖ ≤ R) →
      (T.card : ℝ) ≤ B) :
    (S.card : ℝ) ≤ B := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · simpa [hS] using hB
  · obtain ⟨u₀, hu₀⟩ := hS
    apply card_dot_fiber_le S y (u₀ ⬝ᵥ y) R B hB _ hnorm hplane
    intro u hu
    exact dot_eq_of_fixed_triple_product u u₀ v w y a ha hcross
      ((hdet u hu).trans (hdet u₀ hu₀).symm)

end Problem355.DeterminantFibers

end OAI
