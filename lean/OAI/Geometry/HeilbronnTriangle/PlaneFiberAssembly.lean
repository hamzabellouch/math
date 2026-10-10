import OAI.Geometry.HeilbronnTriangle.NormalFiberCount
import OAI.Geometry.HeilbronnTriangle.DeterminantFibers

namespace OAI


namespace Problem355.PlaneFiberAssembly

open scoped Matrix
open LatticeBox

abbrev Vec := Fin 3 → ℤ
abbrev Triple := Vec × Vec × Vec

theorem triple_count_of_plane_counts
    (S : Finset Triple) (y : Vec) (t : ℤ) (R₁ R₂ R₃ B₁ B₂ B₃ : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hdet : ∀ x ∈ S, x.1 ⬝ᵥ (x.2.1 ⨯₃ x.2.2) = t)
    (hcross : ∀ x ∈ S, ∃ a : ℤ, a ≠ 0 ∧ x.2.1 ⨯₃ x.2.2 = a • y)
    (hplane : ∀ x ∈ S, x.2.1 ⬝ᵥ y = 0 ∧ x.2.2 ⬝ᵥ y = 0)
    (hnorm : ∀ x ∈ S, ‖realVector x.1‖ ≤ R₁ ∧
      ‖realVector x.2.1‖ ≤ R₂ ∧ ‖realVector x.2.2‖ ≤ R₃)
    (hcount₁ : ∀ T : Finset Vec, ∀ center : EuclideanSpace ℝ (Fin 3),
      (∀ z ∈ T, z ⬝ᵥ y = 0 ∧ ‖realVector z - center‖ ≤ R₁) →
      (T.card : ℝ) ≤ B₁)
    (hcount₂ : ∀ T : Finset Vec,
      (∀ z ∈ T, z ⬝ᵥ y = 0 ∧ ‖realVector z‖ ≤ R₂) → (T.card : ℝ) ≤ B₂)
    (hcount₃ : ∀ T : Finset Vec,
      (∀ z ∈ T, z ⬝ᵥ y = 0 ∧ ‖realVector z‖ ≤ R₃) → (T.card : ℝ) ≤ B₃) :
    (S.card : ℝ) ≤ B₁ * B₂ * B₃ := by
  classical
  let Y := S.image (fun x => x.2.1)
  let Z := S.image (fun x => x.2.2)
  have hY : (Y.card : ℝ) ≤ B₂ := by
    apply hcount₂
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨(hplane x hx).1, (hnorm x hx).2.1⟩
  have hZ : (Z.card : ℝ) ≤ B₃ := by
    apply hcount₃
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨(hplane x hx).2, (hnorm x hx).2.2⟩
  apply NormalFiberCount.card_triples_le_mul S Y Z B₁ B₂ B₃ hB₁ hB₂ hY hZ
  · intro x hx
    exact ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
  · intro v hv w hw
    let F := S.filter (fun x => x.2 = (v, w))
    change (F.card : ℝ) ≤ B₁
    rcases F.eq_empty_or_nonempty with hF | hF
    · simpa [hF] using hB₁
    · obtain ⟨x₀, hx₀⟩ := hF
      have hx₀S := (Finset.mem_filter.mp hx₀).1
      have htail₀ := (Finset.mem_filter.mp hx₀).2
      obtain ⟨a, ha, haxy⟩ := hcross x₀ hx₀S
      have haxy' : v ⨯₃ w = a • y := by
        simpa only [htail₀] using haxy
      let U := F.image Prod.fst
      have hcard : U.card = F.card := by
        apply Finset.card_image_of_injOn
        intro x hx x' hx' hfirst
        apply Prod.ext hfirst
        exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hx').2.symm
      have hU : (U.card : ℝ) ≤ B₁ := by
        apply DeterminantFibers.card_determinant_fiber_le U v w y a t ha haxy'
          R₁ B₁ hB₁ _ _ hcount₁
        · intro u hu
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
          have hd := hdet x (Finset.mem_filter.mp hx).1
          simpa only [(Finset.mem_filter.mp hx).2] using hd
        · intro u hu
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
          exact (hnorm x (Finset.mem_filter.mp hx).1).1
      simpa only [hcard] using hU

end Problem355.PlaneFiberAssembly

end OAI
