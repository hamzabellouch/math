import OAI.NumberTheory.TwoPoint.Halasz.HalaszFinitePhase

namespace OAI

/-! Diagonal pairs in the long variables retain a full copy of the
short-variable energy for each long tuple. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem halasz_energy_diagonal_lower {α β γ : Type*} [Add γ]
    (F : Finset α) (G : Finset β) (f : α → γ) (g : β → γ) :
    F.card * halaszFiberEnergy G g ≤
      halaszFiberEnergy (F×ˢG) (fun x => f x.1+g x.2) := by
  rw [halasz_fiber_energy_rows,halasz_fiber_energy_rows,sum_product,mul_sum]
  have hl (a : α) (ha : a∈F) (b : β) :
      (G.filter (fun y => g y=g b)).card ≤
        ((F×ˢG).filter (fun y => f y.1+g y.2=f a+g b)).card := by
    calc
      _ = ({a}×ˢ(G.filter (fun y => g y=g b))).card := by simp
      _ ≤ _ := by
        apply card_le_card
        intro y hy
        obtain ⟨hy1,hy2⟩ := mem_product.mp hy
        have hy1' : y.1=a := mem_singleton.mp hy1
        obtain ⟨hyG,hyg⟩ := mem_filter.mp hy2
        exact mem_filter.mpr ⟨mem_product.mpr ⟨hy1' ▸ ha,hyG⟩,by rw [hy1',hyg]⟩
  calc
    _ = ∑ _a∈F, ∑ b∈G, (G.filter (fun y => g y=g b)).card := by
      rw [← mul_sum]
      simp
    _ ≤ _ := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b _
      exact hl a ha b

end TwoPointCorrelations

end OAI
