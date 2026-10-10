import OAI.MeasureTheory.Falconer.Estimates.PointSamples
import OAI.MeasureTheory.Falconer.Estimates.Packing

namespace OAI

/-! A fixed finite loss makes the actual points four times more separated.
This pays for the anisotropic change of slope chart. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem quadruple_separated_subset {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Space 2)) (hS : S.Nonempty) (hsep : FiniteSeparatedAt δ S) :
    ∃ P ⊆ S, P.Nonempty ∧ FiniteSeparatedAt (4*δ) P ∧ (S.card:ℝ) ≤ 81*(P.card:ℝ) := by
  obtain ⟨P,hPS,hPsep,hcover⟩ := exists_separated_cover S (show 0 ≤ 4*δ by positivity)
  have hP : P.Nonempty := by
    obtain ⟨x,hx⟩ := hS
    obtain ⟨y,hy,_⟩ := hcover x hx
    exact ⟨y,hy⟩
  refine ⟨P,hPS,hP,hPsep,?_⟩
  have hc : ∀ y ∈ P, ((S.filter fun x => dist x y ≤ 4*δ).card:ℝ) ≤ 81 := by
    intro y _
    have hh := separated_ball_card (S.filter fun x => dist x y ≤ 4*δ) y hδ
      (show 0 ≤ 4*δ by positivity)
      (fun x hx z hz hne => hsep x (Finset.mem_filter.mp hx).1 z (Finset.mem_filter.mp hz).1 hne)
      (fun x hx => (Finset.mem_filter.mp hx).2)
    have he : 2*(4*δ)/δ+1 = (9:ℝ) := by field_simp; ring
    rw [he] at hh
    norm_num only [Nat.cast_ofNat,show (9:ℝ)^2 = 81 by norm_num] at hh
    exact hh
  simpa only [mul_comm] using selected_points_card_lower S id P hcover hc

end Falconer

end OAI
