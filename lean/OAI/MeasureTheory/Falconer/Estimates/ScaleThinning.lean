import OAI.MeasureTheory.Falconer.Estimates.SeparatedThinning
import OAI.MeasureTheory.Falconer.Incidence.FiniteBallBounds

namespace OAI

/-! A prescribed coarser separation scale costs only the planar packing
factor. This is the fixed loss used before assigning original points to leaves. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem planar_separated_subset_at {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (S : Finset (Space 2)) (hS : S.Nonempty) (hsep : FiniteSeparatedAt δ S) :
    ∃ P ⊆ S, P.Nonempty ∧ FiniteSeparatedAt ρ P ∧
      (S.card:ℝ) ≤ (2*ρ/δ+1)^2*(P.card:ℝ) := by
  obtain ⟨P,hPS,hPsep,hcover⟩ := exists_separated_cover S hρ
  have hP : P.Nonempty := by
    obtain ⟨x,hx⟩ := hS
    obtain ⟨y,hy,_⟩ := hcover x hx
    exact ⟨y,hy⟩
  refine ⟨P,hPS,hP,hPsep,?_⟩
  have hc : ∀ y ∈ P, ((S.filter fun x => dist x y ≤ ρ).card:ℝ) ≤ (2*ρ/δ+1)^2 := by
    intro y _
    exact separated_ball_card (S.filter fun x => dist x y ≤ ρ) y hδ hρ
      (fun x hx z hz hne => hsep x (Finset.mem_filter.mp hx).1 z (Finset.mem_filter.mp hz).1 hne)
      (fun x hx => (Finset.mem_filter.mp hx).2)
  simpa only [mul_comm] using selected_points_card_lower S id P hcover hc

theorem thin_pencils_to_scale {δ ρ s K a b : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (hK : 1 ≤ K) (ha : 0 < a) (P : Finset (Space 2))
    (V : Space 2 → Finset (Space 2))
    (hV : ∀ x ∈ P, a ≤ ((V x).card:ℝ) ∧ ((V x).card:ℝ) ≤ b ∧
      FiniteSeparatedAt δ (V x) ∧ NormalizedFiniteBallBound δ s K (V x)) :
    ∃ U : Space 2 → Finset (Space 2), ∀ x ∈ P,
      U x ⊆ V x ∧ a/(2*ρ/δ+1)^2 ≤ ((U x).card:ℝ) ∧ ((U x).card:ℝ) ≤ b ∧
      FiniteSeparatedAt ρ (U x) ∧
      NormalizedFiniteBallBound δ s (K*(2*ρ/δ+1)^2) (U x) := by
  have hF : 0 < (2*ρ/δ+1)^2 := by positivity
  have hex : ∀ x, ∃ T : Finset (Space 2), x ∈ P →
      T ⊆ V x ∧ T.Nonempty ∧ FiniteSeparatedAt ρ T ∧
      ((V x).card:ℝ) ≤ (2*ρ/δ+1)^2*(T.card:ℝ) := by
    intro x
    by_cases hx : x ∈ P
    · have hv := hV x hx
      have hn : (V x).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (ha.trans_le hv.1))
      obtain ⟨T,hT⟩ := planar_separated_subset_at hδ hρ (V x) hn hv.2.2.1
      exact ⟨T,fun _ => hT⟩
    · exact ⟨∅,fun h => False.elim (hx h)⟩
  choose U hU using hex
  refine ⟨U,?_⟩
  intro x hx
  obtain ⟨hUV,_,hsep,hsize⟩ := hU x hx
  have hv := hV x hx
  refine ⟨hUV,(div_le_iff₀ hF).2 (by simpa only [mul_comm] using hv.1.trans hsize),
    (Nat.cast_le.mpr (Finset.card_le_card hUV)).trans hv.2.1,hsep,?_⟩
  exact normalized_finite_ball_bound_subset hδ.le (zero_le_one.trans hK) hUV hsize hv.2.2.2

end Falconer

end OAI
