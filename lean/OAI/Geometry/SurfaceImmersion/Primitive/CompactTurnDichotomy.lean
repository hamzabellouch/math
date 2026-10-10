import OAI.Geometry.SurfaceImmersion.Primitive.LongitudinalCrossing

namespace OAI

/-! Compactness converts the two limiting mechanisms at turns and away from
turns into a single small-scale alternative. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.GeometryPreservation

lemma compact_away_from_turns {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {A N₀ : X → ℝ}
    (hA : Continuous A) (hN₀ : Continuous N₀) (H : ℝ)
    (hturn : ∀ x ∈ K, A x = 0 → H+2 < |N₀ x|) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, |N₀ x| ≤ H+1 → δ ≤ |A x| := by
  let C := K ∩ {x | |N₀ x| ≤ H+1}
  have hC : IsCompact C := hK.inter_right (isClosed_le hN₀.abs continuous_const)
  by_cases hne : C.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hC.exists_isMinOn hne hA.abs.continuousOn
    have hp : 0 < |A x| := by
      apply abs_pos.mpr
      intro hz
      have hh := hturn x hx.1 hz
      have hxN : |N₀ x| ≤ H+1 := hx.2
      linarith
    exact ⟨|A x|,hp,fun y hy hn => hmin ⟨hy,hn⟩⟩
  · refine ⟨1,by norm_num,?_⟩
    intro x hx hn
    exact False.elim (hne ⟨x,hx,hn⟩)

theorem small_scale_turn_or_longitudinal {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {A N₀ : X → ℝ}
    (hA : Continuous A) (hN₀ : Continuous N₀) (H J : ℝ) (hJ : 0 ≤ J)
    (hturn : ∀ x ∈ K, A x = 0 → H+2 < |N₀ x|) :
    ∃ η : ℝ, 0 < η ∧ ∀ z : ℝ, 0 < z → z < η →
      ∀ x ∈ K, ∀ N L : ℝ, |N-N₀ x| < 1 → |z*L-A x| < η →
        H < |N| ∨ J < |L| := by
  obtain ⟨δ,hδ,haway⟩ := compact_away_from_turns hK hA hN₀ H hturn
  let η := δ/(2*(J+1))
  have hη : 0 < η := div_pos hδ (by positivity)
  have heq : η*(J+1) = δ/2 := by
    dsimp [η]
    field_simp
  refine ⟨η,hη,?_⟩
  intro z hz hzη x hx N L hN hL
  by_cases hn : H < |N|
  · exact Or.inl hn
  · right
    by_contra hl
    have hn' : |N| ≤ H := le_of_not_gt hn
    have hl' : |L| ≤ J := le_of_not_gt hl
    have hn₀ : |N₀ x| ≤ H+1 := by
      have hh := abs_sub_le (N₀ x) N 0
      simp only [sub_zero,abs_sub_comm] at hh
      linarith
    have ha := haway x hx hn₀
    have hb : |A x| ≤ |z*L-A x|+z*|L| := by
      have hh := abs_sub_le (A x) (z*L) 0
      simpa only [sub_zero,abs_sub_comm,abs_mul,abs_of_pos hz] using hh
    have hmul := mul_le_mul_of_nonneg_left hl' hz.le
    have hmul' := mul_le_mul_of_nonneg_right hzη.le hJ
    nlinarith

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
