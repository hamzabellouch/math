import OAI.MeasureTheory.Falconer.Estimates.CommonRegularFamily
import OAI.MeasureTheory.Falconer.Geometry.ProjectionCells

namespace OAI

/-! Common regular parameters with large subsets having small projections.
This is the exact finite configuration produced before the projection theorem
in Orponen--Shmerkin, Appendix A.7. No projection estimate is assumed here. -/
namespace Falconer

theorem common_regular_small_projections {α : Type*} (J : Finset α) (hJ : J.Nonempty)
    (A : α → Finset (Space 2)) (direction : α → ℝ) {δ s K m R : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hm : 0 < m) (hR : 0 < R)
    (hsize : ∀ j ∈ J, m ≤ ((A j).card : ℝ))
    (hunion : ((J.biUnion A).card : ℝ) ≤ R*m)
    (hA : ∀ j ∈ J, NormalizedFiniteBallBound δ s K (A j))
    (M : ℕ) (hproj : ∀ j ∈ J, (projectionCells δ (direction j) (A j)).card ≤ M) :
    ∃ G ⊆ J.biUnion A, G.Nonempty ∧ m/2 ≤ (G.card : ℝ) ∧
      NormalizedFiniteBallBound δ s (4*R^2*K) G ∧
      ∃ Y ⊆ J, Y.Nonempty ∧ (J.card : ℝ) ≤ 4*R*(Y.card : ℝ) ∧
        ∀ j ∈ Y, m/4 ≤ ((G ∩ A j).card : ℝ) ∧
          (projectionCells δ (direction j) (G ∩ A j)).card ≤ M := by
  obtain ⟨G,hGU,hGcard,hGregular,hGmass⟩ := common_regular_family J hJ A hδ hK hm hR
    hsize hunion hA
  obtain ⟨Y,hYJ,hYcard,hYsize⟩ := popular_family_rows J A G hGU hm hR.le hunion hGmass
  have hG : G.Nonempty := Finset.card_pos.mp (by
    have hh := (half_pos hm).trans_le hGcard
    exact_mod_cast hh)
  have hY : Y.Nonempty := by
    apply Finset.card_pos.mp
    by_contra h
    have hz : Y.card = 0 := Nat.eq_zero_of_not_pos h
    rw [hz,Nat.cast_zero,mul_zero] at hYcard
    have hJpos : 0 < (J.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hJ)
    linarith
  refine ⟨G,hGU,hG,hGcard,hGregular,Y,hYJ,hY,hYcard,?_⟩
  intro j hj
  exact ⟨hYsize j hj,
    (Finset.card_le_card (projectionCells_mono δ (direction j) Finset.inter_subset_right)).trans
      (hproj j (hYJ hj))⟩

end Falconer

end OAI
