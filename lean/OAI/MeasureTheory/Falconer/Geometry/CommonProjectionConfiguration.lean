import OAI.MeasureTheory.Falconer.Geometry.SeparatedProjectionBases
import OAI.MeasureTheory.Falconer.Incidence.FiniteBallBounds
import OAI.MeasureTheory.Falconer.Geometry.ProjectionCells

namespace OAI

/-! The two bases and every graph slice are selected from the original
common projection family, retaining explicit relative mass and regularity. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem common_projection_configuration {δ t K ρ r : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hr : 0 < r)
    (I : Finset ℝ) (U : Finset (Space 2)) (A : ℝ → Finset (Space 2))
    (hI : I.Nonempty) (hU : U.Nonempty)
    (hsub : ∀ i ∈ I, A i ⊆ U)
    (hsize : ∀ i ∈ I, ρ*(U.card:ℝ) ≤ ((A i).card:ℝ))
    (hball : ∀ z : ℝ, scalarBallMass I z r ≤ (ρ^6/128)*(I.card:ℝ))
    (hUreg : NormalizedFiniteBallBound δ t K U)
    (P : ℕ) (hproj : ∀ i ∈ I, (projectionCells δ i (A i)).card ≤ P) :
    ∃ a ∈ I, ∃ b ∈ I, r < |b-a| ∧ b ≠ a ∧ ∃ J ⊆ I,
      J.Nonempty ∧ (ρ^6/64)*(I.card:ℝ) ≤ (J.card:ℝ) ∧
      let V := A a ∩ A b
      V.Nonempty ∧ V ⊆ U ∧ (U.card:ℝ) ≤ (8/ρ^4)*(V.card:ℝ) ∧
      NormalizedFiniteBallBound δ t (K*(8/ρ^4)) V ∧
      (projectionCells δ a V).card ≤ P ∧ (projectionCells δ b V).card ≤ P ∧
      ∀ j ∈ J, r < |j-a| ∧ r < |j-b| ∧
        (ρ^4/8)*(V.card:ℝ) ≤ ((V ∩ A j).card:ℝ) ∧
        (projectionCells δ j (V ∩ A j)).card ≤ P := by
  classical
  obtain ⟨a,ha,b,hb,hab,hba,J,hJI,hJsize,htriple⟩ :=
    separated_projection_bases I U A hI hU hρ hρ1 hr hsub hsize hball
  have hJ : J.Nonempty := by
    apply Finset.card_pos.mp
    have hp : 0 < (ρ^6/64)*(I.card:ℝ) :=
      mul_pos (by positivity) (Nat.cast_pos.mpr hI.card_pos)
    exact_mod_cast hp.trans_le hJsize
  let V := A a ∩ A b
  have hVU : V ⊆ U := Finset.inter_subset_left.trans (hsub a ha)
  obtain ⟨j,hj⟩ := hJ
  have hVlower : (ρ^4/8)*(U.card:ℝ) ≤ (V.card:ℝ) :=
    (htriple j hj).2.2.trans (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left))
  have hV : V.Nonempty := by
    apply Finset.card_pos.mp
    have hp : 0 < (ρ^4/8)*(U.card:ℝ) :=
      mul_pos (by positivity) (Nat.cast_pos.mpr hU.card_pos)
    exact_mod_cast hp.trans_le hVlower
  have hVUsize : (U.card:ℝ) ≤ (8/ρ^4)*(V.card:ℝ) := by
    have hpos : 0 < ρ^4 := by positivity
    have hh := mul_le_mul_of_nonneg_left hVlower (show 0 ≤ 8/ρ^4 by positivity)
    have he : (8/ρ^4)*((ρ^4/8)*(U.card:ℝ)) = (U.card:ℝ) := by field_simp
    rwa [he] at hh
  refine ⟨a,ha,b,hb,hab,hba,J,hJI,⟨j,hj⟩,hJsize,hV,hVU,hVUsize,
    normalized_finite_ball_bound_subset hδ hK hVU hVUsize hUreg,?_,?_,?_⟩
  · exact (Finset.card_le_card (projectionCells_mono δ a Finset.inter_subset_left)).trans (hproj a ha)
  · exact (Finset.card_le_card (projectionCells_mono δ b Finset.inter_subset_right)).trans (hproj b hb)
  · intro j hj
    obtain ⟨hja,hjb,hcard⟩ := htriple j hj
    refine ⟨hja,hjb,?_,?_⟩
    · exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Finset.card_le_card hVU))
        (show 0 ≤ ρ^4/8 by positivity)).trans hcard
    · exact (Finset.card_le_card (projectionCells_mono δ j Finset.inter_subset_right)).trans (hproj j (hJI hj))

end Falconer

end OAI
