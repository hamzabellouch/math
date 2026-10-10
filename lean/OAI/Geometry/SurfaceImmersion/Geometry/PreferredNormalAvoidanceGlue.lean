import OAI.Geometry.SurfaceImmersion.Geometry.PreferredNormalGluing
import OAI.Geometry.SurfaceImmersion.Primitive.CrossingNormalPath

namespace OAI

/-! Collar gluing retains full-curve antipode avoidance. Only the transition
region requires positive pairings; the exact endpoint fields cover the rest. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4
open VelocityFrame NormalFrame
variable {M κ : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma ne_neg_normalize_of_pairing_pos {w n : Vec} (hp : 0 < w ⬝ᵥ n) :
    n ≠ -normalize w := by
  have hw : w ≠ 0 := nonzero_of_dot_pos hp
  have hs : 0 < normalize w ⬝ᵥ w := normalize_dot_pos (dot_self_pos hw)
  intro he
  rw [he,dotProduct_neg,dotProduct_comm w (normalize w)] at hp
  linarith

theorem preferredNormal_collar_avoidance {F a b : M → Space} {U V : Set M}
    (hU : IsOpen U) (hV : IsOpen V)
    (ha : ContMDiffOn planeModel spaceModel ∞ a U)
    (hb : ContMDiffOn planeModel spaceModel ∞ b V)
    (ha1 : ∀ p ∈ U, ‖a p‖ = 1) (hb1 : ∀ p ∈ V, ‖b p‖ = 1)
    (haN : ∀ p ∈ U, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (a p) = 0)
    (hbN : ∀ p ∈ V, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (b p) = 0)
    (hne : ∀ p ∈ U ∩ V, b p ≠ -a p)
    {χ : M → ℝ} (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hχU : tsupport χ ⊆ U) (hχV : tsupport (fun p => 1-χ p) ⊆ V)
    (hχ01 : ∀ p, χ p ∈ Icc (0 : ℝ) 1)
    (C : κ → Set M) (B : κ → M → Vec)
    (haAvoid : ∀ k p, p ∈ C k → p ∈ U → spaceCoordinates (a p) ≠ -normalize (B k p))
    (hbAvoid : ∀ k p, p ∈ C k → p ∈ V → spaceCoordinates (b p) ≠ -normalize (B k p))
    (hpositive : ∀ k p, p ∈ C k → 0 < χ p → χ p < 1 →
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (a p) ∧
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (b p)) :
    ∃ N : PreferredNormal F,
      (∀ p, χ p = 1 → N.vector p = a p) ∧
      (∀ p, χ p = 0 → N.vector p = b p) ∧
      ∀ k p, p ∈ C k → spaceCoordinates (N.vector p) ≠ -normalize (B k p) := by
  obtain ⟨N,hNa,hNb,hNp⟩ := preferredNormal_collar hU hV ha hb ha1 hb1 haN hbN hne
    hχ hχU hχV hχ01
  refine ⟨N,hNa,hNb,?_⟩
  intro k p hp
  by_cases h0 : χ p = 0
  · rw [hNb p h0]
    apply hbAvoid k p hp
    apply hχV
    apply subset_tsupport
    change 1-χ p ≠ 0
    simp only [h0,sub_zero,ne_eq,one_ne_zero,not_false_eq_true]
  by_cases h1 : χ p = 1
  · rw [hNa p h1]
    exact haAvoid k p hp (hχU (subset_tsupport χ (by change χ p ≠ 0; rw [h1]; exact one_ne_zero)))
  have hpos := hpositive k p hp (lt_of_le_of_ne (hχ01 p).1 (Ne.symm h0))
    (lt_of_le_of_ne (hχ01 p).2 h1)
  have hglobal := hNp p (spaceCoordinates.symm (B k p)) (fun _ => hpos.1) (fun _ => hpos.2)
  apply ne_neg_normalize_of_pairing_pos
  simpa only [← spaceCoordinates_dot,spaceCoordinates.apply_symm_apply] using hglobal

end ClosedSurfaceR4

end

end OAI
