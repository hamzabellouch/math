import OAI.GroupTheory.Thompson.StandardCharacterization
import OAI.GroupTheory.Thompson.FiniteBoundary
import OAI.GroupTheory.Thompson.AnalyticConstruction
import OAI.GroupTheory.Thompson.MeanToFolner

namespace OAI

noncomputable section

open scoped symmDiff

namespace ThompsonNonamenability

local instance : DecidableEq F := Classical.decEq F

theorem thompson_F_boundary_with_exact_constant :
    ∃ (D : ℕ) (S : Finset F),
      2 ≤ D ∧
      4 * Analytic.displacementLipschitzConstant ^ 2 / (1 / 2 : ℝ) ^ 2 <
        (D : ℝ) ∧
      S.Nonempty ∧
      0 < boundaryConstant Analytic.displacementLipschitzConstant (1 / 2) D ∧
      ∀ A : Finset F, A.Nonempty →
        ∃ h ∈ S,
          boundaryConstant Analytic.displacementLipschitzConstant (1 / 2) D ≤
            boundaryRatio A h := by
  obtain ⟨D, hD, hlarge⟩ :=
    exists_branching_parameter Analytic.displacementLipschitzConstant (1 / 2)
  obtain ⟨S, hS, hb, hboundary⟩ :=
    exists_fixed_boundary Analytic.displacementMap
      Analytic.displacementLipschitzConstant (1 / 2)
      Analytic.displacementLipschitzConstant_pos (by norm_num)
      Analytic.displacementMap_lipschitz Analytic.displacementMap_displacement
      D hD hlarge
  exact ⟨D, S, hD, hlarge, hS, hb, hboundary⟩

/-- The displayed formula has no additional normalization or hidden factor. -/
theorem thompson_F_boundary_constant_formula (D : ℕ) :
    boundaryConstant Analytic.displacementLipschitzConstant (1 / 2) D =
      ((1 / 2 : ℝ) ^ 2 / Analytic.displacementLipschitzConstant ^ 2 -
        4 / (D : ℝ)) / (4 * (1 - 1 / (D : ℝ))) := rfl

/-- A fixed finite subset of the genuine PL group uniformly expands every
nonempty finite subset, in the unnormalized symmetric-difference form. -/
theorem thompson_F_uniform_boundary :
    ∃ (S : Finset F) (b : ℝ), S.Nonempty ∧ 0 < b ∧
      ∀ A : Finset F, A.Nonempty →
        ∃ h ∈ S, b * (A.card : ℝ) ≤ ((leftTranslate h A ∆ A).card : ℝ) := by
  obtain ⟨D, S, _hD, _hlarge, hS, hb, hboundary⟩ :=
    thompson_F_boundary_with_exact_constant
  refine ⟨S, boundaryConstant Analytic.displacementLipschitzConstant (1 / 2) D,
    hS, hb, ?_⟩
  intro A hA
  obtain ⟨h, hh, hratio⟩ := hboundary A hA
  have hcard : (0 : ℝ) < (A.card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  refine ⟨h, hh, ?_⟩
  change boundaryConstant Analytic.displacementLipschitzConstant (1 / 2) D ≤
    ((leftTranslate h A ∆ A).card : ℝ) / (A.card : ℝ) at hratio
  exact (le_div_iff₀ hcard).mp hratio

/-- Standard Thompson F admits no positive normalized left-invariant mean on
all bounded real functions. The carrier is identified with the ordinary
finite-breakpoint dyadic PL homeomorphisms by `F.standardPLEquiv`. -/
theorem thompson_F_not_amenable : ¬ Nonempty (InvariantMean F) := by
  obtain ⟨S, b, _hS, hb, hboundary⟩ := thompson_F_uniform_boundary
  exact not_amenable_of_uniform_boundary S hb hboundary

theorem thompson_F_nonamenable_composition :
    ∃ group : Group F, letI := group;
      (∀ (h g : F) (x : UnitInterval),
        (h * g).val.toHomeomorph x = h.val.toHomeomorph (g.val.toHomeomorph x)) ∧
      ¬ Nonempty (InvariantMean F) := by
  refine ⟨inferInstance, ?_, thompson_F_not_amenable⟩
  intro h g x
  exact F.mul_apply h g x

end ThompsonNonamenability

end

end OAI
