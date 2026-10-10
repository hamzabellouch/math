import OAI.Analysis.KadisonKastler.PublishedNestDistance
import OAI.Analysis.KadisonKastler.DecomposableNorm

namespace OAI

/-! # Actual measurable multipliers from a nest approximation

The published distance formula first supplies a nest-preserving operator.
The proved invariant mean retains that property and its error bound.
Published diagonal decomposition then gives an actual measurable field,
and uniqueness of fields transfers the approximation estimate pointwise
almost everywhere. No analytic extension theorem is assumed here.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
  {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

theorem exists_nest_multiplier_approximation
    (hNest : PublishedRealNestDistance.{u})
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (m : ScalarInvariantMean G)
    (P : ℝ → RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hP : ∀ a, IsStarProjection (P a))
    (hmono : ∀ a b, a ≤ b → P a * P b = P a)
    (U : G →* unitary (RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (hchar : ∀ a : ℝ, ∃ g, (U g : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      regularCharacterUnitary (H := H) a)
    (hperm : ∀ g a, ∃ b, P a = unitaryConj (U g) (P b))
    (F : ℝ → H →L[ℂ] H)
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hF : RepresentsOperatorField volume F T)
    (hfixed : ∀ g, unitaryConj (U g) T = T)
    {δ : ℝ} (hδ : 0 < δ) (hdefect : ∀ a, ‖(1 - P a) * T * P a‖ ≤ δ) :
    ∃ (B : ℝ → H →L[ℂ] H) (S : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H),
      PreservesProjectionNest P S ∧
      (∀ x, AEStronglyMeasurable (fun t => B t x) volume) ∧
      RepresentsOperatorField volume B S ∧
      (∀ᵐ t, ‖B t‖ ≤ ‖T‖ + 2 * δ) ∧
      (∀ᵐ t, ‖B t - F t‖ ≤ 2 * δ) := by
  obtain ⟨S, hS, hSfixed, hST⟩ :=
    exists_invariant_nest_approximant hNest m P hP hmono U hperm T hfixed hδ hdefect
  have hcomm (A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (hA : ∀ g, unitaryConj (U g) A = A) (a : ℝ) :
      Commute A (regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
    obtain ⟨g, hg⟩ := hchar a
    rw [← hg]
    exact ((commute_unitary_iff_star_right_conjugate (U g).property).mpr (hA g)).symm
  obtain ⟨B, hBm, hBn, hBS⟩ := hDiagonal H S (hSpectral H S (hcomm S hSfixed))
  have hdiff := hBS.ae_norm_sub_le_of_diagonal hSpectral hDiagonal hF
    (hcomm S hSfixed) (hcomm T hfixed)
  refine ⟨B, S, hS, hBm, hBS, ?_, ?_⟩
  · filter_upwards [hBn] with t ht
    exact ht.trans ((norm_le_norm_sub_add S T).trans (by linarith))
  · filter_upwards [hdiff] with t ht
    exact ht.trans hST.le

end

end KadisonKastler

end OAI
