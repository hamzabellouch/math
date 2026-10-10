import OAI.Analysis.KadisonKastler.NestMultiplierApproximation
import OAI.Analysis.KadisonKastler.AbelianInvariantMean

namespace OAI

/-! # Real character averaging of a bounded multiplier

The real group is made discrete only for its invariant mean. Its unitary
representation is the actual character multiplication on L²(real,H).
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularFieldOperator_commutes_character
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun t => F t x) volume)
    (C : ℝ) (hC : ∀ᵐ t, ‖F t‖ ≤ C) (a : ℝ) :
    Commute (regularFieldOperator volume F hF C hC)
      (regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  change _ * _ = _ * _
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularFieldOperator_represents volume F hF C hC
      ((regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularCharacterUnitary_apply_ae a f,
    regularCharacterUnitary_apply_ae a (regularFieldOperator volume F hF C hC f),
    regularFieldOperator_represents volume F hF C hC f] with t h₁ h₂ h₃ h₄
  change (regularFieldOperator volume F hF C hC
      ((regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) t =
    ((regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularFieldOperator volume F hF C hC f)) t
  rw [h₁, h₂, h₃, h₄, map_smul]

/-- All mean and character-representation data are constructed here.
The only approximation hypotheses are the actual nest defect and the
published nest and diagonal decomposition theorems. -/
theorem exists_real_nest_multiplier
    [TopologicalSpace.SeparableSpace H]
    (hNest : PublishedRealNestDistance.{u})
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    (P : ℝ → RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hP : ∀ a, IsStarProjection (P a))
    (hmono : ∀ a b, a ≤ b → P a * P b = P a)
    (hperm : ∀ a b : ℝ, ∃ c, P a = unitaryConj (regularCharacterUnitary b) (P c))
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun t => F t x) volume)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ t, ‖F t‖ ≤ C)
    {δ : ℝ} (hδ : 0 < δ)
    (hdefect : ∀ a, ‖(1 - P a) * regularFieldOperator volume F hF C hC * P a‖ ≤ δ) :
    ∃ (B : ℝ → H →L[ℂ] H) (S : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H),
      PreservesProjectionNest P S ∧
      (∀ x, AEStronglyMeasurable (fun t => B t x) volume) ∧
      RepresentsOperatorField volume B S ∧
      (∀ᵐ t, ‖B t‖ ≤ C + 2 * δ) ∧
      (∀ᵐ t, ‖B t - F t‖ ≤ 2 * δ) := by
  let : TopologicalSpace (Multiplicative ℝ) := ⊥
  let : DiscreteTopology (Multiplicative ℝ) := ⟨rfl⟩
  let m := abelianScalarInvariantMean (Multiplicative ℝ)
  let T := regularFieldOperator volume F hF C hC
  have hfixed (g : Multiplicative ℝ) : unitaryConj (regularCharacterRepresentation g) T = T :=
    (commute_unitary_iff_star_right_conjugate
      (regularCharacterUnitary (H := H) g.toAdd).property).mp
        (regularFieldOperator_commutes_character F hF C hC g.toAdd).symm
  obtain ⟨B, S, hS, hBm, hBS, hBn, hBF⟩ := exists_nest_multiplier_approximation
    hNest hSpectral hDiagonal m P hP hmono regularCharacterRepresentation
    (fun a => ⟨Multiplicative.ofAdd a, rfl⟩) (fun g a => hperm a g.toAdd)
    F T (regularFieldOperator_represents volume F hF C hC) hfixed hδ hdefect
  refine ⟨B, S, hS, hBm, hBS, ?_, hBF⟩
  filter_upwards [hBn] with t ht
  have hn : ‖T‖ ≤ C := norm_regularFieldOperator_le volume F hF hC0 hC
  exact ht.trans (by linarith)

end

end KadisonKastler

end OAI
