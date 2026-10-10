import OAI.Analysis.KadisonKastler.PublishedRegularDiagonal

namespace OAI

/-! # Norm bounds for concrete decomposable fields

Uniqueness on finite-measure indicator tests transfers the norm bound
in the published diagonal decomposition to any representing field.
Applying this to a difference avoids a measurable nearest-point choice.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem RepresentsOperatorField.ae_norm_le_of_diagonal
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T)
    (hT : ∀ (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C),
      Commute T (regularScalarMultiplier (H := H) φ hφ C hC)) :
    ∀ᵐ t, ‖F t‖ ≤ ‖T‖ := by
  obtain ⟨G, _, hGn, hG⟩ := hDiagonal H T hT
  have he := hF.field_eq_ae_real hG
  filter_upwards [he, hGn] with t ht hn
  simpa only [ht] using hn

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem RepresentsOperatorField.sub_real
    {F G : ℝ → H →L[ℂ] H}
    {T S : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (hG : RepresentsOperatorField volume G S) :
    RepresentsOperatorField volume (fun t => F t - G t) (T - S) := by
  intro f
  filter_upwards [hF f, hG f, Lp.coeFn_sub (T f) (S f)] with t ht hs hsub
  change ((T f - S f) t) = (F t - G t) (f t)
  rw [hsub]
  simp only [Pi.sub_apply, ht, hs, sub_apply]

/-- The operator-norm distance of two decomposable operators bounds the
essential uniform distance of their representing fields. -/
theorem RepresentsOperatorField.ae_norm_sub_le_of_diagonal
    (hSpectral : PublishedRealSpectralCommutant.{u})
    (hDiagonal : PublishedRealDiagonalDecomposition.{u})
    {F G : ℝ → H →L[ℂ] H}
    {T S : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (hG : RepresentsOperatorField volume G S)
    (hT : ∀ a : ℝ, Commute T (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H))
    (hS : ∀ a : ℝ, Commute S (regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)) :
    ∀ᵐ t, ‖F t - G t‖ ≤ ‖T - S‖ :=
  (hF.sub_real hG).ae_norm_le_of_diagonal hDiagonal
    (hSpectral H (T - S) (fun a => (hT a).sub_left (hS a)))

end

end KadisonKastler

end OAI
