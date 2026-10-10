import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalCardinality
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalFamilyHeight
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalHeightSize
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalLeafFrequency
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalNumerics
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalPivotFrequency
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalPrior

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateSupportRemoval
open SymbolicHistory Filter
open scoped Topology BigOperators

theorem eventually_template_support_removal (C z : ℝ) (d : ℕ) {a c : ℝ}
    (hC : 0 ≤ C) (hz : 0 ≤ z) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ {ι : Type} [Fintype ι] [DecidableEq ι],
    ∀ (k : ℕ) (B₀ V₀ : (j:ℕ) → Template.State k (j+1) → ℤ) (j : ℕ)
      (b : Bool) (s : ℤ) (e : Template.Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
      (D : Finset (Expr ι)), (∀ q ∈ D, q ∈ Template.obstructionExpressions k j b s e t) → ∀ (i : ι)
      (S : Other i → Finset ℤ) (μ : Other i → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
      (H A : ℝ), Real.log 2 ≤ H → 0 ≤ A →
      (∀ u v, v ∈ S u → 0 ≤ μ u v) → (∀ u, ∑ v ∈ S u, μ u v=1) →
      (∀ u v, v ∈ S u → μ u v ≤ Real.exp (-c*Real.exp (a*L))) →
      (∀ p ∈ B, p.Prime) → (∀ p ∈ B, 0 ≤ ν p) → (∑ p ∈ B, ν p=1) →
      (∀ p ∈ B, ν p ≤ Real.exp (-c*Real.exp (a*L))) →
      ∀ (Z : ℕ), (∀ q ∈ D, q.syntaxSize ≤ Z) →
      (∀ q ∈ D, q.FixedLogBound H) →
      (∀ u v, v ∈ S u → |(v:ℝ)| ≤ Real.exp H) →
      ∀ (r : (Other i → ℤ) → ℕ → Bool) (f : (Other i → ℤ) → ℕ → ℂ),
      (∀ x, (∀ u, x u ∈ S u) → ∀ p ∈ B, ‖f x p‖ ≤ A) →
      (∀ x, (∀ u, x u ∈ S u) → ∀ p ∈ B, r x p=true →
        ∀ u, HistoryReconstruction.Good (insertCoordinate i x (p:ℤ)) (e u)) →
      (∀ x, (∀ u, x u ∈ S u) → ∀ p ∈ B, r x p=true →
        Template.Supported k B₀ V₀ j s (Template.evalExpressions (insertCoordinate i x (p:ℤ)) e) t) →
      (∀ q ∈ D, ∀ x, (∀ u, x u ∈ S u) → ∀ p ∈ B, r x p=true → q.DivisorsBelow p) →
      (2^(j+1) : ℝ) ≤ Real.exp (historyPolynomialCost C z d L) →
      (Z : ℝ) ≤ Real.exp (historyPolynomialCost C z d L) →
      H ≤ Real.exp (historyPolynomialCost C z d L) →
      A ≤ Real.exp (historyPolynomialCost C z d L) →
    ‖independentPrimeMean S μ B ν (fun x p => familyCoprimeSupportedValue D (r x p) p
        (fun q => q.integerEval (insertCoordinate i x (p:ℤ))) (f x p))-
      independentPrimeMean S μ B ν (fun x p => familyPolynomialEnlargedValue D
        (fun q => eraseCoordinate i q.numerator) (r x p) (f x p))‖ ≤
      Real.exp (-(c/2)*Real.exp (a*L)) := by
  filter_upwards [eventually_removalCost_small C z d hC hz ha hc] with L hL
  intro ι _ _ k B₀ V₀ j b s e t D hD i S μ B ν H A hH hA hμ hmass hatom
    hprime hν hνmass hνatom Z hsyntax hfixed hvars r f hf hgood hsupport hfreq htree hZ hHt hAt
  have hH0 : 0 ≤ H := (Real.log_pos (by norm_num : (1:ℝ)<2)).le.trans hH
  have hatom0 : 0 ≤ Real.exp (-c*Real.exp (a*L)) := (Real.exp_pos _).le
  have hfinite := template_family_height_enlargement_error_le k B₀ V₀ j b s e t D hD i S μ B ν
    (Real.exp (-c*Real.exp (a*L))) (Real.exp (-c*Real.exp (a*L))) H A
    hatom0 hatom0 hH hA hμ hmass hatom hprime hν hνmass hνatom Z hsyntax hfixed hvars
    r f hf hgood hsupport hfreq
  apply hfinite.trans
  have hdegree : ∀ q ∈ D, (q.degreeBudget : ℝ) ≤ (Z : ℝ) := by
    intro q hq
    exact_mod_cast q.degreeBudget_le_syntaxSize.trans (hsyntax q hq)
  apply (familyRemovalCost_le (Z := (Z : ℝ)) D Expr.degreeBudget hA hatom0 hdegree).trans
  apply hL A D.card Z ((Z:ℝ)*H) _ _ hA (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hH0) hatom0 hatom0 hAt
  · have hcard : (D.card : ℝ) ≤ (2^(j+1) : ℝ) := by
      exact_mod_cast Template.selected_obstruction_card_le k j b s e t D hD
    exact hcard.trans htree
  · exact hZ
  · calc
      _ ≤ Real.exp (historyPolynomialCost C z d L)*Real.exp (historyPolynomialCost C z d L) :=
        mul_le_mul hZ hHt hH0 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · exact le_refl _
  · exact le_refl _

end Ostmann.Characters.TemplateSupportRemoval

end

end OAI
