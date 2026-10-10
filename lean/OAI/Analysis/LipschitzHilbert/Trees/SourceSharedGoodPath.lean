import OAI.Analysis.LipschitzHilbert.Trees.SourceCommonTerminalIntegral
import OAI.Analysis.LipschitzHilbert.Trees.SourceTerminalScale
import OAI.Analysis.LipschitzHilbert.Estimates.TopWeight
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! Original per-top plane bounds descend to one common good set and
one terminal count. The latter is the supremum of the actual first
ineligible shifted endpoints, without an additional stopping premise. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

/-- Shrinking a good set preserves an integral bound for a nonnegative
integrand, even when integrability was proved only after restriction. -/
theorem nonnegative_integral_shared_good {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (localGood good : Set X) (B : ℝ)
    (hgood : MeasurableSet good) (hsub : good ⊆ localGood)
    (hf : ∀ x, 0 ≤ f x)
    (hbound : Integrable (localGood.indicator f) μ ∧
      (∫ x, localGood.indicator f x ∂μ) ≤ B) :
    Integrable (good.indicator f) μ ∧ (∫ x, good.indicator f x ∂μ) ≤ B := by
  classical
  have heq : good.indicator (localGood.indicator f) = good.indicator f := by
    funext x
    by_cases hx : x ∈ good
    · simp only [Set.indicator_of_mem hx,Set.indicator_of_mem (hsub hx)]
    · simp only [Set.indicator_of_notMem hx]
  have hi : Integrable (good.indicator f) μ := by
    rw [←heq]
    exact hbound.1.indicator hgood
  refine ⟨hi, (integral_mono hi hbound.1 ?_).trans hbound.2⟩
  intro x
  by_cases hx : x ∈ good
  · simp only [Set.indicator_of_mem hx,Set.indicator_of_mem (hsub hx),le_refl]
  · rw [Set.indicator_of_notMem hx]
    exact Set.indicator_nonneg (fun x _ => hf x) x

namespace AngularGrid
variable {τ σ : Type*} {κ : Type} [Fintype κ]

def sourceTopTerminalCount {Kb : ℕ} (g : AngularGrid) (T : τ → SlopeBox)
    (cutoff w : ℝ) (hw : 0 < w) (hKb : 0 < Kb) (shift : Fin Kb) (top : τ) : ℕ :=
  g.firstIneligibleShiftedBlock cutoff (w/(T top).length)
    (div_pos hw (T top).length_pos) hKb shift

theorem source_top_shared_good_common_integral {Kb : ℕ}
    (g : AngularGrid) (tops : Finset τ) (T : τ → SlopeBox)
    (cutoff w Kw D : ℝ) (hw : 0 < w) (hKw : 0 < Kw)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : (ℝ×ℝ) → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a alpha p M : ℝ) (hM : 0 ≤ M)
    (hKb : 0 < Kb) (shift : Fin Kb)
    (localGood : τ → Set (ℝ×ℝ)) (good : Set (ℝ×ℝ)) (bad : τ → Set (ℝ×ℝ))
    (hgood : MeasurableSet good) (hbad : ∀ t ∈ tops, MeasurableSet (bad t))
    (hsub : ∀ t ∈ tops, good \ bad t ⊆ localGood t)
    (μ : Measure (ℝ×ℝ)) (C : ℝ)
    (hbound : ∀ t ∈ tops,
      Integrable ((localGood t).indicator (fun x => (T t).weight Kw D x *
        g.sourceActivePathValue tops (fun u => (T u).slope) (fun u => w/(T u).length)
          cutoff (fun u x => (T u).weight Kw D x) K gap packets assigned stop value
          phase a alpha p M shift t (g.sourceTopTerminalCount T cutoff w hw hKb shift t) x)) μ ∧
      (∫ x, (localGood t).indicator (fun y => (T t).weight Kw D y *
        g.sourceActivePathValue tops (fun u => (T u).slope) (fun u => w/(T u).length)
          cutoff (fun u x => (T u).weight Kw D x) K gap packets assigned stop value
          phase a alpha p M shift t (g.sourceTopTerminalCount T cutoff w hw hKb shift t) y) x ∂μ) ≤
        C*(∫ x, (T t).weight Kw D x ∂μ)) :
    ∀ t ∈ tops,
      Integrable ((good \ bad t).indicator (fun x => (T t).weight Kw D x *
        g.sourceActivePathValue tops (fun u => (T u).slope) (fun u => w/(T u).length)
          cutoff (fun u x => (T u).weight Kw D x) K gap packets assigned stop value
          phase a alpha p M shift t
          (tops.sup (g.sourceTopTerminalCount T cutoff w hw hKb shift)) x)) μ ∧
      (∫ x, (good \ bad t).indicator (fun y => (T t).weight Kw D y *
        g.sourceActivePathValue tops (fun u => (T u).slope) (fun u => w/(T u).length)
          cutoff (fun u x => (T u).weight Kw D x) K gap packets assigned stop value
          phase a alpha p M shift t
          (tops.sup (g.sourceTopTerminalCount T cutoff w hw hKb shift)) y) x ∂μ) ≤
        C*(∫ x, (T t).weight Kw D x ∂μ) := by
  have hw0 (t : τ) (x : ℝ×ℝ) : 0 ≤ (T t).weight Kw D x :=
    ((T t).weight_pos hKw D x).le
  let count := g.sourceTopTerminalCount T cutoff w hw hKb shift
  have hterminal t (_ht : t ∈ tops) :
      ¬g.eligible cutoff (w/(T t).length) (ShiftedBlocks.endpoint shift (count t)) :=
    g.firstIneligibleShiftedBlock_spec cutoff (w/(T t).length)
      (div_pos hw (T t).length_pos) hKb shift
  have hcommon := g.source_common_terminal tops (fun t => w/(T t).length) cutoff
    (fun t _ => (div_pos hw (T t).length_pos).le) hKb shift count hterminal
  intro t ht
  apply g.sourceActivePathValue_integral_count_congr tops
    (fun u => (T u).slope) (fun u => w/(T u).length) cutoff
    (fun u x => (T u).weight Kw D x)
    (fun u _ => (div_pos hw (T u).length_pos).le) hw0 K gap packets assigned stop value
    phase a alpha p M hM hKb shift t ht (count t) (tops.sup count)
    (hterminal t ht) (hcommon t ht) (good \ bad t) μ C
  apply nonnegative_integral_shared_good μ _ (localGood t) (good \ bad t) _
    (hgood.diff (hbad t ht)) (hsub t ht)
  · intro x
    exact mul_nonneg (hw0 t x)
      (g.sourceActivePathValue_nonneg tops (fun u => (T u).slope) (fun u => w/(T u).length)
        cutoff (fun u x => (T u).weight Kw D x) hw0 K gap packets assigned stop value
        phase a alpha p M shift t (g.sourceTopTerminalCount T cutoff w hw hKb shift t) x)
  · exact hbound t ht

end AngularGrid
end LipschitzHilbert

end

end OAI
