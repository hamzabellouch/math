import OAI.NumberTheory.Ostmann.Arithmetic.CompensationEqualityPatternsSources

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.CompensationEqualityPatterns
open Construction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def extendSourceTest (sources : SourceFamily) (origin : ι → ℕ)
    (F : IndependentSamples sources origin → ℂ) (w : ι → CommonSample sources origin) : ℂ :=
  if h : ∀ i, (w i).val ∈ (sources (origin i)).candidates then
    F (fun i => ⟨(w i).val, h i⟩) else 0

omit [DecidableEq ι] in
@[simp] theorem extendSourceTest_tupleEmbed [DecidableEq ι]
    (sources : SourceFamily) (origin : ι → ℕ)
    (F : IndependentSamples sources origin → ℂ) (x : IndependentSamples sources origin) :
    extendSourceTest sources origin F (tupleEmbed sources origin x) = F x := by
  have hs : ∀ i, (tupleEmbed sources origin x i).val ∈ (sources (origin i)).candidates :=
    fun i => (x i).property
  rw [extendSourceTest, dite_eq_left hs]
  congr 1

theorem source_cmean_arbitrary_eq_patterns (sources : SourceFamily) (origin τ : ι → ℕ)
    (F : IndependentSamples sources origin → ℂ) :
    (dependentProductPrior (fun i => (sources (origin i)).law)).cmean F =
      ∑ p : Pattern τ, ∑ b : BlockDraw p (CommonSample sources origin),
        (∏ q : Block p, blockWeight p (sourceWeight sources origin) q (b.val q)) •
          extendSourceTest sources origin F (expand p b) := by
  simpa only [extendSourceTest_tupleEmbed] using
    source_cmean_eq_patterns sources origin τ (extendSourceTest sources origin F)

end Ostmann.Arithmetic.CompensationEqualityPatterns

end

end OAI
