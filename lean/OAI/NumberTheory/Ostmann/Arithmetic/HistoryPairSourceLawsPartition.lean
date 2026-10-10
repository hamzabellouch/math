import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsBlocks

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceLaws
open Construction CompensationEqualityPatterns
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem original_source_jacobian_eq_patterns (sources : SourceFamily) (origin τ : ι → ℕ)
    (F : (ι → CommonSample sources origin) → ℂ) :
    (dependentProductPrior (fun i => (sources (origin i)).law)).cmean
      (fun x => (∏ i, ((x i).val : ℝ)) • F (tupleEmbed sources origin x)) =
      ∑ p : Pattern τ, ∑ b : BlockDraw p (CommonSample sources origin),
        ((∏ q, biasedBlockWeight sources origin p q (b.val q)) *
          (∏ q, ((b.val q).val : ℝ))) • F (expand p b) := by
  have h := source_cmean_eq_patterns sources origin τ
    (fun w => (∏ i, ((w i).val : ℝ)) • F w)
  simp only [smul_smul] at h
  simp_rw [← biased_product_jacobian sources origin] at h
  exact h

end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI
