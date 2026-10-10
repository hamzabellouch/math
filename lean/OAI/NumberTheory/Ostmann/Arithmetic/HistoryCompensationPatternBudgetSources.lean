import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationMomentSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationPatternBudget

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryCompensationPatternBudget
open Construction CompensationEqualityPatterns HistoryCompensationMoment
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] Classical.propDecidable

theorem source_cmean_norm_le_caps (sources : SourceFamily) (origin τ : ι→ℕ)
    (C : ι→ℝ)
    (hcap : ∀i (v:CommonSample sources origin),
      sourceWeight sources origin i v*(v.val:ℝ) ≤ C i)
    (F : IndependentSamples sources origin→ℂ)
    (hF : ∀(p:Pattern τ)(b:BlockDraw p (CommonSample sources origin)),
      ‖extendSourceTest sources origin F (expand p b)‖ ≤
        (∏i:ι,((expand p b i).val:ℝ))*∏q:Block p,(2/((b.val q).val:ℝ))) :
    ‖(dependentProductPrior (fun i => (sources (origin i)).law)).cmean F‖ ≤
      ∑p:Pattern τ,(2:ℝ)^Fintype.card (Block p)*∏q:Block p,blockCap p C q := by
  have he := source_sum_eq_common sources origin (extendSourceTest sources origin F)
  simp only [extendSourceTest_tupleEmbed] at he
  have hmean : (dependentProductPrior (fun i => (sources (origin i)).law)).cmean F=
      ∑w:ι → CommonSample sources origin,
        (∏i,sourceWeight sources origin i (w i)) • extendSourceTest sources origin F w := by
    exact he
  rw [hmean]
  apply norm_product_weighted_sum_le_caps τ (sourceWeight sources origin)
    (fun v:CommonSample sources origin => (v.val:ℝ)) C
    (sourceWeight_nonneg sources origin) _ hcap (sourceWeight_sum sources origin) _ hF
  intro v
  exact_mod_cast (commonSample_prime sources origin v).pos

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}

theorem selected_source_cmean_norm_le (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι→ℕ) (F : IndependentSamples C.sources origin→ℂ)
    (hF : ∀(p:Pattern τ)(b:BlockDraw p (CommonSample C.sources origin)),
      ‖extendSourceTest C.sources origin F (expand p b)‖ ≤
        (∏i:ι,((expand p b i).val:ℝ))*∏q:Block p,(2/((b.val q).val:ℝ))) :
    ‖(dependentProductPrior (fun i => (C.sources (origin i)).law)).cmean F‖ ≤
      ∑p:Pattern τ,(2:ℝ)^Fintype.card (Block p)*
        ∏q:Block p,blockCap p (fun i => C.sourceNormalization (origin i)) q :=
  source_cmean_norm_le_caps C.sources origin τ (fun i => C.sourceNormalization (origin i))
    (selected_sourceWeight_mass_mul_le C origin) F hF

theorem selected_source_cmean_norm_le_pow (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι→ℕ) {R : ℝ} (hR : 1 ≤ R)
    (hcap : ∀i,C.sourceNormalization (origin i) ≤ R)
    (F : IndependentSamples C.sources origin→ℂ)
    (hF : ∀(p:Pattern τ)(b:BlockDraw p (CommonSample C.sources origin)),
      ‖extendSourceTest C.sources origin F (expand p b)‖ ≤
        (∏i:ι,((expand p b i).val:ℝ))*∏q:Block p,(2/((b.val q).val:ℝ))) :
    ‖(dependentProductPrior (fun i => (C.sources (origin i)).law)).cmean F‖ ≤
      (2:ℝ)^(Fintype.card ι*Fintype.card ι)*(2:ℝ)^Fintype.card ι*R^Fintype.card ι := by
  apply (selected_source_cmean_norm_le C origin τ F hF).trans
  apply sum_pattern_cost_le τ (fun i => C.sourceNormalization (origin i)) (by positivity)
  intro p
  exact prod_blockCap_le_pow p _
    (fun i => CounterpartNormalizationBound.sourceNormalization_nonneg C (origin i)) hR hcap

end Ostmann.Arithmetic.HistoryCompensationPatternBudget

end

end OAI
