import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.Simple
import OAI.Combinatorics.IndependentSets.PCP.RoundTableGap
import OAI.Combinatorics.IndependentSets.Reduction.FrameNonempty

namespace OAI

namespace LargeIndependentSets
open IndependentSetsGames.Foundations
open scoped Classical
noncomputable section

namespace SemanticReduction
open Target PCP Hastad.SourceContexts Hastad.SourceGame

def gapFormula (H : RoundTables.BaseTable) (F : LargeIndependentSets.Formula) : Target.Formula :=
  TableIteration.gapMap H (Normalization.normalize F)

instance eventsNonempty (H : RoundTables.BaseTable) (F : LargeIndependentSets.Formula) :
    Nonempty (RandomEvent (gapFormula H F)) :=
  event_nonempty _ (TableIteration.gapMap_nonempty H _)

def reduce (H : RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0 < q)
    (F : LargeIndependentSets.Formula) : Graph :=
  p.output q hq (LCInput.labelCover (gapFormula H F) u)

lemma complete (H : RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0 < q)
    (F : LargeIndependentSets.Formula) (hs : F.Satisfiable) :
    (reduce H p u q hq F).ThreeColorable := by
  obtain ⟨l,r,hr⟩ := LCInput.complete (gapFormula H F) u
    (TableIteration.gapMap_completeness H _ ((Normalization.normalize_satisfiable_iff F).mpr hs))
  exact p.output_complete q hq _ l r hr

lemma vertex_bound (H : RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0 < q)
    (F : LargeIndependentSets.Formula) :
    (reduce H p u q hq F).vertices ≤
      max q ((((gapFormula H F).clauses.length * 3)^u)^p.n * (p.law (J u) (I u)).denominator) := by
  simpa only [reduce, RandomEvent, Hastad.SourceContexts.card_slot, Fintype.card_fun, Fintype.card_prod,
    Fintype.card_fin] using p.output_size q hq (LCInput.labelCover (gapFormula H F) u)

end SemanticReduction

theorem semantic_reduction {δ : ℚ} (hδ : 0 < δ) :
    ∃ H : PCP.RoundTables.BaseTable, ∃ p : SamplerParameters, ∃ u q : ℕ, ∃ hq : 0 < q,
    (∀ F : Formula, F.Satisfiable → (SemanticReduction.reduce H p u q hq F).ThreeColorable) ∧
    (∀ F : Formula, ¬F.Satisfiable →
      ((SemanticReduction.reduce H p u q hq F).independenceNumber : ℚ) <
      δ*(SemanticReduction.reduce H p u q hq F).vertices) := by
  obtain ⟨H,hH⟩ := PCP.ExpanderTables.exists_base_table
  obtain ⟨p,σ,q,hq,hσ,hσ1,hp⟩ := finite_graph_reduction (show (0:ℝ) < δ by exact_mod_cast hδ)
  obtain ⟨u,hu,hrep⟩ := LCInput.uniform_repetition
    PCP.PCPIteration.finalClauseGap_positive PCP.TableGapReduction.finalClauseGap_le_one hσ
  refine ⟨H,p,u,q,hq,SemanticReduction.complete H p u q hq,?_⟩
  intro F hF
  have hg : Hastad.SourceGap.ClauseGap (SemanticReduction.gapFormula H F)
      PCP.PCPIteration.finalClauseGap :=
    PCP.TableGapReduction.gapMap_clauseGap H hH _
      (fun hs => hF ((Normalization.normalize_satisfiable_iff F).mp hs))
  have hs := (hp _ _ _ _ _ (LCInput.labelCover (SemanticReduction.gapFormula H F) u)).2
    (hrep _ hg)
  exact_mod_cast hs

end
end LargeIndependentSets

end OAI
