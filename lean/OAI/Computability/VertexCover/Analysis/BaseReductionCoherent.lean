import Mathlib
import OAI.Computability.VertexCover.PCP.TableGapReduction
import OAI.Computability.VertexCover.Reduction.SimpleParallel

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

theorem value_le_of_counts (Φ : LabelCover) (σ : ℝ)
    (h : ∀ A : Φ.Labeling, (Φ.satisfiedCount A : ℝ) ≤ σ * Φ.M) : Φ.value ≤ σ := by
  classical
  obtain ⟨A, _, hA⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset Φ.Labeling)
    ⟨Φ.defaultLabeling, Finset.mem_univ _⟩ Φ.satisfiedCount
  apply (div_le_iff₀ (Nat.cast_pos.mpr Φ.M_pos)).mpr
  change ((Finset.univ.sup Φ.satisfiedCount : ℕ) : ℝ) ≤ _
  rw [hA]
  exact h A

def ParallelCoherent (Φ : LabelCover) : Prop :=
  ∀ e e', Φ.left e = Φ.left e' → Φ.right e = Φ.right e' → Φ.projection e = Φ.projection e'

end VertexCover.LabelCover

namespace VertexCover.ClauseProjection
open UniqueGames.Foundations
open Target

theorem failureCount_eq_sum (F : Formula) (a : Fin F.«variables» → Bool)
    (indices : List (Fin F.clauses.length)) :
    PCP.failureCount F a indices =
      (indices.map (fun i => if (F.clauses.get i).eval a = false then 1 else 0)).sum := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      simp only [PCP.failureCount, List.map_cons, List.sum_cons, ih]
      congr 1
      unfold PCP.clauseFailure PCP.clauseAt
      change (if (F.clauses.get i).eval a = true then 0 else 1) = _
      cases (F.clauses.get i).eval a <;> rfl

theorem failureCount_all (F : Formula) (a : Fin F.«variables» → Bool) :
    PCP.failureCount F a (PCP.allIndices F) = (unsatisfiedClauses F a).card := by
  rw [failureCount_eq_sum]
  simp only [PCP.allIndices, List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  exact (Finset.card_filter _ _).symm

theorem simple_value_le (F : Formula) (η : ℚ) (hgap : Hastad.SourceGap.ClauseGap F η) :
    (simpleGame F hgap.1).value ≤ 1 - (η : ℝ) / 3 := by
  classical
  apply LabelCover.value_le_of_counts
  intro A
  have hbad := hgap.2 (assignmentOf F hgap.1 (decodedLabeling F hgap.1 A))
  rw [failureCount_all] at hbad
  have hreject := simple_rejection_count F hgap.1 A
  have hrejectR := Nat.cast_le (α := ℝ) |>.mpr hreject
  have hpart := Finset.card_filter_add_card_filter_not ((simpleGame F hgap.1).Satisfies A)
    (s := Finset.univ)
  have hpartR : ((simpleGame F hgap.1).satisfiedCount A : ℝ) +
      ((Finset.univ.filter (fun e => ¬(simpleGame F hgap.1).Satisfies A e)).card : ℝ) =
      (F.clauses.length : ℝ) * 3 := by
    simp only [Finset.card_univ, Fintype.card_fin] at hpart
    change (simpleGame F hgap.1).satisfiedCount A + _ = F.clauses.length * 3 at hpart
    exact_mod_cast hpart
  change ((simpleGame F hgap.1).satisfiedCount A : ℝ) ≤
    (1 - (η : ℝ) / 3) * ((F.clauses.length * 3 : ℕ) : ℝ)
  push_cast
  nlinarith

noncomputable def fixedBaseTable : PCP.RoundTables.BaseTable :=
  PCP.ExpanderTables.exists_base_table.choose

theorem fixedBaseTable_certificate :
    PCP.SpectralReturn.SpectralCertificate (PCP.ExpanderTables.graph fixedBaseTable) (1/100 : ℝ) :=
  PCP.ExpanderTables.exists_base_table.choose_spec

noncomputable def baseReduction (F : Formula) : LabelCover :=
  simpleGame (PCP.TableIteration.gapMap fixedBaseTable F)
    (PCP.TableIteration.gapMap_nonempty fixedBaseTable F)

theorem baseReduction_complete (F : Formula) (hF : F.Satisfiable) :
    ∃ A : (baseReduction F).Labeling, ∀ e, (baseReduction F).Satisfies A e :=
  simple_perfect_complete _ _ (PCP.TableIteration.gapMap_completeness fixedBaseTable F hF)

theorem baseReduction_sound (F : Formula) (hF : ¬F.Satisfiable) :
    (baseReduction F).value ≤ 1 - (PCP.PCPIteration.finalClauseGap : ℝ) / 3 :=
  simple_value_le _ _ (PCP.TableGapReduction.gapMap_clauseGap fixedBaseTable
    fixedBaseTable_certificate F hF)

theorem baseReduction_coherent (F : Formula) : (baseReduction F).ParallelCoherent :=
  simple_parallel _ _

end VertexCover.ClauseProjection


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
