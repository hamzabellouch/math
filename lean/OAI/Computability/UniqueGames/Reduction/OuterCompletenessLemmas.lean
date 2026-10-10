import OAI.Computability.UniqueGames.Reduction.ActualCompleteness
import OAI.Computability.UniqueGames.Reduction.FinalParametersLemmas
import OAI.Computability.UniqueGames.Reduction.GapSemanticsLemmas
import OAI.Computability.UniqueGames.Reduction.IncidenceProbabilityLemmas
import OAI.Computability.UniqueGames.Reduction.TableReduction

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.OuterCompleteness

open ActualSource WeightedSource
open UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Integration

/-- Completeness for the actual output after rounding and finite cloning. -/
theorem weighted_completeAt {n s d : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ ξ : ℚ)
    (hγ : 0 < γ) (hξ : ξ ≤ γ / 4) (k : Nat) (g : SplitGadget s d)
    (error : RationalError)
    (hsource : ∃ A : Fin n → Bool,
      1 - ξ ≤ W.weightedValue (fun e => CloneGap.satisfied e A))
    (hbudget : (k : ℚ) * γ + g.stabilityError / 2 ≤ GapSemantics.errorValue error) :
    CompleteAt error
      (ActualGame.outputInstance (Preprocessing.uniformSource W γ hγ) k g) := by
  obtain ⟨A, hA⟩ := Preprocessing.uniformSource_complete W γ ξ hγ hξ hsource
  apply ActualCompleteness.actual_completeAt _ k g A error
  have hm := mul_le_mul_of_nonneg_left hA (show (0 : ℚ) ≤ k by positivity)
  linarith

def sourceError (error : RationalError) (k : Nat) : ℚ :=
  FinalParameters.gamma (GapSemantics.errorValue error) k

theorem sourceError_pos (error : RationalError) {k : Nat} (hk : 0 < k) :
    0 < sourceError error k :=
  (FinalParameters.gamma_bounds (GapSemantics.errorValue_pos error)
    (GapSemantics.errorValue_lt_half error) hk).1

theorem weighted_completeAt_of_parameters {n s d : Nat}
    (error : RationalError) (W : RationalSource (CloneGap.Equation (Fin n)))
    (k : Nat) (hk : 0 < k) (ξ : ℚ)
    (hξ : ξ ≤ sourceError error k / 4) (g : SplitGadget s d)
    (hstable : g.stabilityError ≤ GapSemantics.errorValue error / 2)
    (hsource : ∃ A : Fin n → Bool,
      1 - ξ ≤ W.weightedValue (fun e => CloneGap.satisfied e A)) :
    CompleteAt error
      (ActualGame.outputInstance
        (Preprocessing.uniformSource W (sourceError error k) (sourceError_pos error hk)) k g) := by
  apply weighted_completeAt W (sourceError error k) ξ (sourceError_pos error hk)
    hξ k g error hsource
  calc
    (k : ℚ) * sourceError error k + g.stabilityError / 2 ≤
        (k : ℚ) * sourceError error k + (GapSemantics.errorValue error / 2) / 2 := by
      linarith
    _ = GapSemantics.errorValue error / 2 := FinalParameters.completeness_budget hk
    _ ≤ GapSemantics.errorValue error := by
      have h := GapSemantics.errorValue_pos error
      linarith

theorem weighted_explicit_completeAt_of_parameters {n s d : Nat}
    (error : RationalError) (W : RationalSource (CloneGap.Equation (Fin n)))
    (k : Nat) (hk : 0 < k) (ξ : ℚ)
    (hξ : ξ ≤ sourceError error k / 4) (g : SplitGadget s d)
    (en : NoiseEnumeration g)
    (hstable : g.stabilityError ≤ GapSemantics.errorValue error / 2)
    (hsource : ∃ A : Fin n → Bool,
      1 - ξ ≤ W.weightedValue (fun e => CloneGap.satisfied e A)) :
    CompleteAt error
      (ActualGame.outputInstanceWithEnumeration
        (Preprocessing.uniformSource W (sourceError error k) (sourceError_pos error hk))
        k g en) := by
  apply (ActualGame.completeAt_outputInstanceWithEnumeration_iff error _ k g en).mpr
  exact weighted_completeAt_of_parameters error W k hk ξ hξ g hstable hsource

end UniqueGamesTheorem.Reduction.OuterCompleteness

end

section

namespace UniqueGamesTheorem.Reduction.UniformReduction

open ActualSource
open UniqueGamesTheorem.Integration
open UniqueGamesTheorem.Foundations.Target

variable {n s d : Nat}

def rawSource (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) : Source :=
  Source.ofList es hne

def source (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) : Source :=
  FiniteSource.cloned (rawSource es hne)

/-- All proof-only numerical parameters and the correcting function are absent
    from the runtime input of this map. -/
def output (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) : Instance (2 ^ s) :=
  TableReduction.output (source es hne) k T

def satisfaction (es : List (CloneGap.Equation (Fin n))) (A : Fin n → Bool) : ℚ :=
  (es.countP (fun e => CloneGap.satisfied e A) : ℚ) / es.length

theorem source_variables (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) :
    (source es hne).variables = n * 48 := rfl

theorem source_occurrences (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) :
    (source es hne).occurrences = es.length * CloneGap.distinctTriples.length := by
  exact FiniteSource.cloned_length (rawSource es hne)

theorem source_occurrences_le (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) :
    (source es hne).occurrences ≤ 110592 * es.length := by
  have hd : CloneGap.distinctTriples.length ≤ 110592 := by
    exact Nat.le_trans (List.length_filter_le _ CloneGap.triples)
      (by simp [CloneGap.length_triples])
  rw [source_occurrences]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left es.length hd

theorem source_distinct (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ []) :
    (source es hne).DistinctNames := FiniteSource.cloned_distinct (rawSource es hne)

theorem output_constraint_count (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) :
    (output es hne k T).constraints.length =
      (es.length * CloneGap.distinctTriples.length) ^ k *
        2 ^ ((2 * k + 1) * (s + d + 1)) * T.vectors.length := by
  unfold output TableReduction.output
  erw [ActualGame.outputInstanceWithEnumeration_length]
  simp only [TableReduction.tableEnumeration, source_occurrences, Explicit.edgeCount]
  erw [List.length_finRange]

theorem output_vertex_count (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) :
    (output es hne k T).vertices =
      2 * (ActualGame.explicitBodies (source es hne) k s d).length := rfl

def liftAssignment (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (A : Fin n → Bool) : Fin (source es hne).variables → Bool :=
  fun z => A ((FiniteSource.nameEquiv (rawSource es hne)).symm z).1

theorem source_failure_preserved (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (A : Fin n → Bool) :
    (source es hne).failure (liftAssignment es hne A) = (rawSource es hne).failure A :=
  Preprocessing.cloned_failure_eq (rawSource es hne) A

theorem raw_failure_add_satisfaction (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (A : Fin n → Bool) :
    (rawSource es hne).failure A + satisfaction es A = 1 := by
  have h := SourceProbability.failure_add_satisfaction (rawSource es hne) A
  have hl : (rawSource es hne).sourceList = es := Source.sourceList_ofList es hne
  have ho : (rawSource es hne).occurrences = es.length := rfl
  rw [hl, ho] at h
  exact h

theorem source_complete (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (ξ : ℚ) (hsource : ∃ A : Fin n → Bool, 1 - ξ ≤ satisfaction es A) :
    ∃ A : Fin (source es hne).variables → Bool, (source es hne).failure A ≤ ξ := by
  obtain ⟨A, hA⟩ := hsource
  refine ⟨liftAssignment es hne A, ?_⟩
  rw [source_failure_preserved]
  have hsum := raw_failure_add_satisfaction es hne A
  linarith

/-- The original uniform `((1+ξ)/2)` satisfaction bound supplies exactly the
    quarter-gap premise needed by the cloning theorem. -/
theorem raw_quarter_count_gap (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (ξ : ℚ) (hξ : ξ ≤ 1 / 2)
    (hsource : ∀ A : Fin n → Bool, satisfaction es A ≤ (1 + ξ) / 2) :
    ∀ A : Fin (rawSource es hne).variables → Bool,
      (rawSource es hne).sourceList.length ≤
        4 * (rawSource es hne).sourceList.countP (fun e => !CloneGap.satisfied e A) := by
  intro A
  apply (SourceProbability.quarter_gap_iff (rawSource es hne) A).mp
  have hsum := raw_failure_add_satisfaction es hne A
  have hs := hsource A
  linarith

theorem source_sound (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (ξ : ℚ) (hξ : ξ ≤ 1 / 2)
    (hsource : ∀ A : Fin n → Bool, satisfaction es A ≤ (1 + ξ) / 2) :
    ∀ A : Fin (source es hne).variables → Bool,
      (1 / 64 : ℚ) ≤ (source es hne).failure A := by
  intro A
  have hgap := raw_quarter_count_gap es hne ξ hξ hsource
  have hc := FiniteSource.cloned_gap (rawSource es hne) hgap A
  change (source es hne).sourceList.length ≤
    64 * (source es hne).sourceList.countP (fun e => !CloneGap.satisfied e A) at hc
  rw [SourceProbability.Source_failure_eq_count]
  have hn : (0 : ℚ) < (source es hne).occurrences := by
    exact_mod_cast (source es hne).nonempty
  apply (le_div_iff₀ hn).mpr
  rw [Source.sourceList_length] at hc
  have hc' : ((source es hne).occurrences : ℚ) ≤
      64 * ((source es hne).sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) := by
    exact_mod_cast hc
  linarith

theorem sourceGame_sound (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (ξ : ℚ) (hξ : ξ ≤ 1 / 2)
    (hsource : ∀ A : Fin n → Bool, satisfaction es A ≤ (1 + ξ) / 2) :
    (IncidenceProbability.FoundationBridge.sourceGame (source es hne)).value ≤
      (191 : ℝ) / 192 := by
  have h := IncidenceProbability.FoundationBridge.source_value_le_one_sub_gap_third
    (source es hne) (source_distinct es hne) (1 / 64 : ℝ) (fun A => by
      have hrat := source_sound es hne ξ hξ hsource A
      have hr : ((1 / 64 : ℚ) : ℝ) ≤ ((source es hne).failure A : ℝ) := by
        exact_mod_cast hrat
      norm_num at hr ⊢
      exact hr)
  norm_num at h ⊢
  exact h

theorem completeAt_of_parameters (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (error : RationalError) (k : Nat) (hk : 0 < k) (ξ : ℚ)
    (hξ : ξ ≤ FinalParameters.gamma (GapSemantics.errorValue error) k)
    (T : NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c)
    (hstable : (T.gadget f hf).stabilityError ≤ GapSemantics.errorValue error / 2)
    (hsource : ∃ A : Fin n → Bool, 1 - ξ ≤ satisfaction es A) :
    CompleteAt error (output es hne k T) := by
  obtain ⟨A, hA⟩ := source_complete es hne ξ hsource
  apply (TableReduction.completeAt_output_iff error (source es hne) k T f hf).mpr
  apply ActualCompleteness.actual_completeAt (source es hne) k (T.gadget f hf) A error
  have hm := mul_le_mul_of_nonneg_left (hA.trans hξ) (show (0 : ℚ) ≤ k by positivity)
  calc
    (k : ℚ) * (source es hne).failure A + (T.gadget f hf).stabilityError / 2 ≤
        (k : ℚ) * FinalParameters.gamma (GapSemantics.errorValue error) k +
          (GapSemantics.errorValue error / 2) / 2 := by linarith
    _ = GapSemantics.errorValue error / 2 := FinalParameters.completeness_budget hk
    _ ≤ GapSemantics.errorValue error := by
      have hpos := GapSemantics.errorValue_pos error
      linarith

end UniqueGamesTheorem.Reduction.UniformReduction

end

end OAI
