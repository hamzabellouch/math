import OAI.Computability.PerfectCompleteness.Foundations.DualQuotientRowsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.LegalRationalOutputLemmas
import OAI.Computability.PerfectCompleteness.Reduction.FixedCallBudgetLemmas
import OAI.Computability.PerfectCompleteness.Reduction.PreliminaryLevelPair
import OAI.Computability.PerfectCompleteness.Sampling.SamplerCardinalityLemmas

namespace OAI


namespace PerfectCompleteness.PreliminaryOutput

open HierarchicalArrays
open scoped Classical

noncomputable section

variable {v m : Nat} [NeZero m]

def value (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) : ℝ := by
  let F := PreliminarySampler.family clauses branch n t rows repeats
  let : Fintype (HierarchicalGame.LeftVertex F) := Fintype.ofFinite _
  let : Fintype (HierarchicalGame.RightVertex F) := Fintype.ofFinite _
  let : ∀ x, Fintype (HierarchicalGame.LeftLabel F x) := fun _ => Fintype.ofFinite _
  let : ∀ y, Fintype (HierarchicalGame.RightLabel F y) := fun _ => Fintype.ofFinite _
  exact (PreliminarySampler.game clauses branch n t rows repeats hn hbranch hrows).value

theorem exists_target (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (δ : ℚ) (hδ : 0 < δ) :
    let F := PreliminarySampler.family clauses branch n t rows repeats
    let q := CompletionAlphabet.size (Nat.card (Output branch n rows)) δ
    let M := ⌈(3 : ℚ) / δ⌉₊ *
      Nat.card (PreliminarySampler.Raw clauses branch n t rows repeats) * (2 * q)
    ∃ target : Instance q,
      2 ≤ q ∧
      target.leftVertices = Nat.card (HierarchicalGame.LeftVertex F) ∧
      target.rightVertices = Nat.card (HierarchicalGame.RightVertex F) ∧
      target.edges.length ≤ M ∧
      (Encoding.gameBits target).length ≤
        Nat.card (HierarchicalGame.LeftVertex F) + Nat.card (HierarchicalGame.RightVertex F) +
          q + M + 4 + M *
            (Nat.card (HierarchicalGame.LeftVertex F) +
              Nat.card (HierarchicalGame.RightVertex F) + 2 * q * q + 2 * q + 2) ∧
      ((∃ assignment : Fin v → Bool,
          ∀ c, (clauses c).clause.eval assignment = true) → PerfectlyComplete target) ∧
      (value clauses branch n t rows repeats hn hbranch hrows ≤ (δ : ℝ) / 3 →
        target.value ≤ (δ : ℝ)) := by
  let F := PreliminarySampler.family clauses branch n t rows repeats
  let : Nonempty (PreliminarySampler.Raw clauses branch n t rows repeats) :=
    SamplerRationality.raw_nonempty (t := t) clauses rows repeats hn hbranch hrows
  let : Fintype (HierarchicalGame.LeftVertex F) := Fintype.ofFinite _
  let : Fintype (HierarchicalGame.RightVertex F) := Fintype.ofFinite _
  let : ∀ x, Fintype (HierarchicalGame.LeftLabel F x) := fun _ => Fintype.ofFinite _
  let : ∀ y, Fintype (HierarchicalGame.RightLabel F y) := fun _ => Fintype.ofFinite _
  let μ := PreliminarySampler.law (t := t) clauses rows repeats hn hbranch hrows
  let rational := SamplerRationality.preliminaryLaw (t := t)
    clauses rows repeats hn hbranch hrows
  have h := CanonicalRationalOutput.exists_target (HierarchicalGame.toBlockFamily F)
    μ rational.weights rational.positive rational.total rational.cast_weight δ hδ
  simpa only [← Nat.card_eq_fintype_card, value, PreliminarySampler.game,
    HierarchicalGame.game, F, μ] using h

theorem exists_target_size_bound (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows repeats : Nat → Nat) (hn : 0 < n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (δ : ℚ) (hδ : 0 < δ) :
    let q := CompletionAlphabet.size (Nat.card (Output branch n rows)) δ
    let R := SamplerCardinality.occurrenceConstant branch n t rows repeats *
      m ^ (t * Fintype.card (RecursiveSpaces.Slots branch n))
    let M := ⌈(3 : ℚ) / δ⌉₊ * R * (2 * q)
    ∃ target : Instance q,
      2 ≤ q ∧ target.leftVertices ≤ R ∧ target.rightVertices ≤ R ∧
      target.edges.length ≤ M ∧
      (Encoding.gameBits target).length ≤
        2 * R + q + M + 4 + M * (2 * R + 2 * q * q + 2 * q + 2) ∧
      ((∃ assignment : Fin v → Bool,
          ∀ c, (clauses c).clause.eval assignment = true) → PerfectlyComplete target) ∧
      (value clauses branch n t rows repeats hn hbranch hrows ≤ (δ : ℝ) / 3 →
        target.value ≤ (δ : ℝ)) := by
  let F := PreliminarySampler.family clauses branch n t rows repeats
  let q := CompletionAlphabet.size (Nat.card (Output branch n rows)) δ
  let R := SamplerCardinality.occurrenceConstant branch n t rows repeats *
    m ^ (t * Fintype.card (RecursiveSpaces.Slots branch n))
  let M := ⌈(3 : ℚ) / δ⌉₊ * R * (2 * q)
  obtain ⟨target, hq, htL, htR, htE, _htBits, hc, hs⟩ :=
    exists_target clauses branch n t rows repeats hn hbranch hrows δ hδ
  have hraw : Nat.card (PreliminarySampler.Raw clauses branch n t rows repeats) ≤ R :=
    SamplerCardinality.raw_card_le clauses branch n t rows repeats
  have hlraw : Nat.card (HierarchicalGame.LeftVertex F) ≤
      Nat.card (PreliminarySampler.Raw clauses branch n t rows repeats) := by
    apply Nat.card_le_card_of_surjective (HierarchicalGame.leftAt F)
    rintro ⟨key, e, rfl⟩
    exact ⟨e, rfl⟩
  have hrraw : Nat.card (HierarchicalGame.RightVertex F) ≤
      Nat.card (PreliminarySampler.Raw clauses branch n t rows repeats) := by
    apply Nat.card_le_card_of_surjective (HierarchicalGame.rightAt F)
    rintro ⟨key, e, rfl⟩
    exact ⟨e, rfl⟩
  have hl : target.leftVertices ≤ R := htL.le.trans (hlraw.trans hraw)
  have hr : target.rightVertices ≤ R := htR.le.trans (hrraw.trans hraw)
  have he : target.edges.length ≤ M :=
    htE.trans (Nat.mul_le_mul_right (2 * q)
      (Nat.mul_le_mul_left ⌈(3 : ℚ) / δ⌉₊ hraw))
  refine ⟨target, hq, hl, hr, he, ?_, hc, hs⟩
  apply (Encoding.gameBits_length_le_of_edge_count target M he).trans
  have hvertices : target.leftVertices + target.rightVertices ≤ 2 * R := by omega
  have hheader := Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add_right hvertices q) M) 4
  have hbody := Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add_right hvertices (2 * q * q)) (2 * q)) 2
  exact Nat.add_le_add hheader (Nat.mul_le_mul_left M hbody)

end
end PerfectCompleteness.PreliminaryOutput


namespace PerfectCompleteness.FixedPreliminaryGame

open FixedParameters FixedRows

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem depth_pos : 0 < p.plan.depth := by have := p.plan.depth_ge; omega

theorem rows_pos (height : Nat) : 0 < rows p.plan height :=
  lt_of_lt_of_le Nat.zero_lt_one (p.plan.rows_pos (p.plan.depth - height))

def game (input : List Bool) :=
  PreliminarySampler.game (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (branch p) p.plan.depth (sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
    (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1))

abbrev Strategy (input : List Bool) :=
  PreliminaryStrategy.Strategy (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (branch p) p.plan.depth (sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)

def value (input : List Bool) : ℝ :=
  PreliminaryOutput.value (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (branch p) p.plan.depth (sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
    (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1))

theorem completeness (input : List Bool) (accepted : BinaryLanguage.language input) :
    value p input = 1 := by
  obtain ⟨assignment, satisfies⟩ :=
    (PCPSourceMachine.rawSource_satisfiable_iff input).mpr accepted
  let F := PreliminarySampler.family (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (branch p) p.plan.depth (sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
  let : Fintype (HierarchicalGame.LeftVertex F) := Fintype.ofFinite _
  let : Fintype (HierarchicalGame.RightVertex F) := Fintype.ofFinite _
  let : ∀ x, Fintype (HierarchicalGame.LeftLabel F x) := fun _ => Fintype.ofFinite _
  let : ∀ y, Fintype (HierarchicalGame.RightLabel F y) := fun _ => Fintype.ofFinite _
  unfold value PreliminaryOutput.value
  apply HierarchicalGame.value_eq_one F _ assignment
  intro occurrence
  exact satisfies _ (List.getElem_mem occurrence.isLt)

theorem exists_level_pair (input : List Bool) (strategy : Strategy p input)
    (hsuccess : InitialParameters.epsilon δ ≤ (game p input).success strategy) :
    ∃ i j : Fin p.plan.depth, i < j ∧ InitialParameters.simultaneous δ ≤
      (CandidateCoupling.sharedLaw
        (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
        (rows p.plan) (repeats p.plan)
        (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1))).probability
          (fun e => PreliminaryLevelPair.win
              (PCPSource.clauseFamily (BinaryLanguage.totalRename input)) strategy i e &&
            PreliminaryLevelPair.win
              (PCPSource.clauseFamily (BinaryLanguage.totalRename input)) strategy j e) :=
  PreliminaryLevelPair.exists_pair
    (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (depth_pos p) (fun k _ => branch_pos p k) (fun k => rows_pos p (k + 1))
    strategy (InitialParameters.epsilon_pos hδ) p.plan.depth_mass hsuccess

end
end PerfectCompleteness.FixedPreliminaryGame


namespace PerfectCompleteness.FixedPreliminaryValue

open FixedParameters FixedRows FixedPreliminaryGame

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem exists_optimal_strategy (input : List Bool) :
    ∃ strategy : Strategy p input,
      (game p input).success strategy = value p input := by
  let F := PreliminarySampler.family (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (branch p) p.plan.depth (sourceLength p.plan hδ) (rows p.plan) (repeats p.plan)
  let : Fintype (HierarchicalGame.LeftVertex F) := Fintype.ofFinite _
  let : Fintype (HierarchicalGame.RightVertex F) := Fintype.ofFinite _
  let : ∀ x, Fintype (HierarchicalGame.LeftLabel F x) := fun _ => Fintype.ofFinite _
  let : ∀ y, Fintype (HierarchicalGame.RightLabel F y) := fun _ => Fintype.ofFinite _
  exact (game p input).exists_optimal_strategy

theorem value_lt_of_strategy_lt (input : List Bool) (bound : ℝ)
    (hbound : ∀ strategy : Strategy p input, (game p input).success strategy < bound) :
    value p input < bound := by
  obtain ⟨strategy, hs⟩ := exists_optimal_strategy p input
  rw [← hs]
  exact hbound strategy

theorem value_le_of_no_large_strategy (input : List Bool) (bound : ℝ)
    (hbound : ∀ strategy : Strategy p input, ¬bound ≤ (game p input).success strategy) :
    value p input ≤ bound :=
  le_of_lt (value_lt_of_strategy_lt p input bound (fun strategy =>
    lt_of_not_ge (hbound strategy)))

end
end PerfectCompleteness.FixedPreliminaryValue


namespace PerfectCompleteness.PreliminaryPairReserve

open FixedParameters FixedRows
open scoped BigOperators

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem exists_pair (input : List Bool) (strategy : FixedPreliminaryGame.Strategy p input)
    (hsuccess : InitialParameters.epsilon δ ≤
      (FixedPreliminaryGame.game p input).success strategy) :
    ∃ i j : Fin p.plan.depth, i < j ∧
      InitialParameters.simultaneous δ + 3 * p.accuracy ≤
        (CandidateCoupling.sharedLaw
          (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
          (rows p.plan) (repeats p.plan)
          (fun k _ => branch_pos p k)
          (fun k => FixedPreliminaryGame.rows_pos p (k + 1))).probability
            (fun e => PreliminaryLevelPair.win
                (PCPSource.clauseFamily (BinaryLanguage.totalRename input)) strategy i e &&
              PreliminaryLevelPair.win
                (PCPSource.clauseFamily (BinaryLanguage.totalRename input)) strategy j e) := by
  have hmean : InitialParameters.epsilon δ ≤
      𝔼 level : Fin p.plan.depth,
        (CandidateCoupling.sharedLaw
          (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
          (rows p.plan) (repeats p.plan)
          (fun k _ => branch_pos p k)
          (fun k => FixedPreliminaryGame.rows_pos p (k + 1))).probability
            (PreliminaryLevelPair.win
              (PCPSource.clauseFamily (BinaryLanguage.totalRename input)) strategy level) := by
    rw [← PreliminaryLevelPair.success_eq_mean
      (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
      (FixedPreliminaryGame.depth_pos p) (fun k _ => branch_pos p k)
      (fun k => FixedPreliminaryGame.rows_pos p (k + 1)) strategy]
    exact hsuccess
  obtain ⟨i, j, hij, hprob⟩ := LevelPairReserve.exists_pair _ _
    (InitialParameters.epsilon δ) (InitialParameters.epsilon_pos hδ)
    hmean p.plan.depth_mass
  refine ⟨i, j, hij, ?_⟩
  have hsmall := p.accuracy_small 0 (Nat.zero_le _)
  simp only [CommonAccuracy.tolerance, lt_min_iff] at hsmall
  have hε := InitialParameters.epsilon_pos hδ
  have hreserved : InitialParameters.simultaneous δ + 3 * p.accuracy ≤
      2 * InitialParameters.epsilon δ ^ 2 / 3 := by
    unfold InitialParameters.simultaneous
    nlinarith [hsmall.1, sq_pos_of_pos hε]
  exact hreserved.trans hprob

end
end PerfectCompleteness.PreliminaryPairReserve

end OAI
