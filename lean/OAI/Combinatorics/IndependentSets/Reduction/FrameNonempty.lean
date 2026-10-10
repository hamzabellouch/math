import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.LabelCoverData
import OAI.Combinatorics.IndependentSets.Fourier.Game
import OAI.Combinatorics.IndependentSets.Fourier.Gap
import OAI.Combinatorics.IndependentSets.Reduction.Parameters
import OAI.Combinatorics.IndependentSets.Reduction.OccurrenceTuple
import OAI.Combinatorics.IndependentSets.Encoding.TargetFormula

namespace OAI

namespace LargeIndependentSets
namespace Normalization

lemma frame_nonempty (b : List Bool) : 1 ≤ (frame b).length := by
  cases b <;> simp [frame]

lemma clauseBits_positive (C : List Literal) : 1 ≤ (clauseBits C).length := by
  have h := frame_nonempty C.length.bits
  simp only [clauseBits,List.length_append,nameBits]
  omega

lemma clauses_le_input (F : Formula) : F.clauses.length ≤ (formulaBits F).length := by
  have hl : ∀ cs : List (List Literal), cs.length ≤ (cs.flatMap clauseBits).length := by
    intro cs
    induction cs with
    | nil => simp
    | cons c cs ih =>
      have hc := clauseBits_positive c
      simp only [List.length_cons,List.flatMap_cons,List.length_append]
      omega
  have h := hl F.clauses
  simp only [formulaBits,List.length_append]
  omega

lemma names_bound (F : Formula) : (names F).length ≤ 3*F.clauses.length := by
  simp only [names,List.length_map]
  have h : ∀ cs : List (List Literal), (∀ c ∈ cs, c.length ≤ 3) →
      cs.flatten.length ≤ 3*cs.length := by
    intro cs hw
    induction cs with
    | nil => simp
    | cons c cs ih =>
      have hc := hw c (by simp)
      have ht := ih (fun c hc => hw c (by simp [hc]))
      simp only [List.flatten_cons,List.length_append,List.length_cons]
      omega
  exact h F.clauses F.width

lemma normalize_variables (F : Formula) :
    (normalize F).«variables» ≤ 3*F.clauses.length+1 := by
  by_cases h : [] ∈ F.clauses
  · simp [normalize,h,contradiction]
  · simpa only [normalize,ite_eq_right h] using Nat.add_le_add_right (names_bound F) 1

lemma normalize_clauses (F : Formula) :
    (normalize F).clauses.length ≤ F.clauses.length+2 := by
  by_cases h : [] ∈ F.clauses
  · have he : normalize F = contradiction := ite_eq_left h
    have hh := congrArg (fun G : TargetFormula => G.clauses.length) he
    change (normalize F).clauses.length = 2 at hh
    rw [hh]
    omega
  · have he : normalize F = ⟨(names F).length+1,F.clauses.map (clause F)⟩ := ite_eq_right h
    have hh := congrArg (fun G : TargetFormula => G.clauses.length) he
    simp only [List.length_map] at hh
    rw [hh]
    omega

lemma normalize_bits (F : Formula) :
    (IndependentSetsGames.Foundations.Complexity.formulaBits (normalize F)).length ≤
      100*((formulaBits F).length+1)^2 := by
  have hc := clauses_le_input F
  have hv := normalize_variables F
  have hm := normalize_clauses F
  have hb := IndependentSetsGames.Foundations.Complexity.formulaBits_length_le (normalize F)
  have hv' : (normalize F).«variables» ≤ 3*(formulaBits F).length+1 := by omega
  have hm' : (normalize F).clauses.length ≤ (formulaBits F).length+2 := by omega
  have hprod := Nat.mul_le_mul hm' (Nat.mul_le_mul_left 3 (Nat.add_le_add_right hv' 2))
  nlinarith [Nat.zero_le (formulaBits F).length]

end Normalization
end LargeIndependentSets

namespace LargeIndependentSets.LCInput
open IndependentSetsGames.Foundations
open Target PCP Hastad.SourceContexts Hastad.SourceGame Games
open scoped BigOperators Classical
noncomputable section

def fallback {n : ℕ} (cl : Target.Clause n) : ClauseAnswer :=
  honestAnswer cl (fun v => if v = cl[0].variableIndex then cl[0].positive else false)

lemma fallback_satisfies {n : ℕ} (cl : Target.Clause n) : localSatisfies cl (fallback cl) = true := by
  simp only [fallback, honest_satisfies, Target.Clause.eval, Target.Literal.eval]
  cases cl[0].positive <;> simp

lemma honest_consistent {n : ℕ} (cl : Target.Clause n) (a : Fin n → Bool) :
    localConsistent cl (honestAnswer cl a) = true := by
  rw [localConsistent_eq_true_iff]
  intro s s' h
  simpa only [honest_answerAt] using congrArg a h

lemma fallback_consistent {n : ℕ} (cl : Target.Clause n) : localConsistent cl (fallback cl) = true :=
  honest_consistent cl _

def repair {n : ℕ} (cl : Target.Clause n) (j : ClauseAnswer) : ClauseAnswer :=
  if localSatisfies cl j = true ∧ localConsistent cl j = true then j else fallback cl

lemma repair_spec {n : ℕ} (cl : Target.Clause n) (j : ClauseAnswer) :
    localSatisfies cl (repair cl j) = true ∧ localConsistent cl (repair cl j) = true := by
  unfold repair
  split
  · assumption
  · exact ⟨fallback_satisfies cl, fallback_consistent cl⟩

lemma repair_honest {n : ℕ} (cl : Target.Clause n) (a : Fin n → Bool) (ha : cl.eval a = true) :
    repair cl (honestAnswer cl a) = honestAnswer cl a := by
  simp [repair, honest_satisfies, ha, honest_consistent]

def repaired (F : Target.Formula) {u : ℕ} (c : ClauseContext F u) (j : J u) : J u :=
  fun t => repair (clauseAt F (c t)) (j t)

def labelCover (F : Target.Formula) (u : ℕ) :
    LabelCoverData (ClauseContext F u) (VariableContext F u) (J u) (I u)
      (Fin u → RandomEvent F) where
  left e := fun t => (e t).1
  right e := (repeatedVisible F u e).1
  project e j := pi F (fun t => (e t).1) (repeatedVisible F u e).1
    (repaired F (fun t => (e t).1) j)

lemma complete (F : Target.Formula) (u : ℕ) (hs : F.Satisfiable) :
    ∃ ℓ ρ, (labelCover F u).Satisfied ℓ ρ := by
  obtain ⟨a,ha⟩ := hs
  refine ⟨fun c => honestJ F c a, fun v => honestI F v a, ?_⟩
  intro e
  change pi F _ _ (repaired F _ (honestJ F _ a)) = _
  have he : repaired F (fun t => (e t).1) (honestJ F (fun t => (e t).1) a) =
      honestJ F (fun t => (e t).1) a := by
    funext t
    exact repair_honest _ a (ha _ (List.getElem_mem _))
  dsimp only [labelCover]
  rw [he]
  exact pi_honest F _ _ a (fun t => ⟨(e t).2,rfl⟩)

lemma repaired_accepts_iff (F : Target.Formula) (hne : F.clauses ≠ []) (u : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u) (j : J u) (i : I u) :
    ((baseGame F hne).repetition u).accepts v c i (repaired F c j) = true ↔
      pi F c v (repaired F c j) = i := by
  rw [Game.repetition_accepts_iff]
  constructor
  · intro h
    funext t
    exact ((baseAccepts_eq_true_iff F _ _ _ _).mp (h t)).2.2
  · intro h t
    apply (baseAccepts_eq_true_iff F _ _ _ _).mpr
    exact ⟨(repair_spec _ _).1,(repair_spec _ _).2,congrFun h t⟩

lemma probability_expectation {Ω : Type*} [Fintype Ω] (μ : FiniteDistribution Ω)
    (event : Ω → Bool) : μ.probability event = μ.expectation (fun x => if event x then 1 else 0) := by
  unfold FiniteDistribution.probability FiniteDistribution.expectation
  simp only [mul_ite, mul_one, mul_zero]

lemma success_eq (F : Target.Formula) (hne : F.clauses ≠ []) (u : ℕ)
    (l : ClauseContext F u → J u) (r : VariableContext F u → I u) :
    ((baseGame F hne).repetition u).success (r, fun c => repaired F c (l c)) =
      𝔼 e : Fin u → RandomEvent F,
      if (labelCover F u).project e (l ((labelCover F u).left e)) = r ((labelCover F u).right e)
      then (1:ℝ) else 0 := by
  rw [Game.success, probability_expectation, repeated_expectation]
  apply Finset.expect_congr rfl
  intro e _
  congr 1
  exact propext (repaired_accepts_iff F hne u _ _ _ _)

lemma sound_of_value (F : Target.Formula) (hne : F.clauses ≠ []) (u : ℕ) {σ : ℝ}
    (hs : ((baseGame F hne).repetition u).value ≤ σ) : (labelCover F u).Sound σ := by
  let : Nonempty (RandomEvent F) := event_nonempty F hne
  intro l r
  have h := (Game.success_le_value ((baseGame F hne).repetition u)
    (r, fun c => repaired F c (l c))).trans hs
  rw [success_eq] at h
  simp only [Finset.expect_eq_sum_div_card, Finset.sum_boole, Finset.card_univ] at h
  have hh := (div_le_iff₀ (Nat.cast_pos.mpr (Fintype.card_pos (α := Fin u → RandomEvent F)))).mp h
  convert hh using 1
  congr 2
  ext constraint
  simp

theorem uniform_repetition {η σ : ℚ} (hη : 0 < η) (hη1 : η ≤ 1) (hσ : 0 < σ) :
    ∃ u : ℕ, 0 < u ∧ ∀ F : Target.Formula, Hastad.SourceGap.ClauseGap F η →
      (labelCover F u).Sound (σ:ℝ) := by
  have hg : 0 < η / 3 := by positivity
  have hg1 : η / 3 ≤ 1 := by linarith
  obtain ⟨u,hu,hpow⟩ := IndependentSetsGames.Soundness.RepetitionUpper.exists_power_lt
    (IndependentSetsGames.Integration.SourceParameters.rate (η/3)) σ
    (IndependentSetsGames.Integration.SourceParameters.rate_bounds hg hg1).1.le
    (IndependentSetsGames.Integration.SourceParameters.rate_bounds hg hg1).2 hσ
  refine ⟨u,hu,?_⟩
  intro F hgap
  apply sound_of_value F hgap.1 u
  have hb : (baseGame F hgap.1).value ≤ 1 - ((η/3:ℚ):ℝ) := by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using base_value_le_of_clause_gap F hgap.1 (η:ℝ) hgap.2
  have hr := IndependentSetsGames.Integration.SourceParameters.game_repetition_rate
    (baseGame F hgap.1) hg hg1 (by simp) hb u
  have hp : (IndependentSetsGames.Integration.SourceParameters.rate (η/3):ℝ)^u ≤ σ := by
    exact_mod_cast hpow.le
  exact hr.trans hp

end
end LargeIndependentSets.LCInput

end OAI
