import OAI.Combinatorics.BalancedRyser.Selection.SelectionFirstAbortFinal
import OAI.Combinatorics.BalancedRyser.Selection.SelectionHistoryFinalLaw
import OAI.Combinatorics.BalancedRyser.Selection.SelectionPostabort

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.Selection.Process

attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] in

theorem not_noPostAbort_eq_union (q : ℕ) (G : Input I V) (T : ℕ) :
    {ω | ¬ FirstAbort.NoPostAbort q G T ω} =
      ⋃ t ∈ Finset.range T, postcheckEvent q G t := by
  ext ω
  constructor
  · intro h
    change ¬ FirstAbort.NoPostAbort q G T ω at h
    unfold FirstAbort.NoPostAbort at h
    push Not at h
    obtain ⟨t, ht, S, r, hS, hr, hbad⟩ := h
    refine Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr ht, ?_⟩⟩
    simpa only [postcheckEvent, Set.mem_ofPred_eq, postcheckFailed, hS, hr] using hbad
  · intro h hgood
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp h
    obtain ⟨ht, hbad⟩ := Set.mem_iUnion.mp ht
    have htime := Finset.mem_range.mp ht
    change postcheckFailed q G (ω t).1 (ω (t + 1)).2 at hbad
    cases hS : (ω t).1 with
    | none => simp [hS, postcheckFailed] at hbad
    | some S =>
      cases hr : (ω (t + 1)).2 with
      | none => simp [hS, hr, postcheckFailed] at hbad
      | some r =>
        have hb : ¬ Postcheck q G S r.2.1 r.2.2 := by
          simpa only [hS, hr, postcheckFailed] using hbad
        exact hb (hgood t htime S r hS hr)

theorem successMass_finalLaw_ge_good_events [Nonempty V]
    (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (htail : (p.tailSlots q : ℝ) ≤ 2 * p.a * q)
    (hlarge : 6 ≤ p.smin * p.c * q)
    (he : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q) :
    1 - (snapshotPathLaw p q G).real
        {ω | ¬ FirstAbort.ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω} -
      (snapshotPathLaw p q G).real
        {ω | ¬ FirstAbort.NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω} ≤
      successMass (finalLaw p q G hno) := by
  let T := p.lastMainTime q (Fintype.card I)
  let E : Set (FiniteHistory.Path (Snapshot I V)) :=
    {ω | ∃ S, (ω T).1 = some S ∧ SourceTailCheck p q G S}
  have hm : MeasurableSet E :=
    (show MeasurableSet {s : Snapshot I V | ∃ S, s.1 = some S ∧ SourceTailCheck p q G S}
      from .of_discrete).preimage (measurable_pi_apply T)
  have hsub : Eᶜ ⊆ {ω | ¬ ∃ S, (ω T).1 = some S ∧
      StateInvariant G S ∧ SourceTailCheck p q G S} := by
    intro ω hω ⟨S, hs, _, ht⟩
    exact hω ⟨S, hs, ht⟩
  have hle := (measureReal_mono hsub (measure_ne_top _ _)).trans
    (FirstAbort.terminal_failure_probability_le p q G hp hG hq hPq htail hlarge he he₂)
  have hcompl : (snapshotPathLaw p q G).real Eᶜ =
      1 - successMass (finalLaw p q G hno) := by
    rw [measureReal_compl hm, successMass_finalLaw_eq_path_probability]
    simp only [probReal_univ]
    rfl
  rw [hcompl] at hle
  linarith

theorem successMass_finalLaw_ge_concentration_sub_postcheck [Nonempty V]
    (p : Parameters) (q : ℕ) (G : Input I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (htail : (p.tailSlots q : ℝ) ≤ 2 * p.a * q)
    (hlarge : 6 ≤ p.smin * p.c * q)
    (he : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q) :
    1 - (snapshotPathLaw p q G).real
      {ω | ¬ FirstAbort.ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω} -
      18 * (q : ℝ) ^ 3 * postcheckTail p q ≤ successMass (finalLaw p q G hno) := by
  have hsuccess := successMass_finalLaw_ge_good_events p q G hno hp hG hq hPq
    htail hlarge he he₂
  rw [not_noPostAbort_eq_union] at hsuccess
  have hpost := main_postcheck_union_mass_le p q hq (Parameters.Pstar_pos hp).le G hG
  linarith

theorem successMass_outputLaw_ge_concentration_sub_postcheck
    (p : Parameters) (q : ℕ) (G : Input I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (htail : (p.tailSlots q : ℝ) ≤ 2 * p.a * q)
    (hlarge : 6 ≤ p.smin * p.c * q)
    (he : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q) :
    1 - (snapshotPathLaw p q G).real
      {ω | ¬ FirstAbort.ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω} -
      18 * (q : ℝ) ^ 3 * postcheckTail p q ≤ successMass (outputLaw p q G hG.2.1) := by
  let : Nonempty V := graphBounds_vertex_nonempty G q p.c p.C hp.1 (by omega) hG
  rw [outputLaw_eq_finalLaw]
  exact successMass_finalLaw_ge_concentration_sub_postcheck p q G hG.2.1 hp hG hq hPq
    htail hlarge he he₂

universe u v

theorem exists_uniform_success_threshold (p : Parameters) (hp : p.Admissible) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q →
      ∀ {I : Type u} {V : Type v} [Fintype I] [Fintype V]
        (G : Input I V) (hG : GraphBounds G q p.c p.C),
      1 - (snapshotPathLaw p q G).real
        {ω | ¬ FirstAbort.ConcentratedPath p q G
          (p.lastMainTime q (Fintype.card I)) ω} -
        18 * (q : ℝ) ^ 3 * postcheckTail p q ≤
          successMass (outputLaw p q G hG.2.1) := by
  obtain ⟨N, hN⟩ := FirstAbort.exists_terminal_threshold p hp
  refine ⟨N, ?_⟩
  intro q hq I V _ _ G hG
  obtain ⟨hq, hPq, htail, hlarge, he, he₂⟩ := hN q hq
  exact successMass_outputLaw_ge_concentration_sub_postcheck p q G hp hG
    hq hPq htail hlarge he he₂

end Balanced.Selection.Process

end

end OAI
