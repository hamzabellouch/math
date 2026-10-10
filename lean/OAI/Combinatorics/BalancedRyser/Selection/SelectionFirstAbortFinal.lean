import OAI.Combinatorics.BalancedRyser.Selection.SelectionFinalLaw
import OAI.Combinatorics.BalancedRyser.Selection.SelectionFirstAbort

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.Selection.Process.FirstAbort

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

theorem sourceTailCheck_of_stateConcentration (p : Parameters) (q : ℕ)
    (G : Input I V) (S : State I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (htail : (p.tailSlots q : ℝ) ≤ 2 * p.a * q)
    (hlarge : 6 ≤ p.smin * p.c * q)
    (he : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100)
    (hcard : S.remaining.card = Fintype.card I -
      p.lastMainTime q (Fintype.card I))
    (hconc : StateConcentration p q G
      (p.lastMainTime q (Fintype.card I)) S) : SourceTailCheck p q G S := by
  have htailn : p.tailSlots q ≤ Fintype.card I :=
    (Parameters.tailSlots_le_order hp q).trans (by rw [hG.1]; omega)
  have hremaining : S.remaining.card = p.tailSlots q := by
    rw [hcard, Parameters.lastMainTime, Nat.sub_sub_self htailn]
  have hsmall : (S.remaining.card : ℝ) ≤ 2 * p.a * q := by
    rwa [hremaining]
  have hscale := (Parameters.source_scale_bounds hp hq hPq hG.1
    (le_refl (p.lastMainTime q (Fintype.card I)))).1
  have hnum := tail_check_of_concentration p q _ G S hp hG (by omega)
    hcard hsmall hscale hlarge he hconc.1 hconc.2
  refine ⟨(tailCheck_iff G S).2 ⟨hnum.1, ?_⟩, ?_⟩
  · intro v hv i hi
    exact_mod_cast hnum.2 v hv i hi
  · intro i hi
    exact SelectionBarriers.domain_barrier hscale hp.1
      (by exact_mod_cast (show 0 < q by omega)) (by linarith)
      (hG.2.2.1 i).1 (hconc.1 i hi) (Real.exp_pos _)

theorem ae_sourceTailCheck_of_concentration (p : Parameters) (q : ℕ)
    (G : Input I V) (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (htail : (p.tailSlots q : ℝ) ≤ 2 * p.a * q)
    (hlarge : 6 ≤ p.smin * p.c * q)
    (he : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q) :
    ∀ᵐ ω ∂snapshotPathLaw p q G,
      ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω →
      NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω →
      ∃ S, (ω (p.lastMainTime q (Fintype.card I))).1 = some S ∧
        StateInvariant G S ∧ SourceTailCheck p q G S := by
  have he₁ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2 := by linarith
  filter_upwards [ae_survives_of_concentration p q G hp hG hq hPq he₁ he₂,
    ae_snapshot_state_invariant p q G] with ω hsurv hinv
  intro hc hb
  obtain ⟨S, hS⟩ := hsurv hc hb _ le_rfl
  obtain ⟨hInv, hcard⟩ := hinv _ S hS
  refine ⟨S, hS, hInv, ?_⟩
  exact sourceTailCheck_of_stateConcentration p q G S hp hG hq hPq htail hlarge he
    (by omega) (hc _ le_rfl S hS)

theorem terminal_failure_probability_le (p : Parameters) (q : ℕ) (G : Input I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (htail : (p.tailSlots q : ℝ) ≤ 2 * p.a * q)
    (hlarge : 6 ≤ p.smin * p.c * q)
    (he : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q) :
    (snapshotPathLaw p q G).real
        {ω | ¬ ∃ S, (ω (p.lastMainTime q (Fintype.card I))).1 = some S ∧
          StateInvariant G S ∧ SourceTailCheck p q G S} ≤
      (snapshotPathLaw p q G).real
        {ω | ¬ ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω} +
      (snapshotPathLaw p q G).real
        {ω | ¬ NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω} := by
  let μ := snapshotPathLaw p q G
  let E : Set (FiniteHistory.Path (Snapshot I V)) :=
    {ω | ¬ ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω}
  let B : Set (FiniteHistory.Path (Snapshot I V)) :=
    {ω | ¬ NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω}
  apply le_trans (b := μ.real (E ∪ B)) _ (measureReal_union_le E B)
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [ae_sourceTailCheck_of_concentration p q G hp hG hq hPq
    htail hlarge he he₂] with ω hω
  intro hf
  by_cases hc : ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω
  · by_cases hb : NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω
    · exact False.elim (hf (hω hc hb))
    · exact Or.inr hb
  · exact Or.inl hc

theorem exists_terminal_threshold (p : Parameters) (hp : p.Admissible) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q →
      2 ≤ q ∧ 2 * p.Pstar ≤ q ∧
      (p.tailSlots q : ℝ) ≤ 2 * p.a * q ∧
      6 ≤ p.smin * p.c * q ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 100 ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q := by
  obtain ⟨N, hN⟩ := exists_firstAbort_threshold p hp
  obtain ⟨M, hM⟩ := exists_tail_check_threshold p hp
  refine ⟨max N M, fun q hq => ?_⟩
  have hn := hN q ((le_max_left N M).trans hq)
  have hm := hM q ((le_max_right N M).trans hq)
  exact ⟨hn.1, hn.2.1, hm.2.1, hm.2.2.1, hm.2.2.2, hn.2.2.2⟩

end Balanced.Selection.Process.FirstAbort

end

end OAI
