import OAI.Combinatorics.BalancedRyser.Selection.SelectionHistoryInvariant
import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcessScales
import OAI.Combinatorics.BalancedRyser.Selection.SelectionTailCheck

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.Selection.Process.FirstAbort

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

def StateConcentration (p : Parameters) (q : ℕ) (G : Input I V)
    (t : ℕ) (S : State I V) : Prop :=
  (∀ i ∈ S.remaining,
    |((domain G S i).card : ℝ) - p.sizeScale q t * (slotVertices G i).card| ≤
      (q : ℝ) ^ ((4 : ℝ) / 5)) ∧
  (∀ v ∈ currentVertices G S,
    (degree G S v : ℝ) ≤ p.degreeScale q (Fintype.card I) t *
      (neighbors G v).card + (q : ℝ) ^ ((4 : ℝ) / 5))

def ConcentratedPath (p : Parameters) (q : ℕ) (G : Input I V) (T : ℕ)
    (ω : FiniteHistory.Path (Snapshot I V)) : Prop :=
  ∀ t ≤ T, ∀ S, (ω t).1 = some S → StateConcentration p q G t S

def NoPostAbort (q : ℕ) (G : Input I V) (T : ℕ)
    (ω : FiniteHistory.Path (Snapshot I V)) : Prop :=
  ∀ t < T, ∀ S r, (ω t).1 = some S → (ω (t + 1)).2 = some r →
    Postcheck q G S r.2.1 r.2.2

def SupportedPath (p : Parameters) (q : ℕ) (G : Input I V)
    (ω : FiniteHistory.Path (Snapshot I V)) : Prop :=
  ω 0 = initialSnapshot ∧
    ∀ t, 0 < snapshotWeight p q t G (ω t) (ω (t + 1))

theorem ae_supportedPath (p : Parameters) (q : ℕ) (G : Input I V) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, SupportedPath p q G ω := by
  filter_upwards [FiniteHistory.ae_initial_state (fun t => snapshotPMF p q t G)
      (initialSnapshot (I := I) (V := V)),
    ae_all_iff.2 (fun t => FiniteHistory.ae_step_support
      (fun n => snapshotPMF p q n G) (initialSnapshot (I := I) (V := V)) t)]
      with ω hzero hsupport
  refine ⟨hzero, fun t => ?_⟩
  have hn : snapshotWeight p q t G (ω t) (ω (t + 1)) ≠ 0 := by
    intro hz
    apply hsupport t
    change ENNReal.ofReal (snapshotWeight p q t G (ω t) (ω (t + 1))) = 0
    rw [hz, ENNReal.ofReal_zero]
  exact lt_of_le_of_ne (snapshotWeight_nonnegative p q t G _ _) (Ne.symm hn)

omit [Fintype I] in

theorem next_state_of_checks (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) (S : State I V)
    (hpos : 0 < snapshotWeight p q t G before out)
    (hbefore : before.1 = some S) (hpre : Precheck p q t G S)
    (hpost : ∀ r, out.2 = some r → Postcheck q G S r.2.1 r.2.2) :
    ∃ S', out.1 = some S' := by
  have heq : out.1 = advance q G before.1 out.2 := by
    by_contra hn
    simp [snapshotWeight, hn] at hpos
  have hw : 0 < drawStepWeight p q t G before.1 out.2 := by
    simpa only [snapshotWeight, heq, ite_true] using hpos
  cases hdraw : out.2 with
  | none => simp [hbefore, drawStepWeight, hpre, hdraw] at hw
  | some r =>
      refine ⟨update G S r.1 r.2.1 r.2.2, ?_⟩
      simpa only [hbefore, hdraw, advance, performedResult, hpost r hdraw, ite_true]
        using heq

theorem survives_of_checks (p : Parameters) (q : ℕ) (G : Input I V) (T : ℕ)
    (ω : FiniteHistory.Path (Snapshot I V))
    (hsupport : SupportedPath p q G ω)
    (hpre : ∀ t < T, ∀ S, (ω t).1 = some S → Precheck p q t G S)
    (hpost : NoPostAbort q G T ω) :
    ∀ t ≤ T, ∃ S, (ω t).1 = some S := by
  intro t ht
  induction t with
  | zero => exact ⟨initialState, by rw [hsupport.1]; rfl⟩
  | succ t ih =>
      obtain ⟨S, hS⟩ := ih (by omega)
      exact next_state_of_checks p q t G _ _ S (hsupport.2 t) hS
        (hpre t (by omega) S hS) (fun r hr => hpost t (by omega) S r hS hr)

theorem precheck_of_stateConcentration (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (ht : t ≤ p.lastMainTime q (Fintype.card I))
    (hcard : S.remaining.card = Fintype.card I - t)
    (he₁ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q)
    (hconc : StateConcentration p q G t S) : Precheck p q t G S := by
  have hqn : q ≤ Fintype.card I := by rw [hG.1]; omega
  have hh := Parameters.remaining_ge hp hqn ht
  rw [← hcard] at hh
  have hscale := (Parameters.source_scale_bounds hp hq hPq hG.1 ht).1
  have hP := Parameters.Pstar_pos hp
  exact precheck_of_concentration p q t G S hp hG (by omega) (by linarith)
    hh hcard hscale he₁ he₂ hconc.1 hconc.2

theorem survives_of_concentration (p : Parameters) (q : ℕ) (G : Input I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (he₁ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q)
    (ω : FiniteHistory.Path (Snapshot I V))
    (hsupport : SupportedPath p q G ω)
    (hcard : ∀ t S, (ω t).1 = some S → S.remaining.card = Fintype.card I - t)
    (hconc : ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω)
    (hpost : NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω) :
    ∀ t ≤ p.lastMainTime q (Fintype.card I), ∃ S, (ω t).1 = some S := by
  apply survives_of_checks p q G _ ω hsupport
  · intro t ht S hS
    exact precheck_of_stateConcentration p q t G S hp hG hq hPq ht.le
      (hcard t S hS) he₁ he₂ (hconc t ht.le S hS)
  · exact hpost

theorem ae_survives_of_concentration (p : Parameters) (q : ℕ) (G : Input I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (he₁ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q) :
    ∀ᵐ ω ∂snapshotPathLaw p q G,
      ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω →
      NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω →
      ∀ t ≤ p.lastMainTime q (Fintype.card I), ∃ S, (ω t).1 = some S := by
  filter_upwards [ae_supportedPath p q G, ae_snapshot_remaining_card p q G]
    with ω hs hc
  exact survives_of_concentration p q G hp hG hq hPq he₁ he₂ ω hs hc

theorem main_failure_probability_le (p : Parameters) (q : ℕ) (G : Input I V)
    (hp : p.Admissible) (hG : GraphBounds G q p.c p.C)
    (hq : 2 ≤ q) (hPq : 2 * p.Pstar ≤ q)
    (he₁ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2)
    (he₂ : (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q) :
    (snapshotPathLaw p q G).real
        {ω | (ω (p.lastMainTime q (Fintype.card I))).1 = none} ≤
      (snapshotPathLaw p q G).real
        {ω | ¬ ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω} +
      (snapshotPathLaw p q G).real
        {ω | ¬ NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω} := by
  let μ := snapshotPathLaw p q G
  let E : Set (FiniteHistory.Path (Snapshot I V)) := {ω | ¬ ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω}
  let B : Set (FiniteHistory.Path (Snapshot I V)) := {ω | ¬ NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω}
  have hsub : ∀ᵐ ω ∂μ,
      (ω (p.lastMainTime q (Fintype.card I))).1 = none → ω ∈ E ∪ B := by
    filter_upwards [ae_survives_of_concentration p q G hp hG hq hPq he₁ he₂]
      with ω hω
    intro hf
    by_cases hc : ConcentratedPath p q G (p.lastMainTime q (Fintype.card I)) ω
    · by_cases hb : NoPostAbort q G (p.lastMainTime q (Fintype.card I)) ω
      · obtain ⟨S, hS⟩ := hω hc hb _ le_rfl
        rw [hf] at hS
        contradiction
      · exact Or.inr hb
    · exact Or.inl hc
  have hle : μ.real {ω | (ω (p.lastMainTime q (Fintype.card I))).1 = none} ≤
      μ.real (E ∪ B) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  exact hle.trans (measureReal_union_le E B)

theorem exists_firstAbort_threshold (p : Parameters) (hp : p.Admissible) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q →
      2 ≤ q ∧ 2 * p.Pstar ≤ q ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.smin * p.c * q / 2 ∧
      (q : ℝ) ^ ((4 : ℝ) / 5) ≤ p.a * p.smin * p.c * q := by
  obtain ⟨N, hN⟩ := exists_precheck_threshold p hp
  obtain ⟨M, hM⟩ := eventually_atTop.mp (Parameters.eventually_scale_regime p)
  refine ⟨max N M, fun q hq => ?_⟩
  have hn := hN q ((le_max_left N M).trans hq)
  have hm := hM q ((le_max_right N M).trans hq)
  exact ⟨hm.1, hm.2, hn.2.2⟩

end Balanced.Selection.Process.FirstAbort

end

end OAI
