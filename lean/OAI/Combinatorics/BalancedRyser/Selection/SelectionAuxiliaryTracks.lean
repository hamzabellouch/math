import OAI.Combinatorics.BalancedRyser.Selection.SelectionCensoring
import OAI.Combinatorics.BalancedRyser.Selection.SelectionHistoryInvariant

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators

namespace Balanced.Selection.Process

attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [Fintype V]

def censoredDomainNumerator (q : ℕ) (G : Input I V) (S : State I V)
    (r : Noise I V) (i : I) : ℝ :=
  if (q : ℝ) ^ (1 / 8 : ℝ) <
      (((thinned G S r.2.1 r.2.2) ∩ domain G S i).card : ℝ) then
    (domain G S i).card
  else ((survivors G S r.2.1 r.2.2 ∩ domain G S i).card : ℝ)

def censoredDegreeNumerator (q : ℕ) (G : Input I V) (S : State I V)
    (r : Noise I V) (v : V) : ℝ :=
  if r.2.1 ∈ G.exceptional v ∨ (q : ℝ) ^ (1 / 8 : ℝ) <
      (((thinned G S r.2.1 r.2.2) ∩ neighbors G v).card : ℝ) then
    degree G S v
  else degree G (update G S r.1 r.2.1 r.2.2) v

def domainTrackIncrement (p : Parameters) (q t : ℕ) (G : Input I V) (i : I)
    (before : Option (State I V)) (draw : Option (Noise I V)) : ℝ :=
  match before, draw with
  | some S, some r =>
      if i ∈ S.remaining then
        censoredDomainNumerator q G S r i / p.sizeScale q (t + 1) -
          (domain G S i).card / p.sizeScale q t
      else 0
  | _, _ => 0

def degreeTrackIncrement (p : Parameters) (q t : ℕ) (G : Input I V) (v : V)
    (before : Option (State I V)) (draw : Option (Noise I V)) : ℝ :=
  match before, draw with
  | some S, some r =>
      if v ∈ currentVertices G S then
        censoredDegreeNumerator q G S r v / p.degreeScale q (Fintype.card I) (t + 1) -
          (degree G S v : ℝ) / p.degreeScale q (Fintype.card I) t
      else 0
  | _, _ => 0

def domainTrack (p : Parameters) (q : ℕ) (G : Input I V) (i : I)
    (t : ℕ) (ω : FiniteHistory.Path (Snapshot I V)) : ℝ :=
  ((domain G initialState i).card : ℝ) +
    ∑ j ∈ Finset.range t, domainTrackIncrement p q j G i (ω j).1 (ω (j + 1)).2

def degreeTrack (p : Parameters) (q : ℕ) (G : Input I V) (v : V)
    (t : ℕ) (ω : FiniteHistory.Path (Snapshot I V)) : ℝ :=
  (degree G initialState v : ℝ) +
    ∑ j ∈ Finset.range t, degreeTrackIncrement p q j G v (ω j).1 (ω (j + 1)).2

@[simp] theorem domainTrack_zero (p : Parameters) (q : ℕ) (G : Input I V)
    (i : I) (ω : FiniteHistory.Path (Snapshot I V)) :
    domainTrack p q G i 0 ω = (domain G initialState i).card := by
  simp [domainTrack]

@[simp] theorem degreeTrack_zero (p : Parameters) (q : ℕ) (G : Input I V)
    (v : V) (ω : FiniteHistory.Path (Snapshot I V)) :
    degreeTrack p q G v 0 ω = degree G initialState v := by
  simp [degreeTrack]

theorem domainTrack_succ_sub (p : Parameters) (q t : ℕ) (G : Input I V)
    (i : I) (ω : FiniteHistory.Path (Snapshot I V)) :
    domainTrack p q G i (t + 1) ω - domainTrack p q G i t ω =
      domainTrackIncrement p q t G i (ω t).1 (ω (t + 1)).2 := by
  simp [domainTrack, Finset.sum_range_succ]

theorem degreeTrack_succ_sub (p : Parameters) (q t : ℕ) (G : Input I V)
    (v : V) (ω : FiniteHistory.Path (Snapshot I V)) :
    degreeTrack p q G v (t + 1) ω - degreeTrack p q G v t ω =
      degreeTrackIncrement p q t G v (ω t).1 (ω (t + 1)).2 := by
  simp [degreeTrack, Finset.sum_range_succ]

omit [Fintype I] in

theorem positive_snapshot_surviving_step (p : Parameters) (q t : ℕ)
    (G : Input I V) (before out : Snapshot I V) (S' : State I V)
    (hout : out.1 = some S') (hpos : 0 < snapshotWeight p q t G before out) :
    ∃ S r, before.1 = some S ∧ out.2 = some r ∧ Precheck p q t G S ∧
      r.1 ∈ S.remaining ∧ r.2.1 ∈ domain G S r.1 ∧
      performedResult q G S r = some S' := by
  have hadv : out.1 = advance q G before.1 out.2 := by
    by_contra h
    simp [snapshotWeight, h] at hpos
  have hdraw : 0 < drawStepWeight p q t G before.1 out.2 := by
    simpa only [snapshotWeight, hadv, ite_true] using hpos
  cases hb : before.1 with
  | none => simp [hb, advance] at hadv; rw [hout] at hadv; contradiction
  | some S =>
    cases hd : out.2 with
    | none => simp [hd, advance] at hadv; rw [hout] at hadv; contradiction
    | some r =>
      have hpre : Precheck p q t G S := by
        by_contra h
        simp [hb, hd, drawStepWeight, h] at hdraw
      have hn : 0 < noiseWeight p q G S r := by
        simpa [hb, hd, drawStepWeight, hpre] using hdraw
      have hr : r.1 ∈ S.remaining ∧ r.2.1 ∈ domain G S r.1 := by
        by_contra h
        simp [noiseWeight, drawWeight, h] at hn
      exact ⟨S, r, rfl, rfl, hpre, hr.1, hr.2, by
        simpa only [hb, hd, advance, hout] using hadv.symm⟩

theorem ae_snapshot_positive_steps (p : Parameters) (q : ℕ) (G : Input I V) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ t,
      0 < snapshotWeight p q t G (ω t) (ω (t + 1)) := by
  apply ae_all_iff.2
  intro t
  have hs := FiniteHistory.ae_step_support (fun n => snapshotPMF p q n G)
    (initialSnapshot (I := I) (V := V)) t
  filter_upwards [hs] with ω hω
  have hn : snapshotWeight p q t G (ω t) (ω (t + 1)) ≠ 0 := by
    intro hz
    apply hω
    change ENNReal.ofReal (snapshotWeight p q t G (ω t) (ω (t + 1))) = 0
    rw [hz, ENNReal.ofReal_zero]
  exact lt_of_le_of_ne (snapshotWeight_nonnegative p q t G _ _) (Ne.symm hn)

theorem domainTrack_agreement_of_positive_steps (p : Parameters) (q : ℕ)
    (G : Input I V) (i : I) (ω : FiniteHistory.Path (Snapshot I V))
    (hzero : ω 0 = initialSnapshot)
    (hstep : ∀ t, 0 < snapshotWeight p q t G (ω t) (ω (t + 1))) :
    ∀ t S, (ω t).1 = some S → i ∈ S.remaining →
      domainTrack p q G i t ω = (domain G S i).card / p.sizeScale q t := by
  intro t
  induction t with
  | zero =>
      intro S hS _
      have heq : S = initialState := by
        simpa only [hzero, initialSnapshot, Option.some.injEq] using hS.symm
      subst S
      simp [Parameters.sizeScale]
  | succ t ih =>
      intro S' hS' hi'
      obtain ⟨S, r, hS, hr, hpre, hri, hrw, hout⟩ :=
        positive_snapshot_surviving_step p q t G (ω t) (ω (t + 1)) S' hS' (hstep t)
      have hup := update_eq_of_performedResult_some hout
      have himem : i ∈ S.remaining.erase r.1 := by
        simpa only [← hup, update] using hi'
      obtain ⟨hine, hi⟩ := Finset.mem_erase.mp himem
      have hthin := (postcheck_of_performedResult_some hout).1 i hi
      have hnum : censoredDomainNumerator q G S r i = (domain G S' i).card := by
        rw [censoredDomainNumerator, ite_eq_right (not_lt_of_ge hthin), ← hup,
          domain_update_eq_survivors_inter_domain G S hine]
      have hprev := ih S hS hi
      have hinc := domainTrack_succ_sub p q t G i ω
      simp only [domainTrackIncrement, hS, hr, hi, ite_true, hnum] at hinc
      linarith

theorem degreeTrack_agreement_of_positive_steps (p : Parameters) (q : ℕ)
    (G : Input I V) (hG : GraphBounds G q p.c p.C) (v : V)
    (ω : FiniteHistory.Path (Snapshot I V)) (hzero : ω 0 = initialSnapshot)
    (hstep : ∀ t, 0 < snapshotWeight p q t G (ω t) (ω (t + 1))) :
    ∀ t S, (ω t).1 = some S → v ∈ currentVertices G S →
      degreeTrack p q G v t ω =
        (degree G S v : ℝ) / p.degreeScale q (Fintype.card I) t := by
  intro t
  induction t with
  | zero =>
      intro S hS _
      have heq : S = initialState := by
        simpa only [hzero, initialSnapshot, Option.some.injEq] using hS.symm
      subst S
      have hn : (Fintype.card I : ℝ) ≠ 0 := by
        rw [hG.1]
        positivity
      simp [Parameters.degreeScale, Parameters.sizeScale, hn]
  | succ t ih =>
      intro S' hS' hv'
      obtain ⟨S, r, hS, hr, hpre, hri, hrw, hout⟩ :=
        positive_snapshot_surviving_step p q t G (ω t) (ω (t + 1)) S' hS' (hstep t)
      have hup := update_eq_of_performedResult_some hout
      have hv : v ∈ currentVertices G S := by
        apply currentVertices_update_subset G S r.1 r.2.1 r.2.2
        simpa only [hup] using hv'
      have hunc := relevant_successor_uncensored hG hrw hout hv'
      have hnum : censoredDegreeNumerator q G S r v = (degree G S' v : ℝ) := by
        rw [censoredDegreeNumerator, ite_eq_right (not_or.mpr
          ⟨hunc.1, not_lt_of_ge hunc.2⟩), hup]
      have hprev := ih S hS hv
      have hinc := degreeTrack_succ_sub p q t G v ω
      simp only [degreeTrackIncrement, hS, hr, hv, ite_true, hnum] at hinc
      linarith

theorem ae_domainTrack_agreement (p : Parameters) (q : ℕ) (G : Input I V) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ i t S,
      (ω t).1 = some S → i ∈ S.remaining →
      domainTrack p q G i t ω = (domain G S i).card / p.sizeScale q t := by
  filter_upwards [FiniteHistory.ae_initial_state (fun t => snapshotPMF p q t G)
    (initialSnapshot (I := I) (V := V)), ae_snapshot_positive_steps p q G] with ω hz hs
  exact fun i => domainTrack_agreement_of_positive_steps p q G i ω hz hs

theorem ae_degreeTrack_agreement (p : Parameters) (q : ℕ) (G : Input I V)
    (hG : GraphBounds G q p.c p.C) :
    ∀ᵐ ω ∂snapshotPathLaw p q G, ∀ v t S,
      (ω t).1 = some S → v ∈ currentVertices G S →
      degreeTrack p q G v t ω =
        (degree G S v : ℝ) / p.degreeScale q (Fintype.card I) t := by
  filter_upwards [FiniteHistory.ae_initial_state (fun t => snapshotPMF p q t G)
    (initialSnapshot (I := I) (V := V)), ae_snapshot_positive_steps p q G] with ω hz hs
  exact fun v => degreeTrack_agreement_of_positive_steps p q G hG v ω hz hs

end Balanced.Selection.Process

end

end OAI
