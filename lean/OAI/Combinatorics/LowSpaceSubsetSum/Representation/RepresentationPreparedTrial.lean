import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSchedulePreparation
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationFamilyPreparation

namespace OAI

/-! # The stopped trial consumes only its stored preparation -/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationPreparedTrial

variable {n : ℕ}

abbrev width (n : ℕ) := StoredTopCoordinates.width n

theorem family_sizes (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d)
    (t : ((RepresentationFamilyPreparation.parameters I hn s).samplerCoupling n).Seed)
    (families : Fin 4 → Array (Fin (2 ^ width n)))
    (hf : (RepresentationFamilyPreparation.run I hn hlog s d h t).1 = some families) :
    ∀ i, (families i).size ≤ 11 * 2 ^ width n := by
  rw [RepresentationFamilyPreparation.value] at hf
  exact SeparatorFamilyExecution.Application.sizes _ n t families hf

def control {D F : Type} (prepared : Option D × ℕ)
    (middle : ∀ d, prepared.1 = some d → Option F × ℕ)
    (last : ∀ d (hd : prepared.1 = some d) f,
      (middle d hd).1 = some f → BudgetedSeparatorCall.Outcome Bool) :
    BudgetedSeparatorCall.Outcome Bool :=
  match h : prepared.1 with
  | none => (none, prepared.2+1)
  | some d =>
    let families := middle d h
    match hf : families.1 with
    | none => (none, prepared.2+families.2+17)
    | some f =>
      let out := last d h f hf
      (out.1, prepared.2+families.2+out.2+17)


def run (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed)
    (budget : ℕ) : BudgetedSeparatorCall.Outcome Bool :=
  control (RepresentationExtraPreparation.run I hn hlog s.1)
    (fun d hd => RepresentationFamilyPreparation.run I hn hlog s.1 d hd s.2)
    (fun d hd rows hf => BudgetedPreparedSchedule.run
      (RepresentationSchedulePreparation.fromSuccess I hn hlog s.1 d hd)
      d.residues.primes.stored.stored.layout.signs rfl (representationBufferCapacity n)
      d.residues.primes.stored.coordinates rows
      (family_sizes I hn hlog s.1 d hd s.2 rows hf) budget)

theorem value (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed)
    (budget rest : ℕ) (v : Bool)
    (hy : (run I hn hlog s budget).1 = some (v, rest)) :
    ∃ history, ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).bounded s = some history ∧
      v = (canonicalRepresentationData I).sampledTrial hn hlog (representationBufferCapacity n) history := by
  unfold run control at hy
  dsimp only at hy
  split at hy
  · contradiction
  next d hd =>
    split at hy
    · contradiction
    next families hf =>
      let R := (canonicalRepresentationData I).zeroSetup
      let S := RepresentationFamilyPreparation.parameters I hn s.1
      obtain ⟨extra, he, _, _⟩ := RepresentationExtraPreparation.source I hn hlog s.1 d hd
      have hi := (R.extraHistoryExecution (by omega)).ideal_eq_of_some s.1 extra
        (((R.extraHistoryExecution (by omega)).value_eq s.1).trans he)
      have hb : (R.extraHistoryCoupling (by omega)).bounded s.1 =
          some ((R.extraHistoryCoupling (by omega)).ideal s.1) := by
        rw [hi]
        exact he
      have hfv := SeparatorFamilyExecution.Application.value S n s.2
      have hfr := (RepresentationFamilyPreparation.value I hn hlog s.1 d hd s.2).symm.trans hf
      rw [hfr] at hfv
      obtain ⟨draws, hdraw, hcodes⟩ := Option.map_eq_some_iff.mp hfv.symm
      have hbounded : (S.samplerCoupling n).bounded s.2 = some draws := by
        exact ((S.samplerExecution n).value_eq
          (show (S.samplerCoupling n).Seed from s.2)).symm.trans hdraw
      refine ⟨⟨(R.extraHistoryCoupling (by omega)).ideal s.1, draws⟩, ?_, ?_⟩
      · dsimp only [R] at hb
        simp only [RepresentationSetup.bucketHistoryCoupling, SamplerCoupling.bind, hb,
          reduceCtorEq, ↓reduceIte]
        change ((S.samplerCoupling n).bounded s.2).map _ = _
        rw [hbounded]
        rfl
      · have ht := BudgetedPreparedSchedule.value
          (RepresentationSchedulePreparation.fromSuccess I hn hlog s.1 d hd)
          d.residues.primes.stored.stored.layout.signs rfl (representationBufferCapacity n)
          d.residues.primes.stored.coordinates (fun _ _ => rfl) families
          (family_sizes I hn hlog s.1 d hd s.2 families hf) budget v rest hy
        rw [RepresentationSchedulePreparation.fromSuccess_eq] at ht
        rw [← hcodes, PreparedSeparatorExpectation.codes_decode] at ht
        exact ht

theorem accepts (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed)
    (history : (canonicalRepresentationData I).zeroSetup.BucketTrialHistory (by omega))
    (hs : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).bounded s = some history)
    (hh : (canonicalRepresentationData I).CoreFavorable hn hlog (representationBufferCapacity n) history) :
    ∃ rest, (run I hn hlog s (2 * trialWatchdog I)).1 = some (true, rest) := by
  let R := (canonicalRepresentationData I).zeroSetup
  let S := RepresentationFamilyPreparation.parameters I hn s.1
  have hp : (R.extraHistoryCoupling (by omega)).bounded s.1 ≠ none := by
    intro hf
    dsimp only [R] at hf
    simp only [RepresentationSetup.bucketHistoryCoupling, SamplerCoupling.bind, hf,
      ↓reduceIte, reduceCtorEq] at hs
  have hb : (R.extraHistoryCoupling (by omega)).bounded s.1 =
      some ((R.extraHistoryCoupling (by omega)).ideal s.1) :=
    ((R.extraHistoryCoupling (by omega)).agrees s.1).resolve_left hp
  dsimp only [R] at hb
  simp only [RepresentationSetup.bucketHistoryCoupling, SamplerCoupling.bind, hb,
    reduceCtorEq, ↓reduceIte] at hs
  obtain ⟨draws, hdraw, he⟩ := Option.map_eq_some_iff.mp hs
  cases he
  obtain ⟨d, hd, _⟩ := RepresentationExtraPreparation.complete I hn hlog s.1
    ((R.extraHistoryCoupling (by omega)).ideal s.1) hb
  have hf := RepresentationFamilyPreparation.value I hn hlog s.1 d hd s.2
  have hv := SeparatorFamilyExecution.Application.value S n s.2
  have hbDraw : (S.samplerCoupling n).bounded
      (show (S.samplerCoupling n).Seed from s.2) = some draws := hdraw
  have hx := ((S.samplerExecution n).value_eq
    (show (S.samplerCoupling n).Seed from s.2)).trans hbDraw
  have hv' : (SeparatorFamilyExecution.Application.run S n s.2).1 =
      some (PreparedSeparatorExpectation.codes S draws) := by
    exact hv.trans (congrArg (Option.map (PreparedSeparatorExpectation.codes S)) hx)
  have hfamily : (RepresentationFamilyPreparation.run I hn hlog s.1 d hd s.2).1 =
      some (PreparedSeparatorExpectation.codes S draws) := hf.trans hv'
  have hdecode : (fun i => (PreparedSeparatorExpectation.codes S draws i).map
      SeparatorStoredMasks.decode) = SeparatorCheck.sampledFamilies draws :=
    PreparedSeparatorExpectation.codes_decode S draws
  have hg : width n ≤ n := by
    simp only [width, StoredTopCoordinates.width, RepresentationSetup.blockHalf, Matrix.cons_val_zero]
    omega
  have hw : 2 ^ (2 * width n) ≤ 2 ^ ((n + 1) / 2) := by
    apply Nat.pow_le_pow_right (by decide)
    simp only [width, StoredTopCoordinates.width, RepresentationSetup.blockHalf, Matrix.cons_val_zero]
    omega
  have hschedule := RepresentationSchedulePreparation.fromSuccess_eq I hn hlog s.1 d hd
  obtain ⟨rest, hr⟩ := BudgetedPreparedSchedule.accepts_of_core
    (RepresentationSchedulePreparation.fromSuccess I hn hlog s.1 d hd)
    d.residues.primes.stored.stored.layout.signs rfl (representationBufferCapacity n)
    hn hg hw d.residues.primes.stored.coordinates (fun _ _ => rfl)
    (PreparedSeparatorExpectation.codes S draws) (PreparedSeparatorExpectation.codes_size S draws)
    (by rw [hschedule, hdecode]; exact hh.2)
    (by rw [hschedule, hdecode]; exact hh.1)
  refine ⟨rest, ?_⟩
  unfold run control
  dsimp only
  split
  next hnone =>
    rw [hd] at hnone
    contradiction
  next d' hd' =>
    have he : d' = d := Option.some.inj (hd'.symm.trans hd)
    subst d'
    split
    next hnone =>
      rw [hfamily] at hnone
      contradiction
    next families hsome =>
      have he : families = PreparedSeparatorExpectation.codes S draws :=
        Option.some.inj (hsome.symm.trans hfamily)
      subst families
      exact hr

theorem sound (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed)
    (budget rest : ℕ) (hy : (run I hn hlog s budget).1 = some (true, rest)) : Solvable I := by
  obtain ⟨history, _, hv⟩ := value I hn hlog s budget rest true hy
  exact (canonicalRepresentationData I).trial_sound history.1.1.1 history.1.1.2 hn hlog
    history.1.2.val (primeRange_prime history.1.2.property).pos (representationBufferCapacity n)
    (SeparatorCheck.sampledFamilies history.2) hv.symm

theorem work (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hscale : Real.logb 2 (inputScale I : ℝ) ≤ (n : ℝ) / 1000000000)
    (s : ((canonicalRepresentationData I).zeroSetup.bucketHistoryCoupling hn).Seed)
    (budget : ℕ) :
    (run I hn hlog s budget).2 ≤ (RepresentationExtraPreparation.run I hn hlog s.1).2 +
      (60 * width n + 51 + 44 * 2 ^ width n *
        (width n * n ^ 3 + 32 * (width n + 1) ^ 3 + 4) + 22) + budget + 18 := by
  unfold run control
  dsimp only
  split
  · omega
  next d hd =>
    have hf := RepresentationFamilyPreparation.work I hn hlog s.1 d hd s.2
    change (RepresentationFamilyPreparation.run I hn hlog s.1 d hd s.2).2 ≤
      60 * width n + 51 + 44 * 2 ^ width n *
        (width n * n ^ 3 + 32 * (width n + 1) ^ 3 + 4) + 22 at hf
    split
    · dsimp only
      omega
    next families hfamilies =>
      have ha : BudgetedSeparatorFlow.Account budget
          (BudgetedPreparedSchedule.run
            (RepresentationSchedulePreparation.fromSuccess I hn hlog s.1 d hd)
            d.residues.primes.stored.stored.layout.signs rfl (representationBufferCapacity n)
            d.residues.primes.stored.coordinates families
            (family_sizes I hn hlog s.1 d hd s.2 families hfamilies) budget) := by
        apply BudgetedSeparatorFlow.bind_account
        · exact BudgetedIncidencePreparation.account _ _ _ _
        · intro blocks left _
          have hs := RepresentationPreparedFields.agrees I hn hlog s.1 d hd
          have he := RepresentationSchedulePreparation.schedule_run_congr
            (RepresentationSchedulePreparation.fromSuccess I hn hlog s.1 d hd)
            (RepresentationFromFamilies.schedule (canonicalRepresentationData I) hn hlog
              (((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).ideal s.1))
            (RepresentationSchedulePreparation.fromSuccess_eq I hn hlog s.1 d hd)
            d.residues.primes.stored.stored.layout.signs rfl hs.signs
            (representationBufferCapacity n) blocks left
          rw [he]
          exact (canonicalRepresentationData I).schedule_account _ _ hn hlog hscale _ _ _ _ blocks left
      have hb := ha.1
      change _ + _ + _ + 17 ≤ _
      omega

end LowSpaceSubsetSum.RepresentationPreparedTrial

end

end OAI
