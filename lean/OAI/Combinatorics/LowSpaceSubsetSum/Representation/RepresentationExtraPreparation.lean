import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationResiduePreparation
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationExtraDraw

namespace OAI

/-! # The complete stored representation prefix through the extra prime -/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationExtraPreparation

variable {n : ℕ}

structure Data (n : ℕ) where
  residues : RepresentationResiduePreparation.Data n
  q : ℕ

theorem width_ideal (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : (canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.Seed)
    (data : RepresentationResiduePreparation.Data n)
    (h : (RepresentationResiduePreparation.run I hn hlog s).1 = some data) :
    data.primes.stored.stored.layout.parameters.widths[3] =
      (canonicalRepresentationData I).zeroSetup.extraPrimeParameter
        (((canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.ideal s).1.1.1.1) := by
  obtain ⟨_, _, hp, _⟩ := RepresentationResiduePreparation.source I hn hlog s data h
  obtain ⟨_, _, hs, _, _⟩ := RepresentationPrimePreparation.source I hn hlog s.1 data.primes hp
  exact RepresentationPrimePreparation.widths_ideal I hn hlog s.1.1 data.primes.stored hs 3

def run (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed) :
    Option (Data n) × ℕ :=
  let prepared := RepresentationResiduePreparation.run I hn hlog s.1
  match h : prepared.1 with
  | none => (none, prepared.2 + 1)
  | some data =>
    let out := RepresentationExtraDraw.draw (canonicalRepresentationData I).zeroSetup
      (((canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.ideal s.1).1.1.1.1)
      (by omega) data.primes.stored.stored.layout.parameters.widths[3]
      (width_ideal I hn hlog s.1 data h) s.2
    (out.1.map (fun q => ⟨data, q⟩), prepared.2 + out.2 + 1)

theorem work (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed) :
    (run I hn hlog s).2 ≤ (RepresentationResiduePreparation.run I hn hlog s.1).2 +
      n ^ 3 + SamplerExecution.primeTestBudget n + 2 := by
  simp only [run]
  split
  · dsimp only
    omega
  next data h =>
    have hw := RepresentationExtraDraw.work (canonicalRepresentationData I).zeroSetup
      (((canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.ideal s.1).1.1.1.1)
      (by omega) data.primes.stored.stored.layout.parameters.widths[3]
      (width_ideal I hn hlog s.1 data h) s.2
    change _ + _ + 1 ≤ _
    omega

theorem complete (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (history : (canonicalRepresentationData I).zeroSetup.ExtraTrialHistory)
    (h : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).bounded s = some history) :
    ∃ data, (run I hn hlog s).1 = some data ∧ data.q = history.2.val := by
  let R := (canonicalRepresentationData I).zeroSetup
  have hp : R.trialHistoryCoupling.bounded s.1 ≠ none := by
    intro hf
    dsimp only [R] at hf
    simp only [RepresentationSetup.extraHistoryCoupling, SamplerCoupling.bind, hf,
      ↓reduceIte, reduceCtorEq] at h
  have hb : R.trialHistoryCoupling.bounded s.1 = some (R.trialHistoryCoupling.ideal s.1) :=
    (R.trialHistoryCoupling.agrees s.1).resolve_left hp
  dsimp only [R] at hb
  simp only [RepresentationSetup.extraHistoryCoupling, SamplerCoupling.bind, hb,
    reduceCtorEq, ↓reduceIte] at h
  obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.mp h
  cases he
  obtain ⟨data, hd, _⟩ := RepresentationResiduePreparation.complete I hn hlog s.1
    (R.trialHistoryCoupling.ideal s.1) hb
  have hv := RepresentationExtraDraw.value R (R.trialHistoryCoupling.ideal s.1).1.1.1.1
    (by omega) data.primes.stored.stored.layout.parameters.widths[3]
    (width_ideal I hn hlog s.1 data hd) s.2
  rw [hq] at hv
  refine ⟨⟨data, q.val⟩, ?_, rfl⟩
  unfold run
  dsimp only
  split
  next hf =>
    rw [hd] at hf
    contradiction
  next data' hd' =>
    have he : data' = data := Option.some.inj (hd'.symm.trans hd)
    subst data'
    dsimp only [R] at hv
    simpa only [Option.map_some] using
      congrArg (Option.map (fun q => (⟨data, q⟩ : Data n))) hv

theorem source (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (data : Data n) (h : (run I hn hlog s).1 = some data) :
    ∃ history : (canonicalRepresentationData I).zeroSetup.ExtraTrialHistory,
      ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).bounded s = some history ∧
      (RepresentationResiduePreparation.run I hn hlog s.1).1 = some data.residues ∧
      data.q = history.2.val := by
  unfold run at h
  dsimp only at h
  split at h
  · contradiction
  next residues hr =>
    obtain ⟨q, hq, hd⟩ := Option.map_eq_some_iff.mp h
    cases hd
    have hv := RepresentationExtraDraw.value (canonicalRepresentationData I).zeroSetup
      (((canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.ideal s.1).1.1.1.1)
      (by omega) residues.primes.stored.stored.layout.parameters.widths[3]
      (width_ideal I hn hlog s.1 residues hr) s.2
    obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp (hv.symm.trans hq)
    obtain ⟨history, hh, _, _⟩ := RepresentationResiduePreparation.source I hn hlog s.1 residues hr
    have hi := (canonicalRepresentationData I).zeroSetup.trialHistoryExecution.ideal_eq_of_some
      s.1 history (((canonicalRepresentationData I).zeroSetup.trialHistoryExecution.value_eq s.1).trans hh)
    have hb : (canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.bounded s.1 =
        some ((canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.ideal s.1) := by
      rw [hi]
      exact hh
    refine ⟨⟨(canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.ideal s.1, p⟩,
      ?_, hr, he.symm⟩
    simp only [RepresentationSetup.extraHistoryCoupling, SamplerCoupling.bind, hb,
      reduceCtorEq, ↓reduceIte, hp, Option.map_some]

end LowSpaceSubsetSum.RepresentationExtraPreparation

end

end OAI
