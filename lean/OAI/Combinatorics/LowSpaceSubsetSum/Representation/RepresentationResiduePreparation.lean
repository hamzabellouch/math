import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationPrimePreparation
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationResidueDraws

namespace OAI

/-! # Drawing the three residues from the stored nested moduli -/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationResiduePreparation

variable {n : ℕ}

structure Data (n : ℕ) where
  primes : RepresentationPrimePreparation.Data n
  residues : Vector ℕ 3

def run (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : (canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.Seed) :
    Option (Data n) × ℕ :=
  let prepared := RepresentationPrimePreparation.run I hn hlog s.1
  match h : prepared.1 with
  | none => (none, prepared.2 + 1)
  | some data =>
    let residues := RepresentationResidueDraws.draw (canonicalRepresentationData I).zeroSetup
      (((canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.ideal s.1).2)
      data.moduli (RepresentationPrimePreparation.moduli_pos I hn hlog s.1 data h)
      (RepresentationPrimePreparation.moduli_ideal I hn hlog s.1 data h) s.2
    (residues.1.map (fun r => ⟨data, r⟩), prepared.2 + residues.2 + 1)

theorem work (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : (canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.Seed) :
    (run I hn hlog s).2 ≤ (RepresentationPrimePreparation.run I hn hlog s.1).2 + 3 * n ^ 3 + 8 := by
  simp only [run]
  split
  · dsimp only
    omega
  next data h =>
    have hw := RepresentationResidueDraws.draw_work (canonicalRepresentationData I).zeroSetup
      (((canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.ideal s.1).2)
      data.moduli (RepresentationPrimePreparation.moduli_pos I hn hlog s.1 data h)
      (RepresentationPrimePreparation.moduli_ideal I hn hlog s.1 data h) s.2
    change _ + _ + 1 ≤ _
    omega

theorem complete (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : (canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.Seed)
    (history : (canonicalRepresentationData I).zeroSetup.TrialHistory)
    (h : (canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.bounded s = some history) :
    ∃ data, (run I hn hlog s).1 = some data ∧
      data.residues = ScalarSamplerArrays.residueValues history.2 := by
  let R := (canonicalRepresentationData I).zeroSetup
  have hp : R.primeHistoryCoupling.bounded s.1 ≠ none := by
    intro hf
    dsimp only [R] at hf
    simp only [RepresentationSetup.trialHistoryCoupling, SamplerCoupling.bind, hf,
      ↓reduceIte, reduceCtorEq] at h
  have hb : R.primeHistoryCoupling.bounded s.1 = some (R.primeHistoryCoupling.ideal s.1) :=
    (R.primeHistoryCoupling.agrees s.1).resolve_left hp
  dsimp only [R] at hb
  simp only [RepresentationSetup.trialHistoryCoupling, SamplerCoupling.bind, hb,
    reduceCtorEq, ↓reduceIte] at h
  obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
  cases he
  obtain ⟨data, hd, _, _⟩ := RepresentationPrimePreparation.complete I hn hlog s.1
    (R.primeHistoryCoupling.ideal s.1) hb
  have hv := RepresentationResidueDraws.draw_value R (R.primeHistoryCoupling.ideal s.1).2
    data.moduli (RepresentationPrimePreparation.moduli_pos I hn hlog s.1 data hd)
    (RepresentationPrimePreparation.moduli_ideal I hn hlog s.1 data hd) s.2
  rw [hr] at hv
  refine ⟨⟨data, ScalarSamplerArrays.residueValues r⟩, ?_, rfl⟩
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
    (s : (canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.Seed)
    (data : Data n) (h : (run I hn hlog s).1 = some data) :
    ∃ history : (canonicalRepresentationData I).zeroSetup.TrialHistory,
      (canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.bounded s = some history ∧
      (RepresentationPrimePreparation.run I hn hlog s.1).1 = some data.primes ∧
      data.residues = ScalarSamplerArrays.residueValues history.2 := by
  unfold run at h
  dsimp only at h
  split at h
  · contradiction
  next primes hp =>
    obtain ⟨q, hq, hd⟩ := Option.map_eq_some_iff.mp h
    cases hd
    have hv := RepresentationResidueDraws.draw_value (canonicalRepresentationData I).zeroSetup
      (((canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.ideal s.1).2)
      primes.moduli (RepresentationPrimePreparation.moduli_pos I hn hlog s.1 primes hp)
      (RepresentationPrimePreparation.moduli_ideal I hn hlog s.1 primes hp) s.2
    obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp (hv.symm.trans hq)
    obtain ⟨history, hh, _, _, _⟩ :=
      RepresentationPrimePreparation.source I hn hlog s.1 primes hp
    have hi := (canonicalRepresentationData I).zeroSetup.primeHistoryExecution.ideal_eq_of_some
      s.1 history (((canonicalRepresentationData I).zeroSetup.primeHistoryExecution.value_eq s.1).trans hh)
    have hb : (canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.bounded s.1 =
        some ((canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.ideal s.1) := by
      rw [hi]
      exact hh
    refine ⟨⟨(canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.ideal s.1, r⟩,
      ?_, hp, he.symm⟩
    simp only [RepresentationSetup.trialHistoryCoupling, SamplerCoupling.bind, hb,
      reduceCtorEq, ↓reduceIte, hr, Option.map_some]

end LowSpaceSubsetSum.RepresentationResiduePreparation

end

end OAI
