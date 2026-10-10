import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationStoredPreparation
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScalarDraws

namespace OAI

/-! # Drawing the nested primes after materializing the accepted prefix

The sampler is called with the stored integer widths. Coupling histories
occur in erased type transports and correspondence proofs only.
-/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationPrimePreparation

variable {n : ℕ}

structure Data (n : ℕ) where
  stored : RepresentationStoredPreparation.Data n
  factors : Vector ℕ 3
  moduli : Vector ℕ 3

theorem widths_ideal (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.Seed)
    (data : RepresentationStoredPreparation.Data n)
    (h : (RepresentationStoredPreparation.run I s).1 = some data) (j : Fin 4) :
    data.stored.layout.parameters.widths[j.val] =
      (canonicalRepresentationData I).zeroSetup.samplerPrimeWidths
        (((canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.ideal s).1.1) j := by
  obtain ⟨history, hh, _, _, _, hw, _, _⟩ := RepresentationStoredPreparation.source I s data h hn hlog
  have he := (canonicalRepresentationData I).zeroSetup.partitionHistoryExecution.ideal_eq_of_some
    s history (((canonicalRepresentationData I).zeroSetup.partitionHistoryExecution.value_eq s).trans hh)
  rw [he]
  exact hw j

def run (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : (canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.Seed) :
    Option (Data n) × ℕ :=
  let prepared := RepresentationStoredPreparation.run I s.1
  match h : prepared.1 with
  | none => (none, prepared.2 + 1)
  | some data =>
    let primes := RepresentationScalarDraws.draw (canonicalRepresentationData I).zeroSetup
      (((canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.ideal s.1).1.1)
      data.stored.layout.parameters.widths (widths_ideal I hn hlog s.1 data h) s.2
    (primes.1.map (fun p => ⟨data, p, (ScalarSamplerArrays.moduli p).1⟩),
      prepared.2 + primes.2 + 4)

theorem work (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : (canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.Seed) :
    (run I hn hlog s).2 ≤ (RepresentationStoredPreparation.run I s.1).2 +
      3 * n ^ 3 + 3 * SamplerExecution.primeTestBudget n + 11 := by
  simp only [run]
  split
  · dsimp only
    omega
  next data h =>
    have hw := RepresentationScalarDraws.draw_work (canonicalRepresentationData I).zeroSetup
      (((canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.ideal s.1).1.1)
      data.stored.layout.parameters.widths (widths_ideal I hn hlog s.1 data h) s.2
    change _ + _ + 4 ≤ _
    omega

theorem complete (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : (canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.Seed)
    (history : (canonicalRepresentationData I).zeroSetup.PrimeHistory)
    (h : (canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.bounded s = some history) :
    ∃ data, (run I hn hlog s).1 = some data ∧
      data.factors = ScalarSamplerArrays.factors history.2.val ∧
      ∀ j : Fin 3, data.moduli[j.val] = prefixModulus history.2.val j := by
  let R := (canonicalRepresentationData I).zeroSetup
  have hp : R.partitionHistoryCoupling.bounded s.1 ≠ none := by
    intro hf
    dsimp only [R] at hf
    simp only [RepresentationSetup.primeHistoryCoupling, SamplerCoupling.bind, hf,
      ↓reduceIte, reduceCtorEq] at h
  have hb : R.partitionHistoryCoupling.bounded s.1 =
      some (R.partitionHistoryCoupling.ideal s.1) :=
    (R.partitionHistoryCoupling.agrees s.1).resolve_left hp
  dsimp only [R] at hb
  simp only [RepresentationSetup.primeHistoryCoupling, SamplerCoupling.bind, hb,
    reduceCtorEq, ↓reduceIte] at h
  obtain ⟨p, hprime, he⟩ := Option.map_eq_some_iff.mp h
  cases he
  obtain ⟨stored, hs, _, _, _⟩ := RepresentationStoredPreparation.complete I s.1
    (R.partitionHistoryCoupling.ideal s.1) hb hn hlog
  have hv := RepresentationScalarDraws.draw_value R (R.partitionHistoryCoupling.ideal s.1).1.1
    stored.stored.layout.parameters.widths (widths_ideal I hn hlog s.1 stored hs) s.2
  rw [hprime] at hv
  refine ⟨⟨stored, ScalarSamplerArrays.factors p.val,
    (ScalarSamplerArrays.moduli (ScalarSamplerArrays.factors p.val)).1⟩, ?_, rfl, ?_⟩
  · unfold run
    dsimp only
    split
    next hf =>
      rw [hs] at hf
      contradiction
    next data hd =>
      have he : data = stored := Option.some.inj (hd.symm.trans hs)
      subst data
      dsimp only [R] at hv
      simpa only [Option.map_some] using
        congrArg (Option.map (fun q => (⟨stored, q, (ScalarSamplerArrays.moduli q).1⟩ : Data n))) hv
  · exact ScalarSamplerArrays.moduli_value R (R.partitionHistoryCoupling.ideal s.1).1.1 p

theorem source (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : (canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.Seed)
    (data : Data n) (h : (run I hn hlog s).1 = some data) :
    ∃ history : (canonicalRepresentationData I).zeroSetup.PrimeHistory,
      (canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.bounded s = some history ∧
      (RepresentationStoredPreparation.run I s.1).1 = some data.stored ∧
      data.factors = ScalarSamplerArrays.factors history.2.val ∧
      ∀ j : Fin 3, data.moduli[j.val] = prefixModulus history.2.val j := by
  unfold run at h
  dsimp only at h
  split at h
  · contradiction
  next stored hs =>
    obtain ⟨q, hq, hd⟩ := Option.map_eq_some_iff.mp h
    cases hd
    have hv := RepresentationScalarDraws.draw_value (canonicalRepresentationData I).zeroSetup
      (((canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.ideal s.1).1.1)
      stored.stored.layout.parameters.widths (widths_ideal I hn hlog s.1 stored hs) s.2
    obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp (hv.symm.trans hq)
    obtain ⟨history, hh, _, _, _, _, _, _⟩ :=
      RepresentationStoredPreparation.source I s.1 stored hs hn hlog
    have hi := (canonicalRepresentationData I).zeroSetup.partitionHistoryExecution.ideal_eq_of_some
      s.1 history (((canonicalRepresentationData I).zeroSetup.partitionHistoryExecution.value_eq s.1).trans hh)
    have hb : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.bounded s.1 =
        some ((canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.ideal s.1) := by
      rw [hi]
      exact hh
    refine ⟨⟨(canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.ideal s.1, p⟩,
      ?_, hs, he.symm, ?_⟩
    · simp only [RepresentationSetup.primeHistoryCoupling, SamplerCoupling.bind, hb,
        reduceCtorEq, ↓reduceIte, hp, Option.map_some]
    · intro j
      change (ScalarSamplerArrays.moduli q).1[j.val] = _
      rw [← he]
      exact ScalarSamplerArrays.moduli_value (canonicalRepresentationData I).zeroSetup
        (((canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.ideal s.1).1.1) p j

theorem moduli_ideal (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : (canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.Seed)
    (data : Data n) (h : (run I hn hlog s).1 = some data) (j : Fin 3) :
    data.moduli[j.val] = prefixModulus
      (((canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.ideal s).2.val) j := by
  obtain ⟨history, hh, _, _, hm⟩ := source I hn hlog s data h
  have he := (canonicalRepresentationData I).zeroSetup.primeHistoryExecution.ideal_eq_of_some
    s history (((canonicalRepresentationData I).zeroSetup.primeHistoryExecution.value_eq s).trans hh)
  rw [he]
  exact hm j

theorem moduli_pos (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (s : (canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.Seed)
    (data : Data n) (h : (run I hn hlog s).1 = some data) (j : Fin 3) :
    0 < data.moduli[j.val] := by
  rw [moduli_ideal I hn hlog s data h j]
  exact prefixModulus_pos _ j

end LowSpaceSubsetSum.RepresentationPrimePreparation

end

end OAI
