import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationStoredPreparationCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ScalarStageCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationPrimePreparation

namespace OAI

/-! # Retaining the stored prefix during bounded nested-prime sampling

Unread candidate vectors are reserved even if prefix preparation rejects.
The successful branch calls the exact stored-width scalar sampler.
-/

noncomputable section
namespace LowSpaceSubsetSum.PrimePreparationCells

variable {n : ℕ}

def run (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : (canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.Seed) :
    (Option (RepresentationPrimePreparation.Data n) × ℕ) × ℕ :=
  let prepared := RepresentationStoredPreparationCells.run I s.1
  match h : prepared.1.1 with
  | none => ((none, prepared.1.2+1), prepared.2+9*n^3+512)
  | some data =>
    let hs : (RepresentationStoredPreparation.run I s.1).1 = some data :=
      (congrArg Prod.fst (RepresentationStoredPreparationCells.value I s.1)).symm.trans h
    let primes := RepresentationScalarCells.draw (canonicalRepresentationData I).zeroSetup
      (((canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.ideal s.1).1.1)
      data.stored.layout.parameters.widths (RepresentationPrimePreparation.widths_ideal I hn hlog s.1 data hs) s.2
    ((primes.1.1.map (fun p => ⟨data,p,(ScalarSamplerArrays.moduli p).1⟩),
      prepared.1.2+primes.1.2+4), prepared.2+primes.2+9*n^3+512)

theorem value (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : (canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.Seed) :
    (run I hn hlog s).1 = RepresentationPrimePreparation.run I hn hlog s := by
  have hp₁ := congrArg Prod.fst (RepresentationStoredPreparationCells.value I s.1)
  have hp₂ := congrArg Prod.snd (RepresentationStoredPreparationCells.value I s.1)
  simp only [run, hp₂, RepresentationPrimePreparation.run]
  split
  next h =>
    split
    · rfl
    next data hs =>
      have he := (hp₁.symm.trans h).symm.trans hs
      cases he
  next data h =>
    simp only [RepresentationScalarCells.draw_value]
    split
    next hs =>
      have he := (hp₁.symm.trans h).symm.trans hs
      cases he
    next data' hs =>
      have he : data = data' := Option.some.inj ((hp₁.symm.trans h).symm.trans hs)
      subst data'
      rfl


theorem cells_add (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : (canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.Seed) :
    (run I hn hlog s).2 ≤ (RepresentationStoredPreparationCells.run I s.1).2+18*n^3+832 := by
  unfold run
  dsimp only
  split
  · omega
  next data h =>
    have hs : (RepresentationStoredPreparation.run I s.1).1 = some data :=
      (congrArg Prod.fst (RepresentationStoredPreparationCells.value I s.1)).symm.trans h
    have hx := RepresentationScalarCells.draw_cells (canonicalRepresentationData I).zeroSetup
      (((canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.ideal s.1).1.1)
      data.stored.layout.parameters.widths (RepresentationPrimePreparation.widths_ideal I hn hlog s.1 data hs) s.2
    change _+_+9*n^3+512 ≤ _
    omega

theorem cells (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : (canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.Seed) :
    (run I hn hlog s).2 ≤ inputScale I^13*(compressionDictionaryCapacity n+1) := by
  have hp := RepresentationStoredPreparationCells.cells I hn s.1
  unfold run
  dsimp only
  split
  · have hs := ScalarStageCells.bound n (inputScale I) (compressionDictionaryCapacity n) 12
      (RepresentationStoredPreparationCells.run I s.1).2 0 (by unfold inputScale; omega)
      (by unfold inputScale; omega) (by decide) hp (Nat.zero_le _)
    omega
  next data h =>
    exact ScalarStageCells.bound n (inputScale I) (compressionDictionaryCapacity n) 12
      (RepresentationStoredPreparationCells.run I s.1).2 _ (by unfold inputScale; omega)
      (by unfold inputScale; omega) (by decide) hp (RepresentationScalarCells.draw_cells _ _ _ _ _)

end LowSpaceSubsetSum.PrimePreparationCells

end

end OAI
