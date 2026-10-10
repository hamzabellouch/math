import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PrimePreparationCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationResiduePreparation

namespace OAI

/-! # The retained prime state during bounded low-residue draws -/

noncomputable section
namespace LowSpaceSubsetSum.ResiduePreparationCells

variable {n : ℕ}

def run (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : (canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.Seed) :
    (Option (RepresentationResiduePreparation.Data n) × ℕ) × ℕ :=
  let prepared := PrimePreparationCells.run I hn hlog s.1
  match h : prepared.1.1 with
  | none => ((none, prepared.1.2+1), prepared.2+9*n^3+512)
  | some data =>
    let hs : (RepresentationPrimePreparation.run I hn hlog s.1).1 = some data :=
      (congrArg Prod.fst (PrimePreparationCells.value I hn hlog s.1)).symm.trans h
    let residues := RepresentationScalarCells.drawResidues (canonicalRepresentationData I).zeroSetup
      (((canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.ideal s.1).2)
      data.moduli (RepresentationPrimePreparation.moduli_pos I hn hlog s.1 data hs)
      (RepresentationPrimePreparation.moduli_ideal I hn hlog s.1 data hs) s.2
    ((residues.1.1.map (fun r => ⟨data,r⟩), prepared.1.2+residues.1.2+1),
      prepared.2+residues.2+9*n^3+512)

theorem value (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : (canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.Seed) :
    (run I hn hlog s).1 = RepresentationResiduePreparation.run I hn hlog s := by
  have hp₁ := congrArg Prod.fst (PrimePreparationCells.value I hn hlog s.1)
  have hp₂ := congrArg Prod.snd (PrimePreparationCells.value I hn hlog s.1)
  simp only [run, hp₂, RepresentationResiduePreparation.run]
  split
  next h =>
    split
    · rfl
    next data hs =>
      have he := (hp₁.symm.trans h).symm.trans hs
      cases he
  next data h =>
    simp only [RepresentationScalarCells.drawResidues_value]
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
    (s : (canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.Seed) :
    (run I hn hlog s).2 ≤ (PrimePreparationCells.run I hn hlog s.1).2+18*n^3+800 := by
  unfold run
  dsimp only
  split
  · omega
  next data h =>
    have hs : (RepresentationPrimePreparation.run I hn hlog s.1).1 = some data :=
      (congrArg Prod.fst (PrimePreparationCells.value I hn hlog s.1)).symm.trans h
    have hx := RepresentationScalarCells.drawResidues_cells (canonicalRepresentationData I).zeroSetup
      (((canonicalRepresentationData I).zeroSetup.primeHistoryCoupling.ideal s.1).2)
      data.moduli (RepresentationPrimePreparation.moduli_pos I hn hlog s.1 data hs)
      (RepresentationPrimePreparation.moduli_ideal I hn hlog s.1 data hs) s.2
    change _+_+9*n^3+512 ≤ _
    omega

theorem cells (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : (canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.Seed) :
    (run I hn hlog s).2 ≤ inputScale I^13*(compressionDictionaryCapacity n+1) := by
  have h1 := cells_add I hn hlog s
  have h2 := PrimePreparationCells.cells_add I hn hlog s.1
  have hbase := RepresentationStoredPreparationCells.cells I hn s.1.1
  have htotal : (run I hn hlog s).2 ≤ (RepresentationStoredPreparationCells.run I s.1.1).2+(36*n^3+1632) := by
    calc
      _ ≤ (PrimePreparationCells.run I hn hlog s.1).2+18*n^3+800 := h1
      _ ≤ ((RepresentationStoredPreparationCells.run I s.1.1).2+18*n^3+832)+18*n^3+800 :=
        Nat.add_le_add_right (Nat.add_le_add_right h2 (18*n^3)) 800
      _ = _ := by ring
  exact htotal.trans (ScalarStageCells.aggregate n (inputScale I) (compressionDictionaryCapacity n)
    (RepresentationStoredPreparationCells.run I s.1.1).2 (36*n^3+1632)
    (by unfold inputScale; omega) (by unfold inputScale; omega) hbase (by omega))

end LowSpaceSubsetSum.ResiduePreparationCells

end

end OAI
