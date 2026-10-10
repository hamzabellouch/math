import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ResiduePreparationCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationExtraPreparation

namespace OAI

/-! # Full prepared-state memory through the bounded extra-prime draw -/

noncomputable section
namespace LowSpaceSubsetSum.ExtraPreparationCells

variable {n : ℕ}

def run (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed) :
    (Option (RepresentationExtraPreparation.Data n) × ℕ) × ℕ :=
  let prepared := ResiduePreparationCells.run I hn hlog s.1
  match h : prepared.1.1 with
  | none => ((none, prepared.1.2+1), prepared.2+9*n^3+512)
  | some data =>
    let hs : (RepresentationResiduePreparation.run I hn hlog s.1).1 = some data :=
      (congrArg Prod.fst (ResiduePreparationCells.value I hn hlog s.1)).symm.trans h
    let out := RepresentationScalarCells.extra (canonicalRepresentationData I).zeroSetup
      (((canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.ideal s.1).1.1.1.1)
      (by omega) data.primes.stored.stored.layout.parameters.widths[3]
      (RepresentationExtraPreparation.width_ideal I hn hlog s.1 data hs) s.2
    ((out.1.1.map (fun q => ⟨data,q⟩), prepared.1.2+out.1.2+1),
      prepared.2+out.2+9*n^3+512)

theorem value (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed) :
    (run I hn hlog s).1 = RepresentationExtraPreparation.run I hn hlog s := by
  have hp₁ := congrArg Prod.fst (ResiduePreparationCells.value I hn hlog s.1)
  have hp₂ := congrArg Prod.snd (ResiduePreparationCells.value I hn hlog s.1)
  simp only [run, hp₂, RepresentationExtraPreparation.run]
  split
  next h =>
    split
    · rfl
    next data hs =>
      have he := (hp₁.symm.trans h).symm.trans hs
      cases he
  next data h =>
    simp only [RepresentationScalarCells.extra_value]
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
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed) :
    (run I hn hlog s).2 ≤ (ResiduePreparationCells.run I hn hlog s.1).2+12*n^3+608 := by
  unfold run
  dsimp only
  split
  · omega
  next data h =>
    have hs : (RepresentationResiduePreparation.run I hn hlog s.1).1 = some data :=
      (congrArg Prod.fst (ResiduePreparationCells.value I hn hlog s.1)).symm.trans h
    have hx := RepresentationScalarCells.extra_cells (canonicalRepresentationData I).zeroSetup
      (((canonicalRepresentationData I).zeroSetup.trialHistoryCoupling.ideal s.1).1.1.1.1)
      (by omega) data.primes.stored.stored.layout.parameters.widths[3]
      (RepresentationExtraPreparation.width_ideal I hn hlog s.1 data hs) s.2
    change _+_+9*n^3+512 ≤ _
    omega

theorem cells (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed) :
    (run I hn hlog s).2 ≤ inputScale I^13*(compressionDictionaryCapacity n+1) := by
  have h1 := cells_add I hn hlog s
  have h2 := ResiduePreparationCells.cells_add I hn hlog s.1
  have h3 := PrimePreparationCells.cells_add I hn hlog s.1.1
  have hbase := RepresentationStoredPreparationCells.cells I hn s.1.1.1
  have htotal : (run I hn hlog s).2 ≤ (RepresentationStoredPreparationCells.run I s.1.1.1).2+(48*n^3+2240) := by
    calc
      _ ≤ (ResiduePreparationCells.run I hn hlog s.1).2+12*n^3+608 := h1
      _ ≤ ((PrimePreparationCells.run I hn hlog s.1.1).2+18*n^3+800)+12*n^3+608 :=
        Nat.add_le_add_right (Nat.add_le_add_right h2 (12*n^3)) 608
      _ ≤ (((RepresentationStoredPreparationCells.run I s.1.1.1).2+18*n^3+832)+18*n^3+800)+12*n^3+608 :=
        Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.add_le_add_right (Nat.add_le_add_right h3 (18*n^3)) 800) (12*n^3)) 608
      _ = _ := by ring
  exact htotal.trans (ScalarStageCells.aggregate n (inputScale I) (compressionDictionaryCapacity n)
    (RepresentationStoredPreparationCells.run I s.1.1.1).2 (48*n^3+2240)
    (by unfold inputScale; omega) (by unfold inputScale; omega) hbase le_rfl)

end LowSpaceSubsetSum.ExtraPreparationCells

end

end OAI
