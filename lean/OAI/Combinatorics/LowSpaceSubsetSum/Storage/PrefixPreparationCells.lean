import OAI.Combinatorics.LowSpaceSubsetSum.Storage.LayoutPreparationCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.GuessSamplerCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PartitionSamplerCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationPrefixArrays

namespace OAI

/-! # The complete sampled prefix with retained layout and label arrays

Failed earlier stages reserve the supplied but unread finite seed tails.
Successful stages retain the permutation, signs, domains and guesses while
materializing the three balanced label arrays. All runtime fields and work
counters agree with the canonical preparation.
-/

noncomputable section
namespace LowSpaceSubsetSum.PrefixPreparationCells

variable {n : ℕ}

def seedReserve (n : ℕ) : ℕ := 4*(n+1)*(3*n^3+160)+400

theorem seedReserve_covers (n : ℕ) :
    (9*n^3+360)+(3*((mixerSize n+1)*(3*n^3+160))+16) ≤ seedReserve n := by
  have hm : mixerSize n+1 ≤ n+1 := by unfold mixerSize; omega
  have h := Nat.mul_le_mul_right (3*n^3+160) hm
  have h9 : 9*n^3 ≤ (n+1)*(3*n^3+160) := by
    by_cases hn : 2 ≤ n
    · have hh := Nat.mul_le_mul_right (3*n^3) (show 3 ≤ n+1 by omega)
      nlinarith only [hh, Nat.zero_le n]
    · have hn' : n ≤ 1 := by omega
      interval_cases n <;> norm_num
  unfold seedReserve
  nlinarith only [h, h9]

private theorem reserve_bound (I : Instance n) (hn : 10000 ≤ n) :
    seedReserve n+16*n+96 ≤ inputScale I^6 := by
  let u := inputScale I
  have hu : n+1 ≤ u := by unfold u inputScale; omega
  have hu0 : 10000 ≤ u := by omega
  have h3 := Nat.pow_le_pow_left (show n ≤ u by omega) 3
  have hu3 : u ≤ u^3 := by
    simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ u) (by decide : 1 ≤ 3)
  have ht : 3*n^3+160 ≤ 4*u^3 := by nlinarith only [h3, hu3, hu0]
  have hm := Nat.mul_le_mul hu ht
  have hm' : (n+1)*(3*n^3+160) ≤ 4*u^4 := by convert hm using 1; ring
  have hu4 : u ≤ u^4 := by
    simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ u) (by decide : 1 ≤ 4)
  have hcoef : 34*u^4 ≤ u^6 := by
    have h2 : 34 ≤ u^2 := by nlinarith only [hu0]
    calc
      _ ≤ u^2*u^4 := Nat.mul_le_mul_right _ h2
      _ = _ := by rw [← pow_add]
  change seedReserve n+16*n+96 ≤ u^6
  unfold seedReserve
  nlinarith only [hm', hu, hu0, hu4, hcoef]

def assemble
    (layout : (Option (RepresentationLayoutPreparation.Data n) × ℕ) × ℕ)
    (guesses : Unit → (Option (Vector ℕ 3) × ℕ) × ℕ)
    (partitions : Unit → (Option (StoredPartitions.Data n) × ℕ) × ℕ) :
    (Option (RepresentationPrefixArrays.Data n) × ℕ) × ℕ :=
  match layout.1.1 with
  | none => ((none, layout.1.2+1), layout.2+seedReserve n+16*n+96)
  | some l =>
    let g := guesses ()
    match g.1.1 with
    | none => ((none, layout.1.2+g.1.2+2), layout.2+g.2+seedReserve n+16*n+96)
    | some value =>
      let p := partitions ()
      ((p.1.1.map (fun ps => ⟨l,value,ps⟩), layout.1.2+g.1.2+p.1.2+3),
        layout.2+g.2+p.2+16*n+96)

def run (I : Instance n)
    (s : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.Seed) :
    (Option (RepresentationPrefixArrays.Data n) × ℕ) × ℕ :=
  assemble (LayoutPreparationCells.run I s.1.1)
    (fun _ => GuessSamplerCells.run n s.1.2)
    (fun _ => PartitionSamplerCells.run (canonicalRepresentationData I).zeroSetup
      ((canonicalRepresentationData I).zeroSetup.layoutCoupling.ideal s.1.1) s.2)

theorem value (I : Instance n)
    (s : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.Seed) :
    (run I s).1 = RepresentationPrefixArrays.run (canonicalRepresentationData I) s := by
  have hl := LayoutPreparationCells.value I s.1.1
  have hg := GuessSamplerCells.run_value n s.1.2
  have hp := PartitionSamplerCells.value (canonicalRepresentationData I).zeroSetup
    ((canonicalRepresentationData I).zeroSetup.layoutCoupling.ideal s.1.1) s.2
  change _ = StoredPartitions.run _ _ _ at hp
  have hl₁ := congrArg Prod.fst hl
  have hl₂ := congrArg Prod.snd hl
  have hg₁ := congrArg Prod.fst hg
  have hg₂ := congrArg Prod.snd hg
  have hp₁ := congrArg Prod.fst hp
  have hp₂ := congrArg Prod.snd hp
  simp only [run, assemble, RepresentationPrefixArrays.run, hl₁, hl₂, hg₁, hg₂, hp₁, hp₂]
  split
  · simp_all only
  · split <;> simp_all only

private theorem sum_bound (u C L G P H : ℕ) (hu : 4 ≤ u)
    (hL : L ≤ u^10*(C+1)) (hG : G ≤ u^6) (hP : P ≤ u^6) (hH : H ≤ u^6) :
    L+G+P+H ≤ u^11*(C+1) := by
  have h610 : u^6 ≤ u^10 := pow_le_pow_right' (by omega) (by decide)
  have hm := h610.trans (Nat.le_mul_of_pos_right _ (by omega : 0 < C+1))
  have hG' := hG.trans hm
  have hP' := hP.trans hm
  have hH' := hH.trans hm
  have hf : 4*u^10 ≤ u^11 := by
    calc
      _ ≤ u*u^10 := Nat.mul_le_mul_right _ hu
      _ = _ := (pow_succ' _ _).symm
  have hfinal := Nat.mul_le_mul_right (C+1) hf
  simp only [Nat.mul_assoc] at hfinal
  omega

private theorem assemble_cells (u C : ℕ)
    (layout : (Option (RepresentationLayoutPreparation.Data n) × ℕ) × ℕ)
    (guesses : Unit → (Option (Vector ℕ 3) × ℕ) × ℕ)
    (partitions : Unit → (Option (StoredPartitions.Data n) × ℕ) × ℕ)
    (hu : 4 ≤ u) (hL : layout.2 ≤ u^10*(C+1))
    (hG : (guesses ()).2 ≤ u^6) (hP : (partitions ()).2 ≤ u^6)
    (hr : seedReserve n+16*n+96 ≤ u^6) :
    (assemble layout guesses partitions).2 ≤ u^11*(C+1) := by
  have htotal := sum_bound u C layout.2 (guesses ()).2 (partitions ()).2
    (seedReserve n+16*n+96) hu hL hG hP hr
  unfold assemble
  cases h₁ : layout.1.1
  · change layout.2+seedReserve n+16*n+96 ≤ _
    omega
  · simp only
    cases h₂ : (guesses ()).1.1 <;> simp only <;> omega

theorem cells (I : Instance n) (hn : 10000 ≤ n)
    (s : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.Seed) :
    (run I s).2 ≤ inputScale I^11*(compressionDictionaryCapacity n+1) := by
  apply assemble_cells (inputScale I) (compressionDictionaryCapacity n)
  · unfold inputScale; omega
  · exact LayoutPreparationCells.cells I hn s.1.1
  · have hg := GuessSamplerCells.run_cells n s.1.2
    have hr := reserve_bound I hn
    have hcover := seedReserve_covers n
    omega
  · have hp := PartitionLabelCells.family_cells (canonicalRepresentationData I).zeroSetup
      ((canonicalRepresentationData I).zeroSetup.layoutCoupling.ideal s.1.1) 3 id s.2
    change (PartitionSamplerCells.run _ _ _).2 ≤ _ at hp
    have hr := reserve_bound I hn
    have hcover := seedReserve_covers n
    exact hp.trans (by omega)
  · exact reserve_bound I hn

end LowSpaceSubsetSum.PrefixPreparationCells

end

end OAI
