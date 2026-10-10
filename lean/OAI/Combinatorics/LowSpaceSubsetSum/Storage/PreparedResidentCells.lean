import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationExtraPreparation

namespace OAI

/-! # Cached resident bound for a completed representation preparation

`footprint` is a proof view of the resident lists, sets and fixed-size
vectors. The program can retain `residentLimit n` without traversing any
semantic finite set to compute it.
-/

noncomputable section
namespace LowSpaceSubsetSum.PreparedResidentCells

open scoped BigOperators
variable {n : ℕ}

def leafFootprint (L : RepresentationLeaf (Fin n)) : ℕ :=
  4*(L.top.card+L.mixer.card+L.background.card)+12

def footprint (d : RepresentationExtraPreparation.Data n) : ℕ :=
  let stored := d.residues.primes.stored
  let storedPrefix := stored.stored
  2*n+4*storedPrefix.layout.signs.indices.length+
    4*(∑ j : Fin 3, storedPrefix.layout.domains[j.val].length)+
    2*(∑ j : Fin 3, PartitionLabelExecution.size n j)+
    (∑ side : Fin 2, ∑ i : Fin 4, leafFootprint (stored.leaves side i))+
    8*StoredTopCoordinates.width n+128

def residentLimit (n : ℕ) : ℕ := 256*(n+1)

theorem leaf_bound (L : RepresentationLeaf (Fin n)) : leafFootprint L ≤ 12*n+12 := by
  have ht : L.top.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ L.top
  have hm : L.mixer.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ L.mixer
  have hb : L.background.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ L.background
  unfold leafFootprint
  omega

theorem footprint_bound (d : RepresentationExtraPreparation.Data n)
    (hl : ∀ j : Fin 3, d.residues.primes.stored.stored.layout.domains[j.val].length ≤ n) :
    footprint d ≤ residentLimit n := by
  have hd := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hl j)
  have hp (j : Fin 3) : PartitionLabelExecution.size n j ≤ n := by
    fin_cases j <;> norm_num [PartitionLabelExecution.size, RepresentationSetup.blockCount,
      RepresentationSetup.blockHalf] <;> omega
  have hps := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hp j)
  have hls := Finset.sum_le_sum (fun side (_ : side ∈ (Finset.univ : Finset (Fin 2))) =>
    Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
      leaf_bound (d.residues.primes.stored.leaves side i)))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hd hps hls
  have hs := d.residues.primes.stored.stored.layout.signs.length_le
  have hw : StoredTopCoordinates.width n ≤ n := by
    unfold StoredTopCoordinates.width RepresentationSetup.blockHalf
    simp only [Matrix.cons_val_zero]
    omega
  unfold footprint residentLimit
  dsimp only
  omega

theorem accepted_bound (I : Instance n) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ)+1)+1 ≤ (n : ℝ)/1000)
    (s : ((canonicalRepresentationData I).zeroSetup.extraHistoryCoupling (by omega)).Seed)
    (d : RepresentationExtraPreparation.Data n)
    (h : (RepresentationExtraPreparation.run I hn hlog s).1 = some d) :
    footprint d ≤ residentLimit n := by
  obtain ⟨_, _, hr, _⟩ := RepresentationExtraPreparation.source I hn hlog s d h
  obtain ⟨_, _, hp, _⟩ := RepresentationResiduePreparation.source I hn hlog s.1 d.residues hr
  obtain ⟨_, _, hs, _, _⟩ := RepresentationPrimePreparation.source I hn hlog s.1.1 d.residues.primes hp
  have hprefix := RepresentationStoredPreparation.prefix_result I s.1.1.1 d.residues.primes.stored hs
  exact footprint_bound d (RepresentationStoredPreparation.domain_lengths I s.1.1.1
    d.residues.primes.stored.stored hprefix)

theorem residentLimit_scale (I : Instance n) (hn : 10000 ≤ n) :
    residentLimit n ≤ inputScale I^4*(compressionDictionaryCapacity n+1) := by
  have hu : n+1 ≤ inputScale I := by unfold inputScale; omega
  have hu0 : 10000 ≤ inputScale I := by omega
  have hp : inputScale I ≤ inputScale I^3 := by
    simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ inputScale I) (by decide : 1 ≤ 3)
  have hm := Nat.mul_le_mul_right (inputScale I) (show 256 ≤ inputScale I^3 by omega)
  rw [← pow_succ] at hm
  change 256*inputScale I ≤ inputScale I^4 at hm
  have hc := Nat.le_mul_of_pos_right (inputScale I^4)
    (by omega : 0 < compressionDictionaryCapacity n+1)
  unfold residentLimit
  nlinarith only [hu, hm, hc]

end LowSpaceSubsetSum.PreparedResidentCells

end

end OAI
