import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationLeafSpace
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationQueryBound

namespace OAI

/-! # Storage of the concrete parent-task data structures

The footprint counts indexed masks bit by bit, as well as array records,
tournament nodes, the tie buffer, dictionary records and trie nodes. The bound includes
these concrete structures; their simultaneous lifetimes and the prefix stack
require a separate bound.
-/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators

namespace RepresentationPairData

variable {n : ℕ} (D : RepresentationPairData n)

/-- A conservative flat-cell accounting for the two raw-leaf arrays and
the mutable tournament, including its cached indexed occurrence and cursor. -/
def footprint (s : D.State) : ℕ :=
  (12 * n + 32) * (D.leftArray.size + D.storedRight.size + Tournament.nodes s.tree + 1)

theorem footprint_le (s : D.State) {C : ℕ}
    (hL : D.leftArray.size ≤ C) (hR : D.storedRight.size ≤ C) :
    D.footprint s ≤ (12 * n + 32) * (6 * C + 4) := by
  have ht := Tournament.padded_nodes_le D.leftArray.size s.tree
  unfold footprint
  exact Nat.mul_le_mul_left _ (by omega)

end RepresentationPairData

namespace RepresentationParentData

variable {n : ℕ} (D : RepresentationParentData n)

/-- Two current readers, two replay snapshots, and a mutable tie buffer;
dictionary masks and trie links are accounted for separately. -/
def footprint (B : ℕ) : ℕ :=
  3 * (∑ j : Fin 2, (D.pair j).footprint (D.pair j).start) +
    (12 * n + 16) * B + (n + 2) * (D.entries B).size +
    3 * BinaryTrie.nodes (D.collect B).state.user.keys.tree

theorem footprint_le (B : ℕ)
    (hL : ∀ j, (D.pair j).leftArray.size ≤ D.capacity)
    (hR : ∀ j, (D.pair j).storedRight.size ≤ D.capacity)
    (hB : B ≤ D.capacity) :
    D.footprint B ≤
      6 * (12 * n + 32) * (6 * D.capacity + 4) +
        (12 * n + 16) * D.capacity +
        (n + 2 + 3 * (WeightEncoding.entryWidth D.input + 1)) * (D.capacity + 1) := by
  have hp : (∑ j : Fin 2, (D.pair j).footprint (D.pair j).start) ≤
      2 * ((12 * n + 32) * (6 * D.capacity + 4)) := by
    calc
      _ ≤ ∑ _ : Fin 2, (12 * n + 32) * (6 * D.capacity + 4) :=
        Finset.sum_le_sum (fun j _ => (D.pair j).footprint_le _ (hL j) (hR j))
      _ = _ := by simp
  obtain ⟨he, ht⟩ := D.storage B
  unfold footprint
  have hb := Nat.mul_le_mul_left (12 * n + 16) hB
  have her := Nat.mul_le_mul_left (n + 2) he
  have htr := Nat.mul_le_mul_left 3 ht
  nlinarith only [hp, hb, her, htr]

end RepresentationParentData

/-- The mutable tie buffer chosen by the manuscript. -/
def representationBufferCapacity (n : ℕ) : ℕ := 2 ^ (19 * n / 100)

theorem representationBufferCapacity_le (n : ℕ) :
    representationBufferCapacity n ≤ compressionDictionaryCapacity n := by
  unfold representationBufferCapacity compressionDictionaryCapacity
  exact Nat.pow_le_pow_right (by decide) (by omega)

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem main_leaf_rate_le_capacity (hn : 10000 ≤ n) :
    (2 : ℝ) ^ ((37 / 200 : ℝ) * n) ≤ compressionDictionaryCapacity n := by
  apply (Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (show (37 / 200 : ℝ) * n ≤ (199 / 1000 : ℝ) * n - 1 by
      have hnR : (10000 : ℝ) ≤ n := by exact_mod_cast hn
      linarith)).trans
  exact compression_capacity_lower n

/-- The array capacity is valid for every residue and prefix, on every
outcome. In particular no resource or successful-solution event is assumed. -/
theorem schedule_pair_capacity (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000)
    (q : ℕ) (hq : 0 < q) (z : ℕ) (side : Fin 2) (P : MaskRestriction n) (child : Fin 2) :
    let D := ({ (R.scheduleData h r hn hlog q hq).parentData side z with maskRestriction := P }).pair child
    D.leftArray.size ≤ compressionDictionaryCapacity n ∧
      D.storedRight.size ≤ compressionDictionaryCapacity n := by
  dsimp only
  have hs := R.schedule_pair_storage h r hn hlog hscale q hq z side P child
  have hc := main_leaf_rate_le_capacity hn
  exact ⟨by exact_mod_cast hs.1.trans hc, by exact_mod_cast hs.2.1.trans hc⟩

theorem schedule_task_footprint (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000)
    (q : ℕ) (hq : 0 < q) (z : ℕ) (side : Fin 2) (P : MaskRestriction n) :
    let D := { (R.scheduleData h r hn hlog q hq).parentData side z with maskRestriction := P }
    D.footprint (representationBufferCapacity n) ≤
      inputScale R.input ^ 3 * compressionDictionaryCapacity n := by
  dsimp only
  let D := { (R.scheduleData h r hn hlog q hq).parentData side z with maskRestriction := P }
  let u := inputScale R.input
  let C := compressionDictionaryCapacity n
  have hL : ∀ j, (D.pair j).leftArray.size ≤ D.capacity := by
    intro j
    exact (R.schedule_pair_capacity h r hn hlog hscale q hq z side P j).1
  have hR : ∀ j, (D.pair j).storedRight.size ≤ D.capacity := by
    intro j
    exact (R.schedule_pair_capacity h r hn hlog hscale q hq z side P j).2
  have hf := D.footprint_le (representationBufferCapacity n) hL hR
    (representationBufferCapacity_le n)
  have hnu : n ≤ u := by unfold u inputScale; omega
  have hu : 10000 ≤ u := hn.trans hnu
  have hC : 1 ≤ C := by
    unfold C compressionDictionaryCapacity
    exact Nat.one_le_two_pow
  have hw : WeightEncoding.entryWidth D.input ≤ 3 * u + 1 :=
    (WeightEncoding.widths_le R.input).2
  have ha : 12 * n + 32 ≤ 44 * u := by omega
  have hb : 6 * D.capacity + 4 ≤ 10 * C := by change 6 * C + 4 ≤ _; omega
  have hc : 12 * n + 16 ≤ 28 * u := by omega
  have hd : n + 2 + 3 * (WeightEncoding.entryWidth D.input + 1) ≤ 18 * u := by omega
  have he : D.capacity + 1 ≤ 2 * C := by change C + 1 ≤ _; omega
  have hfirst := Nat.mul_le_mul_left 6 (Nat.mul_le_mul ha hb)
  have hsecond := Nat.mul_le_mul_right C hc
  have hthird := Nat.mul_le_mul hd he
  change 6 * ((12 * n + 32) * (6 * C + 4)) ≤ 6 * (44 * u * (10 * C)) at hfirst
  change (n + 2 + 3 * (WeightEncoding.entryWidth D.input + 1)) * (C + 1) ≤
    18 * u * (2 * C) at hthird
  have hsmall : D.footprint (representationBufferCapacity n) ≤ 2704 * u * C := by
    change D.footprint (representationBufferCapacity n) ≤ _ at hf ⊢
    change 6 * (12 * n + 32) * (6 * C + 4) + (12 * n + 16) * C +
      (n + 2 + 3 * (WeightEncoding.entryWidth D.input + 1)) * (C + 1) ≥ _ at hf
    nlinarith only [hf, hfirst, hsecond, hthird]
  show D.footprint (representationBufferCapacity n) ≤ u ^ 3 * C
  apply hsmall.trans
  have hsq : 2704 ≤ u ^ 2 := by nlinarith only [hu]
  have hm := Nat.mul_le_mul_right (u * C) hsq
  simpa only [pow_succ, pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hm

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
