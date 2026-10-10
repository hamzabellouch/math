import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedFiniteBounds
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedStructuralExecution

namespace OAI

/-! # Polynomial envelopes for the structural history draws

These bounds charge measured permutation generation and the actual constant
size tuple/closure constructors. Materialization is charged by the later
preparation stage.
-/

namespace LowSpaceSubsetSum.WordSeedStructuralBounds

open WordSeedMeasured WordSeedScalarBounds

variable {n : ℕ}

private theorem self_le_power {u k : ℕ} (hu : 1 ≤ u) (hk : 1 ≤ k) : u ≤ u^k := by
  simpa only [Nat.pow_one] using Nat.pow_le_pow_right hu hk

private theorem coefficient_power {u c k : ℕ} (hc : c ≤ u) : c*u^k ≤ u^(k+1) := by
  simpa only [Nat.pow_succ,Nat.mul_comm] using Nat.mul_le_mul_right (u^k) hc

private theorem additive_slack {u : ℕ} (hu : 10000 ≤ u) : u^5+24 ≤ u^6 := by
  have hp : u ≤ u^5 := self_le_power (by omega) (by decide)
  have hs : 2*u^5 ≤ u^6 := coefficient_power (by omega)
  omega

private theorem triple_slack {u : ℕ} (hu : 10000 ≤ u) : 8*u^6+256 ≤ u^7 := by
  have hp : u ≤ u^6 := self_le_power (by omega) (by decide)
  have hs : 9*u^6 ≤ u^7 := coefficient_power (by omega)
  omega

private theorem layout_numeric {n u : ℕ} (hu : 10000 ≤ u) (hnu : n+2 ≤ u) :
    (n+1)*(30*n^3+100*n+1000) ≤ u^6 := by
  have hn3 : n^3 ≤ u^3 := Nat.pow_le_pow_left (by omega) 3
  have hu3 : u ≤ u^3 := self_le_power (by omega) (by decide)
  have hinner : 30*n^3+100*n+1000 ≤ 1130*u^3 := by nlinarith
  calc
    _ ≤ u*(1130*u^3) := Nat.mul_le_mul (by omega) hinner
    _ = 1130*u^4 := by ring
    _ ≤ u^5 := coefficient_power (by omega)
    _ ≤ u^6 := Nat.pow_le_pow_right (by omega) (by decide)

private theorem guesses_numeric {n u : ℕ} (hu : 10000 ≤ u) (hnu : n+2 ≤ u) :
    2000*(n+1)^4 ≤ u^6 := by
  calc
    _ ≤ 2000*u^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
    _ ≤ u^5 := coefficient_power (by omega)
    _ ≤ u^6 := Nat.pow_le_pow_right (by omega) (by decide)

theorem layout_bounded_scale (I : Instance n) (hn : 10000 ≤ n)
    (R : RepresentationSetup n) (w : ℕ) (hp : Nat.clog 2 n ≤ w) (hb : 1 ≤ w) :
    (layout R w hp hb).Bounded (inputScale I^6) (inputScale I^6) (inputScale I^6) := by
  have h := layout_numeric (n := n) (u := inputScale I)
    (by unfold inputScale; omega) (by unfold inputScale; omega)
  exact bounded_mono _ (layout_bounded R w hp hb) h h h

theorem guesses_bounded_scale (I : Instance n) (hn : 10000 ≤ n)
    (R : RepresentationSetup n) (w : ℕ) (hw : Nat.clog 2 (CanonicalGuesses.width n) ≤ w) :
    (guesses R w hw).Bounded (inputScale I^6) (inputScale I^6) (inputScale I^6) := by
  have h := guesses_numeric (n := n) (u := inputScale I)
    (by unfold inputScale; omega) (by unfold inputScale; omega)
  exact bounded_mono _ (guesses_bounded R w hw) h h h

theorem block_size_le (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (i : Fin 3) : RepresentationSetup.blockCount i*(2*RepresentationSetup.blockHalf n i) ≤ n := by
  rw [←CanonicalPartition.size_eq R z i]
  simpa only [Fintype.card_fin] using Finset.card_le_univ (R.orderedMixers z i)

theorem partition_bounded_scale (I : Instance n) (hn : 10000 ≤ n)
    (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (i : Fin 3) (w : ℕ)
    (hw : Nat.clog 2 (RepresentationSetup.blockCount i*
      (2*RepresentationSetup.blockHalf n i)) ≤ w) :
    (partition R z i w hw).Bounded (inputScale I^6) (inputScale I^6) (inputScale I^6) := by
  have hp := permutation_bounded_scale I hn (block_size_le R z i) w hw
  have h1 := map_bounded _ (Equiv.permCongr (CanonicalPartition.ranks R z i).symm)
    (fun p => (((Equiv.permCongr (CanonicalPartition.ranks R z i).symm) p,2),4))
    (fun _ => rfl) _ _ _ 2 4 hp (fun _ => le_rfl) (fun _ => le_rfl)
  have h2 := map_bounded _ (coloringOfPermutation (CanonicalPartition.base R z i))
    (fun p => (((coloringOfPermutation (CanonicalPartition.base R z i)) p,2),4))
    (fun _ => rfl) _ _ _ 2 4 h1 (fun _ => le_rfl) (fun _ => le_rfl)
  have hs := additive_slack (show 10000 ≤ inputScale I by unfold inputScale; omega)
  intro stream cursor
  have h := h2 stream cursor
  change _ ≤ inputScale I^6 ∧ _ ≤ inputScale I^6 ∧ _ ≤ inputScale I^6
  refine ⟨h.1.trans (by omega),h.2.1.trans (by omega),h.2.2.trans (by omega)⟩

theorem partitions_bounded_scale (I : Instance n) (hn : 10000 ≤ n)
    (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) (w : ℕ) (hw : n ≤ w) :
    (partitions R z w hw).Bounded (inputScale I^7) (inputScale I^7) (inputScale I^7) := by
  have hi (i : Fin 3) := block_size_le R z i
  let hwidth (i : Fin 3) : Nat.clog 2 (RepresentationSetup.blockCount i*
      (2*RepresentationSetup.blockHalf n i)) ≤ w :=
    (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le).trans ((hi i).trans hw)
  have hp := pi_bounded w (n*n^3) 3 (fun i => R.Partition z i)
    (fun i => CanonicalPartition.coupling R z i)
    (fun i => WordSeedRealization.enlarge (WordSeedRealization.partition R z i w (hwidth i))
      (Nat.mul_le_mul_right _ (hi i)))
    (fun i => enlarge (partition R z i w (hwidth i)) (Nat.mul_le_mul_right _ (hi i)))
    (inputScale I^6) (inputScale I^6) (inputScale I^6) (fun i =>
      enlarge_bounded _ _ _ _ _ (partition_bounded_scale I hn R z i w (hwidth i)))
  have hs := triple_slack (show 10000 ≤ inputScale I by unfold inputScale; omega)
  intro stream cursor
  have h := hp stream cursor
  change _ ≤ inputScale I^7 ∧ _ ≤ inputScale I^7 ∧ _ ≤ inputScale I^7
  exact ⟨h.1.trans (by omega),h.2.1.trans (by omega),h.2.2.trans (by omega)⟩

end LowSpaceSubsetSum.WordSeedStructuralBounds

end OAI
