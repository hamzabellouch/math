import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedBitsExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedPermutationExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedHistory

namespace OAI

/-! # Measured structural draws in a representation history

Permutation composition and balanced-coloring maps create closures. These
closures are not applied during the next prime draw; the prepared action
later materializes all queried coordinates with its own counted routines.
The guess encoding performs its explicit endpoint arithmetic.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

variable {n : ℕ}

def layout (R : RepresentationSetup n) (w : ℕ)
    (hp : Nat.clog 2 n ≤ w) (hb : 1 ≤ w) :
    Execution (WordSeedRealization.layout R w hp hb) :=
  prod (permutation w n n hp) (signs w n hb)

def guesses (R : RepresentationSetup n) (w : ℕ)
    (hw : Nat.clog 2 (CanonicalGuesses.width n) ≤ w) :
    Execution (WordSeedRealization.guesses R w hw) :=
  pi w (n^3) 3 _ _ _ (fun _ =>
    map (fin w n (CanonicalGuesses.width n) hw) (CanonicalGuesses.encoding n)
      (fun a => ((CanonicalGuesses.encode n a,12),4)) (fun _ => rfl))

def partition (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (i : Fin 3) (w : ℕ)
    (hw : Nat.clog 2 (RepresentationSetup.blockCount i *
      (2*RepresentationSetup.blockHalf n i)) ≤ w) :
    Execution (WordSeedRealization.partition R z i w hw) :=
  map (map (permutation w n _ hw) (Equiv.permCongr (CanonicalPartition.ranks R z i).symm)
    (fun p => (((Equiv.permCongr (CanonicalPartition.ranks R z i).symm) p,2),4))
    (fun _ => rfl)) (coloringOfPermutation (CanonicalPartition.base R z i))
      (fun p => (((coloringOfPermutation (CanonicalPartition.base R z i)) p,2),4))
      (fun _ => rfl)

private theorem clog_le (k w : ℕ) (h : k ≤ w) : Nat.clog 2 k ≤ w :=
  (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)).trans h

def partitions (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (w : ℕ) (hw : n ≤ w) :
    Execution (WordSeedRealization.partitions R z w hw) :=
  pi w (n*n^3) 3 _ _ _ (fun i => by
    have hs : RepresentationSetup.blockCount i*(2*RepresentationSetup.blockHalf n i) ≤ n := by
      rw [←CanonicalPartition.size_eq R z i]
      simpa only [Fintype.card_fin] using Finset.card_le_univ (R.orderedMixers z i)
    exact enlarge (partition R z i w (clog_le _ _ (hs.trans hw)))
      (Nat.mul_le_mul_right _ hs))

theorem layout_bounded (R : RepresentationSetup n) (w : ℕ)
    (hp : Nat.clog 2 n ≤ w) (hb : 1 ≤ w) :
    (layout R w hp hb).Bounded
      ((n+1)*(30*n^3+100*n+1000)) ((n+1)*(30*n^3+100*n+1000))
      ((n+1)*(30*n^3+100*n+1000)) := by
  have h := prod_bounded (permutation w n n hp) (signs w n hb) _ _ _ _ _ _
    (permutation_bounded w n n hp) (signs_bounded w n hb)
  intro stream cursor
  have ht := h stream cursor
  refine ⟨ht.1.trans (by nlinarith),ht.2.1.trans ?_,ht.2.2.trans (by nlinarith)⟩
  apply max_le
  · apply max_le <;> nlinarith
  · nlinarith

theorem guesses_bounded (R : RepresentationSetup n) (w : ℕ)
    (hw : Nat.clog 2 (CanonicalGuesses.width n) ≤ w) :
    (guesses R w hw).Bounded (2000*(n+1)^4) (2000*(n+1)^4) (2000*(n+1)^4) := by
  have hc : Nat.clog 2 (CanonicalGuesses.width n) ≤ n+1 := by
    apply Nat.clog_le_of_le_pow
    apply (show CanonicalGuesses.width n ≤ n+1 by
      unfold CanonicalGuesses.width CanonicalGuesses.upper CanonicalGuesses.lower mixerSize
      omega).trans
    exact Nat.lt_two_pow_self.le
  have hm := map_bounded (fin w n (CanonicalGuesses.width n) hw)
    (CanonicalGuesses.encoding n) (fun a => ((CanonicalGuesses.encode n a,12),4))
    (fun _ => rfl) _ _ _ 12 4 (fin_bounded w n (CanonicalGuesses.width n) hw)
    (fun _ => le_rfl) (fun _ => le_rfl)
  have hp := pi_bounded w (n^3) 3 _ _ _ _
    (13*n^3+5*Nat.clog 2 (CanonicalGuesses.width n)+31)
    (3*n^3+134) (n^3+30) (fun _ stream cursor => by
      have h := hm stream cursor
      exact ⟨h.1,h.2.1.trans (by omega),h.2.2⟩)
  intro stream cursor
  have h := hp stream cursor
  have h3 : n^3 ≤ (n+1)^4 :=
    (Nat.pow_le_pow_left (by omega : n ≤ n+1) 3).trans
      (Nat.pow_le_pow_right (by omega : 0 < n+1) (by decide : 3 ≤ 4))
  have h1 : n ≤ (n+1)^4 := by
    exact (show n ≤ n+1 by omega).trans (by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < n+1) (by decide : 1 ≤ 4))
  have hB : 1 ≤ (n+1)^4 := Nat.one_le_pow _ _ (by omega)
  refine ⟨h.1.trans ?_,h.2.1.trans ?_,h.2.2.trans ?_⟩ <;>
    nlinarith only [hc,h3,h1,hB]

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
