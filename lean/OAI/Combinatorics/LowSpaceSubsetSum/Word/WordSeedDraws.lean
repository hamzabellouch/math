import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedPrimitives
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordRepresentationDraws

namespace OAI

/-! # Successful seeds for signs, partitions and separator families -/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedRealization

def bitsSeed (n : ℕ) (f : Fin n → Bool) : SuccessfulSeed (bitArrayCoupling n) :=
  ⟨f,f,rfl⟩

def bits (w n : ℕ) (hw : 1 ≤ w) : Realization w n (bitArrayCoupling n) where
  program := WordProgram.map
    (fun f => some (bitsSeed n (fun i => finTwoEquiv (ExactWordDraw.low w 1 (f i)))))
    (WordTuple.sample n)
  faithful P := by
    have he : WordProgram.map (observe (bitArrayCoupling n))
        (WordProgram.map
          (fun f => some (bitsSeed n (fun i => finTwoEquiv (ExactWordDraw.low w 1 (f i)))))
          (WordTuple.sample n)) = (WordRealization.bits w n hw).program := by
      rw [map_map]
      rfl
    rw [he]
    exact (WordRealization.bits w n hw).faithful P
  bounded := by
    simpa only [WordProgram.map,Nat.add_zero] using
      WordProgram.bind_bound (WordTuple.sample (w := w) n) n (WordTuple.bounded n)
        (fun f => .pure (some (bitsSeed n
          (fun i => finTwoEquiv (ExactWordDraw.low w 1 (f i)))))) 0
        (fun _ => WordProgram.Bounded.pure _ 0)

def signs (w n : ℕ) (hw : 1 ≤ w) : Realization w n (signCoupling n) :=
  map (bits w n hw) (bitsSubsetEquiv n)

def subset (w n g : ℕ) (K : Finset (Fin g)) (hw : Nat.clog 2 g ≤ w) :
    Realization w (g*n^3) (subsetCoupling n g K) :=
  map (permutation w n g hw) (permutationBlock K)

def fixedSize (w n g e : ℕ) (he : e ≤ g) (hw : Nat.clog 2 g ≤ w) :
    Realization w (g*n^3) (fixedSizeCoupling n g e he) :=
  map (subset w n g (initialSubset g e he) hw) (initialSubsetEquiv g e he)

def families {g : ℕ} (S : SeparatorExpectation.RoundedParameters g)
    (w n : ℕ) (hw : Nat.clog 2 g ≤ w) :
    Realization w (4*(11*2^g*(g*n^3))) (S.samplerCoupling n) :=
  pi w (11*2^g*(g*n^3)) 4 _ _ (fun i =>
    enlarge (pi w (g*n^3) (S.counts i) _ _
      (fun _ => fixedSize w n g (S.e i) (S.size_le i) hw))
      (Nat.mul_le_mul_right _ (S.counts_le i)))

def layout {n : ℕ} (R : RepresentationSetup n) (w : ℕ)
    (hp : Nat.clog 2 n ≤ w) (hb : 1 ≤ w) :
    Realization w (n*n^3+n) R.layoutCoupling :=
  prod (permutation w n n hp) (signs w n hb)

def guesses {n : ℕ} (R : RepresentationSetup n) (w : ℕ)
    (hw : Nat.clog 2 (CanonicalGuesses.width n) ≤ w) :
    Realization w (3*n^3) R.guessesCoupling :=
  pi w (n^3) 3 _ _ (fun _ => map (fin w n (CanonicalGuesses.width n) hw)
    (CanonicalGuesses.encoding n))

def partition {n : ℕ} (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (i : Fin 3) (w : ℕ)
    (hw : Nat.clog 2 (RepresentationSetup.blockCount i *
      (2*RepresentationSetup.blockHalf n i)) ≤ w) :
    Realization w ((RepresentationSetup.blockCount i *
      (2*RepresentationSetup.blockHalf n i))*n^3) (CanonicalPartition.coupling R z i) :=
  map (map (permutation w n _ hw) (Equiv.permCongr (CanonicalPartition.ranks R z i).symm))
    (coloringOfPermutation (CanonicalPartition.base R z i))

end LowSpaceSubsetSum.WordSeedRealization

end

end OAI
