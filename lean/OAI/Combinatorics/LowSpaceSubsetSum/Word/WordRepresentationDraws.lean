import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordPrimeRealization
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorSamplerCoupling

namespace OAI

/-! # Word programs for signs, fixed-size samples, and separator families -/

noncomputable section
namespace LowSpaceSubsetSum.WordRealization

def bits (w n : ℕ) (hw : 1 ≤ w) : Realization w n (bitArrayCoupling n) where
  program := WordProgram.map
    (fun f => some (fun i => finTwoEquiv (ExactWordDraw.low w 1 (f i)))) (WordTuple.sample n)
  faithful P := by
    rw [WordProgram.probability_map, WordTuple.probability]
    rw [ExactWordDraw.uniform_tuple w 1 hw n
      (fun f => P (some (fun i => finTwoEquiv (f i))))]
    let e : (Fin n → Fin 2) ≃ (Fin n → Bool) :=
      Equiv.piCongrRight (fun _ => finTwoEquiv)
    have he := FiniteLaw.map_equiv_uniform e
    change (FiniteLaw.uniform : FiniteLaw (Fin n → Fin 2)).probability
      (fun f => P (some (e f))) = _
    have hp := congrArg (fun μ : FiniteLaw (Fin n → Bool) =>
      μ.probability (fun f => P (some f))) he
    rw [FiniteLaw.map_probability] at hp
    apply hp.trans
    change (FiniteLaw.uniform : FiniteLaw (Fin n → Bool)).probability (fun f => P (some f)) =
      ((FiniteLaw.uniform : FiniteLaw (Fin n → Bool)).map some).probability P
    rw [FiniteLaw.map_probability]
  bounded := by
    simpa only [WordProgram.map, Nat.add_zero] using
      WordProgram.bind_bound (WordTuple.sample (w := w) n) n (WordTuple.bounded n)
        (fun f => .pure (some (fun i => finTwoEquiv (ExactWordDraw.low w 1 (f i))))) 0
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
      (2 * RepresentationSetup.blockHalf n i)) ≤ w) :
    Realization w ((RepresentationSetup.blockCount i *
      (2 * RepresentationSetup.blockHalf n i))*n^3) (CanonicalPartition.coupling R z i) :=
  map (map (permutation w n _ hw) (Equiv.permCongr (CanonicalPartition.ranks R z i).symm))
    (coloringOfPermutation (CanonicalPartition.base R z i))

end LowSpaceSubsetSum.WordRealization

end

end OAI
