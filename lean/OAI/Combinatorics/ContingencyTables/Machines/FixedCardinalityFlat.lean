import OAI.Combinatorics.ContingencyTables.Machines.FixedCardinalityFold
import OAI.Combinatorics.ContingencyTables.Machines.FixedCardinalityMixture
import OAI.Combinatorics.ContingencyTables.Machines.BooleanChunkProgram

namespace OAI

/-! # A flat-word program for a local initial subset

The first B bits select the size. The remaining word is partitioned
into B-bit inclusion rows, so the input list bounds the number of loop
iterations even on malformed inputs.
-/

namespace ContingencyTables.FixedCardinalityProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms

abbrev SubsetInput := (ℕ×ℕ)×List Bool

def subsetCode (z : SubsetInput) : List Bool :=
  drawWords ((z.1.1,scaledWordValue (z.1.1+1,z.2.take z.1.2)),
    wordChunks (z.1.2,z.2.drop z.1.2))

def subsetCodeRealizer : Realizer subsetCode := by
  let N : Realizer (fun z : SubsetInput => z.1.1) := composition first first
  let B : Realizer (fun z : SubsetInput => z.1.2) := composition first second
  let head := composition (pair second B) takeFast
  let size := composition (pair (composition N successor) head) scaledWordRealizer
  let rest := composition (pair second B) dropFast
  let chunks := composition (pair B rest) wordChunksRealizer
  exact composition (pair (pair N size) chunks) drawWordsRealizer

theorem polynomial_subsetCode : PolynomialTime subsetCodeRealizer := by
  unfold subsetCodeRealizer
  have hn : PolynomialTime (composition
      (first (A := ℕ×ℕ) (B := List Bool)) first) :=
    polynomial_composition polynomial_first polynomial_first
  have hb : PolynomialTime (composition
      (first (A := ℕ×ℕ) (B := List Bool)) second) :=
    polynomial_composition polynomial_first polynomial_second
  exact polynomial_composition (polynomial_pair
    (polynomial_pair hn (polynomial_composition
      (polynomial_pair (polynomial_composition hn polynomial_successor)
        (polynomial_composition (polynomial_pair polynomial_second hb) polynomial_takeFast))
      polynomial_scaledWord))
    (polynomial_composition (polynomial_pair hb
      (polynomial_composition (polynomial_pair polynomial_second hb) polynomial_dropFast))
      polynomial_wordChunks)) polynomial_drawWords

noncomputable section
open FairBits FixedCardinalityBits FixedCardinalityMixture

lemma splitWord_append (B L : ℕ) (bits : Fin (B+L) → Bool) :
    List.ofFn bits=List.ofFn (splitWordEquiv B L bits).1++List.ofFn (splitWordEquiv B L bits).2 := by
  have hfirst : (splitWordEquiv B L bits).1=fun i => bits (Fin.castAdd L i) := by
    funext i
    apply congrArg bits
    apply Fin.ext
    rfl
  have hsecond : (splitWordEquiv B L bits).2=fun i => bits (Fin.natAdd B i) := by
    funext i
    apply congrArg bits
    apply Fin.ext
    rfl
  rw [hfirst,hsecond]
  exact List.ofFn_add (f := bits)

lemma splitWord_take (B L : ℕ) (bits : Fin (B+L) → Bool) :
    (List.ofFn bits).take B=List.ofFn (splitWordEquiv B L bits).1 := by
  rw [splitWord_append]
  simp

lemma splitWord_drop (B L : ℕ) (bits : Fin (B+L) → Bool) :
    (List.ofFn bits).drop B=List.ofFn (splitWordEquiv B L bits).2 := by
  rw [splitWord_append]
  simp

private theorem subsetCode_ofFn_raw (B n : ℕ) (hB : 0<B)
    (bits : Fin (B+n*B) → Bool) :
    subsetCode ((n,B),List.ofFn bits)=List.ofFn (vectorDraw B n bits) := by
  unfold subsetCode
  dsimp only
  rw [splitWord_take,splitWord_drop,scaledWordValue_ofFn (n+1) B (Nat.succ_pos n)]
  rw [wordChunks_ofFn hB,drawWords_ofFn]
  rfl

/-- Every local subset output bit agrees with the finite-word draw
with the sequential subset law. -/
theorem subsetCode_ofFn (B n : ℕ) (hB : 0<B)
    (bits : Fin (drawBits B n) → Bool) :
    subsetCode ((n,B),List.ofFn bits)=List.ofFn (vectorDraw B n bits) :=
  subsetCode_ofFn_raw B n hB bits

end
end ContingencyTables.FixedCardinalityProgram

end OAI
