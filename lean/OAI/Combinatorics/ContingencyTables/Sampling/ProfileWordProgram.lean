import OAI.Combinatorics.ContingencyTables.Sampling.ProfileTrialProgram
import OAI.Combinatorics.ContingencyTables.Machines.BooleanChunkProgram

namespace OAI

/-! # Parsing the independent words of the physical outer trial -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

/-- The schedule contains the number of steps and the two step widths. -/
abbrev ProfileWordSchedule := (ℕ×ℕ)×ℕ
abbrev ProfileWordInput := ProfileWordSchedule×List Bool

def splitProfileWord (z : ℕ×List Bool) : ProfileWord := (z.2.take z.1,z.2.drop z.1)
def splitProfileWordRealizer : Realizer splitProfileWord :=
  pair (composition (pair second first) takeFast) (composition (pair second first) dropFast)

theorem polynomial_splitProfileWord : PolynomialTime splitProfileWordRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_takeFast)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_dropFast)

def profileWordWidth (z : ProfileWordInput) : ℕ := z.1.1.2+z.1.2
def profileWordWidthRealizer : Realizer profileWordWidth :=
  composition (pair (composition (composition first first) second) (composition first second)) add

theorem polynomial_profileWordWidth : PolynomialTime profileWordWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_add

def profileWalkWidth (z : ProfileWordInput) : ℕ := z.1.1.1*profileWordWidth z
def profileWalkWidthRealizer : Realizer profileWalkWidth :=
  composition (pair (composition (composition first first) first) profileWordWidthRealizer) multiply

theorem polynomial_profileWalkWidth : PolynomialTime profileWalkWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_profileWordWidth) polynomial_multiply

def profileWalkChunks (z : ProfileWordInput) : List (List Bool) :=
  wordChunks (profileWordWidth z,z.2.take (profileWalkWidth z))
def profileWalkChunksRealizer : Realizer profileWalkChunks :=
  composition (pair profileWordWidthRealizer
    (composition (pair second profileWalkWidthRealizer) takeFast)) wordChunksRealizer

theorem polynomial_profileWalkChunks : PolynomialTime profileWalkChunksRealizer :=
  polynomial_composition (polynomial_pair polynomial_profileWordWidth
    (polynomial_composition (polynomial_pair polynomial_second polynomial_profileWalkWidth)
      polynomial_takeFast)) polynomial_wordChunks

def profileWalkWords (z : ProfileWordInput) : List ProfileWord :=
  (profileWalkChunks z).map (fun bits => splitProfileWord (z.1.1.2,bits))
def profileWalkWordsRealizer : Realizer profileWalkWords :=
  composition (pair (composition (composition first first) second) profileWalkChunksRealizer)
    (mapWith splitProfileWordRealizer)

theorem polynomial_profileWalkWords : PolynomialTime profileWalkWordsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    polynomial_profileWalkChunks) (polynomial_mapWith polynomial_splitProfileWord)

def profileTerminalWord (z : ProfileWordInput) : List Bool := z.2.drop (profileWalkWidth z)
def profileTerminalWordRealizer : Realizer profileTerminalWord :=
  composition (pair second profileWalkWidthRealizer) dropFast

theorem polynomial_profileTerminalWord : PolynomialTime profileTerminalWordRealizer :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_profileWalkWidth) polynomial_dropFast

abbrev PackedProfileTrial := (ProfileConfiguration×ProfileWordSchedule)×List Bool

def profileTrialWords (z : PackedProfileTrial) : ProfileWordInput := (z.1.2,z.2)
def profileTrialWordsRealizer : Realizer profileTrialWords := pair (composition first second) second

theorem polynomial_profileTrialWords : PolynomialTime profileTrialWordsRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second

def prepareProfileTrial (z : PackedProfileTrial) : ProfileTrialData :=
  ((z.1.1,profileWalkWords (profileTrialWords z)),profileTerminalWord (profileTrialWords z))
def prepareProfileTrialRealizer : Realizer prepareProfileTrial :=
  pair (pair (composition first first)
    (composition profileTrialWordsRealizer profileWalkWordsRealizer))
    (composition profileTrialWordsRealizer profileTerminalWordRealizer)

theorem polynomial_prepareProfileTrial : PolynomialTime prepareProfileTrialRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition polynomial_profileTrialWords polynomial_profileWalkWords))
    (polynomial_composition polynomial_profileTrialWords polynomial_profileTerminalWord)

def packedProfileTrial (z : PackedProfileTrial) : Option MatrixCode := profileTrial (prepareProfileTrial z)
def packedProfileTrialRealizer : Realizer packedProfileTrial :=
  composition prepareProfileTrialRealizer profileTrialRealizer

theorem polynomial_packedProfileTrial : PolynomialTime packedProfileTrialRealizer :=
  polynomial_composition polynomial_prepareProfileTrial polynomial_profileTrial

open FairBits GridBoundary
open scoped Classical
noncomputable section

lemma splitProfileWord_ofFn {s f : ℕ} (bits : Fin (s+f) → Bool) :
    splitProfileWord (s,List.ofFn bits)=
      (List.ofFn (splitWordEquiv s f bits).1,List.ofFn (splitWordEquiv s f bits).2) :=
  Prod.ext (ofFn_split_take bits) (ofFn_split_drop bits)

lemma profileWalkWords_ofFn {n s f : ℕ} (hw : 0<s+f)
    (bits : Fin (n*(s+f)+f) → Bool) :
    profileWalkWords (((n,s),f),List.ofFn bits)=List.ofFn (fun i : Fin n =>
      let word := gridWordEquiv n (s+f) (splitWordEquiv (n*(s+f)) f bits).1 i
      (List.ofFn (splitWordEquiv s f word).1,List.ofFn (splitWordEquiv s f word).2)) := by
  unfold profileWalkWords profileWalkChunks
  dsimp only [profileWordWidth,profileWalkWidth]
  rw [ofFn_split_take,wordChunks_ofFn hw,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact splitProfileWord_ofFn _

lemma profileTerminalWord_ofFn {n s f : ℕ} (bits : Fin (n*(s+f)+f) → Bool) :
    profileTerminalWord (((n,s),f),List.ofFn bits)=
      List.ofFn (splitWordEquiv (n*(s+f)) f bits).2 := ofFn_split_drop bits

end
end ContingencyTables.ProfilePrograms

end OAI
