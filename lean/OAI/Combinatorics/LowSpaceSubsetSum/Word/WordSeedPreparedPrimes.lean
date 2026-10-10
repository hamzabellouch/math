import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordLayoutPreparation
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedFactorExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedHistory

namespace OAI

/-! # Prime draws from the counted layout preparation

The widths passed to the sampler are stored integers returned by the mixer
counting procedure. Equalities with ideal parameters are type transports.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

variable {n : ℕ}

private theorem nested_width (I : Instance n) (a : WordLayoutPreparation.Layout I)
    (d : WordLayoutPreparation.Prepared I a) (i : Fin 3) :
    d.val.parameters.widths[i.val] =
      (canonicalRepresentationData I).zeroSetup.factorExponents a.value i := by
  have h := (WordLayoutPreparation.fields I a d).2
  fin_cases i
  · simpa [RepresentationSetup.samplerPrimeWidths] using h 0
  · simpa [RepresentationSetup.samplerPrimeWidths] using h 1
  · simpa [RepresentationSetup.samplerPrimeWidths] using h 2

def nestedAtWidths (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (x y q : ℕ) (hx : x = R.factorExponents z 0)
    (hy : y = R.factorExponents z 1) (hq : q = R.factorExponents z 2)
    (w : ℕ) (hw : n ≤ w) : Execution (WordSeedRealization.nested R z w hw) := by
  have bx : x ≤ w := (le_of_eq hx).trans ((R.factorExponents_le_n z 0).trans hw)
  have by' : y ≤ w := (le_of_eq hy).trans ((R.factorExponents_le_n z 1).trans hw)
  have bq : q ≤ w := (le_of_eq hq).trans ((R.factorExponents_le_n z 2).trans hw)
  let E := triplePrime w n x y q bx by' bq
  cases hx
  cases hy
  cases hq
  exact E

def nestedFromPrepared (I : Instance n) (a : WordLayoutPreparation.Layout I)
    (d : WordLayoutPreparation.Prepared I a) (w : ℕ) (hw : n ≤ w) :
    Execution (WordSeedRealization.nested (canonicalRepresentationData I).zeroSetup a.value w hw) :=
  nestedAtWidths _ a.value d.val.parameters.widths[0] d.val.parameters.widths[1]
    d.val.parameters.widths[2] (nested_width I a d 0) (nested_width I a d 1)
    (nested_width I a d 2) w hw

def nestedPrepared (I : Instance n) (a : WordLayoutPreparation.Layout I)
    (w : ℕ) (hw : n ≤ w) :
    Execution (WordSeedRealization.nested (canonicalRepresentationData I).zeroSetup a.value w hw) :=
  prepareThen (fun _ => WordLayoutPreparation.compute I a)
    (fun d => nestedFromPrepared I a d w hw)

private theorem extra_width (I : Instance n) (a : WordLayoutPreparation.Layout I)
    (d : WordLayoutPreparation.Prepared I a) :
    d.val.parameters.widths[3] =
      (canonicalRepresentationData I).zeroSetup.extraPrimeParameter a.value := by
  simpa [RepresentationSetup.samplerPrimeWidths] using
    (WordLayoutPreparation.fields I a d).2 3

def extraAtWidth (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (x : ℕ) (hx : x = R.extraPrimeParameter z) (hn : 100 ≤ n) (w : ℕ) (hw : n ≤ w) :
    Execution (WordSeedRealization.extraPrime R z hn w hw) := by
  have hr := R.extraPrimeParameter_range z hn
  have lo : 4 ≤ x := hr.1.trans (le_of_eq hx.symm)
  have hi : x ≤ w := (le_of_eq hx).trans (hr.2.trans hw)
  let E := primeInitialized w n x lo hi
  cases hx
  exact E

def extraFromPrepared (I : Instance n) (a : WordLayoutPreparation.Layout I)
    (d : WordLayoutPreparation.Prepared I a) (hn : 100 ≤ n) (w : ℕ) (hw : n ≤ w) :
    Execution (WordSeedRealization.extraPrime (canonicalRepresentationData I).zeroSetup
      a.value hn w hw) :=
  extraAtWidth _ a.value d.val.parameters.widths[3] (extra_width I a d) hn w hw

def extraPrepared (I : Instance n) (a : WordLayoutPreparation.Layout I)
    (hn : 100 ≤ n) (w : ℕ) (hw : n ≤ w) :
    Execution (WordSeedRealization.extraPrime (canonicalRepresentationData I).zeroSetup
      a.value hn w hw) :=
  prepareThen (fun _ => WordLayoutPreparation.compute I a)
    (fun d => extraFromPrepared I a d hn w hw)

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
