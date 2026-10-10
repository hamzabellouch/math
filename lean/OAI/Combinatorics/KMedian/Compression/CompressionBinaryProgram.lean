import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryRepeat
import OAI.Combinatorics.KMedian.Compression.CompressionBounds
import OAI.Combinatorics.KMedian.Programs.RationalFeatureProgram

namespace OAI


                                                
section
namespace MetricKMedian.IntegerLaw.BinaryCompression
open Binary Binary.PolyProgram Function Polynomial

noncomputable def countProgram : PolyProgram Input.encode Nat.bits Input.n :=
  ((lawProgram.comp (snd Signed.encode er)).comp (listLength Signed.encode 0)).congr _
    (fun I => by simp only [Function.comp_apply,Input.lawData,List.length_ofFn])

noncomputable def iterateProgram : PolyProgram Input.encode Input.encode
    (fun I => Input.step^[I.n] I) :=
  stepProgram.repeatFrom (identity Input.encode) countProgram X statePolynomial
    (fun I => by simpa using (input_bounds I).1) (fun I i hi => state_size I i hi)

def Input.compressed (I : Input) : LawData :=
  let ν := compressStepsAuto I.v I.n I.μ
  (ν.denominator,List.ofFn ν.numerator)

noncomputable def compressProgram : PolyProgram Input.encode el Input.compressed :=
  (iterateProgram.comp lawProgram).congr _ (fun I => by
    simp only [Function.comp_apply,input_iterate,Input.lawData,Input.compressed,compressSteps_eq_iterate])

def RationalInput.compressed (I : RationalInput) : LawData :=
  ( (I.μ.compressAuto I.v).denominator, List.ofFn (I.μ.compressAuto I.v).numerator)

noncomputable def rationalCompressProgram : PolyProgram RationalInput.encode el RationalInput.compressed :=
  (integerInputProgram.comp compressProgram).congr _ (fun _ => rfl)

theorem rationalCompress_binary_polytime :
    Nonempty (Turing.TM2ComputableInPolyTime RationalInput.encode el RationalInput.compressed) :=
  ⟨rationalCompressProgram.stock⟩

theorem rationalCompress_finite_work : ∀ k : rationalCompressProgram.machine.K,
    Finite (rationalCompressProgram.machine.tm.Γ k) := rationalCompressProgram.finite_work

end MetricKMedian.IntegerLaw.BinaryCompression
end

end OAI
