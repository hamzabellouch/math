import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.RoundingMatrix
import OAI.Combinatorics.KMedianRecovery.Encoding.DuplicateMatrix
import OAI.Combinatorics.KMedianRecovery.Encoding.RationalConstants

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalization
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open IntegralAssembly (gammaRat)
def pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,List.replicate d true,BinaryRational.encode M]
noncomputable def count (x : List Bool) : List Bool := UnaryResources.lengthBits (field 2 x)
noncomputable def count_computes : PolyComputes count := (field_computes 2).comp UnaryResources.lengthBits_computes
noncomputable def mesh (x : List Bool) : List Bool := BinaryRational.encode
  ((gammaRat/16)*BinaryRational.decode (field 3 x)/(value (count x):ℚ))
noncomputable def mesh_computes : PolyComputes mesh :=
  RatOps.div (RatOps.mul (RatOps.const (gammaRat/16)) (RatOps.ofWords (field_computes 3))) (RatOps.nat count_computes)
noncomputable def capArgument (x : List Bool) : List Bool := BinaryRational.encode
  (20*(value (count x):ℚ)*(value (count x):ℚ)/(gammaRat/16))
noncomputable def capArgument_computes : PolyComputes capArgument :=
  RatOps.div (RatOps.mul (RatOps.mul (RatOps.const 20) (RatOps.nat count_computes)) (RatOps.nat count_computes))
    (RatOps.const (gammaRat/16))
noncomputable def cap (x : List Bool) : List Bool :=
  (⌈BinaryRational.decode (capArgument x)⌉₊+1).bits
noncomputable def cap_computes : PolyComputes cap := by
  change PolyComputes (fun x=>(⌈BinaryRational.decode (capArgument x)⌉₊+1).bits)
  simpa only [value_bits] using NatOps.add (RatOps.natCeil (RatOps.ofWords capArgument_computes)) (const_computes (1:ℕ).bits)
noncomputable def roundingInput (x : List Bool) : List Bool :=
  encode [BinaryDuplicateMatrix.run (field 0 x),BinaryDuplicateMatrix.twice (field 1 x),mesh x,cap x]
noncomputable def roundingInput_computes : PolyComputes roundingInput := by
  unfold roundingInput
  have computes := cons_computes ((field_computes 0).comp BinaryDuplicateMatrix.run_computes)
    (cons_computes ((field_computes 1).comp BinaryDuplicateMatrix.twice_computes)
      (cons_computes mesh_computes (cons_computes cap_computes (const_computes []))))
  simpa only [Function.comp_def,encode] using computes
noncomputable def run : List Bool→List Bool := BinaryRoundingMatrix.run ∘ roundingInput
noncomputable def run_computes : PolyComputes run := roundingInput_computes.comp BinaryRoundingMatrix.run_computes
lemma count_pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) : count (pack δ d M)=d.bits := by
  simp only [count,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    UnaryResources.lengthBits_eq,List.length_replicate]
lemma mesh_pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) :
    mesh (pack δ d M)=BinaryRational.encode ((gammaRat/16)*M/d) := by
  rw [mesh,count_pack,value_bits]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryRational.decode_encode]
lemma cap_pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) :
    cap (pack δ d M)=(Rounding.cap d (IntegralAssembly.gamma/16)).bits := by
  simp only [cap,capArgument,count_pack,value_bits,BinaryRational.decode_encode,IntegralAssembly.cap_rat]
  congr 3
  ring
lemma roundingInput_pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) :
    roundingInput (pack δ d M)=BinaryRoundingMatrix.pack (BinaryDuplicateMatrix.duplicate δ)
      ((gammaRat/16)*M/d) (Rounding.cap d (IntegralAssembly.gamma/16)) := by
  rw [roundingInput,mesh_pack,cap_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryDuplicateMatrix.run_encode,BinaryDuplicateMatrix.twice,←List.replicate_add,BinaryRoundingMatrix.pack]
lemma run_pack {n : ℕ} (δ : Fin n→Fin n→ℚ) (d : ℕ) (M : ℚ) :
    run (pack δ d M)=RationalMatrix.encode
      (BinaryRoundingMatrix.round (BinaryDuplicateMatrix.duplicate δ) ((gammaRat/16)*M/d)
        (Rounding.cap d (IntegralAssembly.gamma/16))) := by
  rw [run,Function.comp_apply,roundingInput_pack,BinaryRoundingMatrix.run_pack]
end MetricKMedianRecovery.BitMachine.BinaryNormalization

end OAI
