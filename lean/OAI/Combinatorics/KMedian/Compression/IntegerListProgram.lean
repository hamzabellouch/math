import Mathlib
import OAI.Combinatorics.KMedian.Compression.RationalScaling
import OAI.Combinatorics.KMedian.Binary.BinaryListContext
import OAI.Combinatorics.KMedian.Binary.BinaryRationalFold

namespace OAI


                                          
section
namespace MetricKMedian.Binary
open PolyProgram Function
namespace IntegerList
abbrev Row := List ℤ
abbrev Rows := List Row
abbrev er := encodeList Signed.encode
abbrev em := encodeList er

def denominator (qs : List ℚ) : ℤ := (qs.map (fun q => (q.den:ℤ))).prod
def numerators (qs : List ℚ) : Row := qs.map (fun q => (q*(denominator qs:ℚ)).num)

theorem denominator_ofFn {n : ℕ} (q : Fin n → ℚ) :
    denominator (List.ofFn q)=RationalScaling.denominator q := by
  simp only [denominator,List.map_ofFn,List.prod_ofFn,Function.comp_def,RationalScaling.denominator]

theorem numerators_ofFn {n : ℕ} (q : Fin n → ℚ) :
    numerators (List.ofFn q)=List.ofFn (RationalScaling.numerator q) := by
  simp only [numerators,denominator_ofFn,List.map_ofFn,Function.comp_def]
  congr 1
  funext i
  rw [← RationalScaling.numerator_cast,Rat.num_intCast]

noncomputable def sumProgram : PolyProgram er Signed.encode List.sum :=
  (((ratOfInt.listMap 0).comp ratSum).comp ratNum).congr _ (fun xs => by
    simp only [Function.comp_apply,← Int.cast_list_sum,Rat.num_intCast])
noncomputable def prodProgram : PolyProgram er Signed.encode List.prod :=
  (((ratOfInt.listMap 0).comp ratProd).comp ratNum).congr _ (fun xs => by
    simp only [Function.comp_apply,← Int.cast_list_prod,Rat.num_intCast])
noncomputable def denominatorProgram : PolyProgram (encodeList Ratio.encode) Signed.encode denominator :=
  (((ratDen.comp intOfNat).listMap 0).comp prodProgram).congr _ (fun _ => rfl)
noncomputable def numeratorsProgram : PolyProgram (encodeList Ratio.encode) er numerators := by
  let mul := (exchange Ratio.encode Ratio.encode).comp ratMul
  let output := (((denominatorProgram.comp ratOfInt).fanout (identity (encodeList Ratio.encode))).comp ((mul.comp ratNum).listMapWith 0 0))
  exact output.congr _ (fun _ => rfl)

end IntegerList
end MetricKMedian.Binary
end

end OAI
