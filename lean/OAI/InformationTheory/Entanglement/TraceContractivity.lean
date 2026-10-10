import OAI.InformationTheory.Entanglement.DensityChange

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

lemma traceNorm_jordan {A : Mat n} (hA : A.IsHermitian) :
    traceNorm A=(Matrix.trace (posPart A)).re+(Matrix.trace (negPart A)).re := by
  change (Matrix.trace (CFC.abs A)).re=_
  rw [← CFC.posPart_add_negPart A hA,Matrix.trace_add,Complex.add_re]

theorem traceNorm_positive_channel (F : Map n m)
    (hF : ∀ {A : Mat n}, A.PosSemidef → (F A).PosSemidef)
    (hT : TracePreserving F) {A : Mat n} (hA : A.IsHermitian) :
    traceNorm (F A)≤traceNorm A := by
  have hp : (posPart A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg A)
  have hm : (negPart A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg A)
  calc
    traceNorm (F A)=traceNorm (F (posPart A)-F (negPart A)) := by
      rw [← map_sub, CFC.posPart_sub_negPart A hA]
    _ ≤ traceNorm (F (posPart A))+traceNorm (F (negPart A)) := traceNorm_sub_le _ _
    _ = (Matrix.trace (posPart A)).re+(Matrix.trace (negPart A)).re := by
      rw [traceNorm_of_psd (hF hp),traceNorm_of_psd (hF hm),hT,hT]
    _ = traceNorm A := (traceNorm_jordan hA).symm
lemma traceNorm_cptp (F : Map n m) (hF : CP F) (hT : TracePreserving F)
    {A : Mat n} (hA : A.IsHermitian) : traceNorm (F A)≤traceNorm A :=
  traceNorm_positive_channel F (fun h => cp_positive hF h) hT hA

end SecretKey

end

end OAI
