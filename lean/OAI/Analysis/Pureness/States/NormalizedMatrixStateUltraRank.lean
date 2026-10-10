import OAI.Analysis.Pureness.Quasitrace.ComplexQuasitraceBounds
import OAI.Analysis.Pureness.States.NormalizedMatrixStateDiagonal
import OAI.Analysis.Pureness.States.RegularizedStateCStarValue

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup Filter
open scoped Topology NNReal ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)
variable (U : Ultrafilter ℕ)

def normalizedMatrixStateAWValue : ComplexQuasitrace (NormalizedMatrixStateUltraAW hsimple y hy f U) :=
  ultralimitAWQuasitrace (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
    (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f)

lemma matrixStateDiagonalAWEmbedding_injective :
    Function.Injective (matrixStateDiagonalAWEmbedding hsimple y hy f U) := by
  intro a b hab
  let e := matrixStateDiagonalAWEmbedding hsimple y hy f U
  let z := a-b
  have hz : e z=0 := (map_sub e a b).trans (sub_eq_zero.mpr hab)
  have hv := matrixStateDiagonalAWEmbedding_value hsimple y hy f U (star z*z)
  have hzero := (normalizedMatrixStateAWValue hsimple y hy f U).map_zero
  have he : e (star z*z)=0 := by
    calc
      _ = star (e z)*e z := (map_mul e (star z) z).trans
        (congrArg₂ (·*·) (map_star e z) rfl)
      _ = 0 := (congrArg (fun w => star w * w) hz).trans (mul_zero _)
  have hsource : (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base (star z*z)=0 :=
    hv.symm.trans ((congrArg (normalizedMatrixStateAWValue hsimple y hy f U).toFun he).trans hzero)
  let eold := (regularizedStateCauchyEmbedding hsimple y hy f 0).comp (scalarMatrixHom (ι := Fin 1))
  have heold : eold (star z*z)=star (eold z)*eold z :=
    (map_mul eold (star z) z).trans (congrArg₂ (·*·) (map_star eold z) rfl)
  have ho := normalizedStateCauchyValue_original hsimple y hy f (star z*z)
  have hoval : normalizedStateCauchyValue hsimple y hy f (star (eold z)*eold z)=0 :=
    (congrArg (normalizedStateCauchyValue hsimple y hy f) heold).symm.trans (ho.trans hsource)
  have hm := (normalizedStateCauchyValue_square_eq_zero_iff hsimple y hy f (eold z)).mp hoval
  have hM : scalarMatrixHom (ι := Fin 1) z=0 :=
    (regularizedStateCauchyEmbedding_injective hsimple y hy f 0)
      (hm.trans (map_zero (regularizedStateCauchyEmbedding hsimple y hy f 0)).symm)
  have hz0 : z=0 := congrArg (fun M : FinMatrix A 1 => M 0 0) hM
  exact sub_eq_zero.mp hz0

lemma matrixStateDiagonalAWEmbedding_isometry :
    Isometry (matrixStateDiagonalAWEmbedding hsimple y hy f U) :=
  NonUnitalStarAlgHom.isometry (matrixStateDiagonalAWEmbedding hsimple y hy f U).toNonUnitalStarAlgHom
    (matrixStateDiagonalAWEmbedding_injective hsimple y hy f U)

lemma matrixStateDiagonalAWEmbedding_root_rank (a : Positive A) :
    Tendsto (fun k => ENNReal.ofReal
      (normalizedMatrixStateAWValue hsimple y hy f U
        (Positive.power (Positive.rootExponent k)
          (Positive.map (matrixStateDiagonalAWEmbedding hsimple y hy f U).toNonUnitalStarAlgHom a)).1).re)
      atTop (nhds (ENNReal.ofReal
        (regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹ *
          regularizedFiniteDimension f.toAddHom f.monotone
            (finitePositiveClass 1 (Positive.map (scalarMatrixHom (ι := Fin 1)).toNonUnitalStarAlgHom a)))) := by
  let e := matrixStateDiagonalAWEmbedding hsimple y hy f U
  let M := Positive.map (scalarMatrixHom (ι := Fin 1)).toNonUnitalStarAlgHom a
  have ht := normalizedMatrixStatePositiveQuasitrace_root_rank hsimple y hy f 0 M
  rw [matrixStateUnitValue_zero] at ht
  have he (k : ℕ) : (normalizedMatrixStateAWValue hsimple y hy f U
      (Positive.power (Positive.rootExponent k) (Positive.map e.toNonUnitalStarAlgHom a)).1).re =
      normalizedMatrixStatePositiveQuasitrace hsimple y hy f 0 (Positive.power (Positive.rootExponent k) M) := by
    rw [← Positive.map_power e.toNonUnitalStarAlgHom a _ (Positive.rootExponent_pos k)]
    change (normalizedMatrixStateAWValue hsimple y hy f U (e (Positive.power (Positive.rootExponent k) a).1)).re = _
    dsimp only [normalizedMatrixStateAWValue,e]
    rw [matrixStateDiagonalAWEmbedding_value]
    rw [← normalizedMatrixStatePositiveQuasitrace_scalar_complex hsimple y hy f 0]
    have hp := congrArg Subtype.val (Positive.map_power (scalarMatrixHom (ι := Fin 1)).toNonUnitalStarAlgHom
      a (Positive.rootExponent k) (Positive.rootExponent_pos k))
    change ((normalizedMatrixStatePositiveQuasitrace hsimple y hy f 0).complexValue
      (scalarMatrixHom (ι := Fin 1) (Positive.power (Positive.rootExponent k) a).1)).re = _
    calc
      _ = ((normalizedMatrixStatePositiveQuasitrace hsimple y hy f 0).complexValue
          (Positive.power (Positive.rootExponent k) M).1).re :=
        congrArg (fun v => ((normalizedMatrixStatePositiveQuasitrace hsimple y hy f 0).complexValue v).re) hp
      _ = _ := congrArg Complex.re
        ((normalizedMatrixStatePositiveQuasitrace hsimple y hy f 0).complexValue_positive _)
  exact ht.congr' (Eventually.of_forall fun k => congrArg ENNReal.ofReal (he k).symm)
end CuntzPureness

end

end OAI
