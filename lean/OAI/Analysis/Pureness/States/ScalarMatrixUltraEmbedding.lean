import OAI.Analysis.Pureness.States.NormalizedMatrixStateScalar
import OAI.Analysis.Pureness.States.ScalarMatrixTrace
import OAI.Analysis.Pureness.Completion.FilteredQuotientLift

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

lemma normalizedMatrixState_scalarPositive (n : ℕ) (a : Positive (FinMatrix ℂ (n+1))) :
    normalizedMatrixStatePositiveQuasitrace hsimple y hy f n
      (Positive.map scalarCoefficientMatrixHom.toNonUnitalStarAlgHom a) =
        scalarMatrixPositiveTrace n a := by
  have he := (normalizedMatrixState_scalarCoefficient hsimple y hy f n a.1).trans
    (scalarMatrixPositiveTrace_complex n a.1).symm
  change (normalizedMatrixStatePositiveQuasitrace hsimple y hy f n).complexValue
    (Positive.map scalarCoefficientMatrixHom.toNonUnitalStarAlgHom a).1 =
      (scalarMatrixPositiveTrace n).complexValue a.1 at he
  rw [PositiveQuasitrace.complexValue_positive,PositiveQuasitrace.complexValue_positive] at he
  exact Complex.ofReal_injective he

abbrev ScalarTracialMatrixUltraproduct (U : Ultrafilter ℕ) :=
  FilteredQuasitraceQuotient scalarMatrixPositiveTrace (U : Filter ℕ)
    scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit

variable (U : Ultrafilter ℕ)

lemma scalarCoefficientAWMap_eq (u v : lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞) :
    scalarCoefficientAWMap hsimple y hy f U u = scalarCoefficientAWMap hsimple y hy f U v ↔
      (filteredQuasitraceNullIdeal scalarMatrixPositiveTrace (U : Filter ℕ)
        scalarMatrixPositiveTrace_metricSize_add).ringCon u v := by
  dsimp only [scalarCoefficientAWMap,StarAlgHom.comp_apply]
  rw [ultralimitCompletionMap_eq,TwoSidedIdeal.rel_iff,TwoSidedIdeal.rel_iff,
    filteredQuasitraceNullIdeal_mem,filteredQuasitraceNullIdeal_mem]
  have he (n : ℕ) : normalizedMatrixStatePositiveQuasitrace hsimple y hy f n
      (Positive.starMul (scalarCoefficientMatrixHom (u n)-scalarCoefficientMatrixHom (v n))) =
        scalarMatrixPositiveTrace n (Positive.starMul (u n-v n)) := by
    rw [← map_sub]
    have hp : Positive.starMul (scalarCoefficientMatrixHom (A := A) (u n-v n)) =
        Positive.map scalarCoefficientMatrixHom.toNonUnitalStarAlgHom (Positive.starMul (u n-v n)) := by
      apply Subtype.ext
      change star (scalarCoefficientMatrixHom (u n-v n))*scalarCoefficientMatrixHom (u n-v n) =
        scalarCoefficientMatrixHom (star (u n-v n)*(u n-v n))
      rw [map_mul,map_star]
    rw [hp,normalizedMatrixState_scalarPositive]
  have hev (w : lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞) (n : ℕ) :
      scalarCoefficientProductHom (A := A) w n = scalarCoefficientMatrixHom (A := A) (w n) := rfl
  simp only [lp.coeFn_sub,Pi.sub_apply,hev,he]

def scalarTracialMatrixAWEmbedding :
    ScalarTracialMatrixUltraproduct U →⋆ₐ[ℂ] NormalizedMatrixStateUltraAW hsimple y hy f U :=
  filteredQuasitraceLift scalarMatrixPositiveTrace (U : Filter ℕ)
    scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit
    (scalarCoefficientAWMap hsimple y hy f U)
    (fun u v h => (scalarCoefficientAWMap_eq hsimple y hy f U u v).mpr h)

lemma scalarTracialMatrixAWEmbedding_map (u : lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞) :
    scalarTracialMatrixAWEmbedding hsimple y hy f U
      (filteredQuasitraceQuotientMap scalarMatrixPositiveTrace (U : Filter ℕ)
        scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit u) =
      scalarCoefficientAWMap hsimple y hy f U u := rfl

lemma scalarTracialMatrixAWEmbedding_injective :
    Function.Injective (scalarTracialMatrixAWEmbedding hsimple y hy f U) :=
  filteredQuasitraceLift_injective scalarMatrixPositiveTrace (U : Filter ℕ)
    scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit
    (scalarCoefficientAWMap hsimple y hy f U)
    (fun u v h => (scalarCoefficientAWMap_eq hsimple y hy f U u v).mpr h)
    (fun u v h => (scalarCoefficientAWMap_eq hsimple y hy f U u v).mp h)

lemma scalarTracialMatrixAWEmbedding_isometry :
    Isometry (scalarTracialMatrixAWEmbedding hsimple y hy f U) :=
  NonUnitalStarAlgHom.isometry (scalarTracialMatrixAWEmbedding hsimple y hy f U).toNonUnitalStarAlgHom
    (scalarTracialMatrixAWEmbedding_injective hsimple y hy f U)

lemma scalarTracialMatrixAWEmbedding_commute (x : A) (z : ScalarTracialMatrixUltraproduct U) :
    Commute (matrixStateDiagonalAWEmbedding hsimple y hy f U x)
      (scalarTracialMatrixAWEmbedding hsimple y hy f U z) := by
  refine Quotient.inductionOn z ?_
  intro u
  exact scalarCoefficientAWMap_commute hsimple y hy f U x u

end CuntzPureness

end

end OAI
