import OAI.Analysis.Pureness.States.FiniteFamilyUltraproduct
import OAI.Analysis.Pureness.States.ScalarTracialUltraproductTrace

namespace OAI
noncomputable section
namespace CuntzPureness.CompatibleFiniteQuasitrace
open CuntzTrace OrderedSemigroup Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (F : CompatibleFiniteQuasitrace A)
variable (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))
variable (hF : F.level 1 1=1)
include hF

omit [Nontrivial A] in
lemma normalizedScalarPositive (n : ℕ) (a : Positive (FinMatrix ℂ (n+1))) :
    F.normalizedPositiveLevel hmono n
      (Positive.map scalarCoefficientMatrixHom.toNonUnitalStarAlgHom a) =
        scalarMatrixPositiveTrace n a := by
  have he := (F.normalizedPositiveLevel_scalarCoefficient hmono hF n a.1).trans
    (scalarMatrixPositiveTrace_complex n a.1).symm
  change (F.normalizedPositiveLevel hmono n).complexValue
    (Positive.map scalarCoefficientMatrixHom.toNonUnitalStarAlgHom a).1 =
      (scalarMatrixPositiveTrace n).complexValue a.1 at he
  rw [PositiveQuasitrace.complexValue_positive,PositiveQuasitrace.complexValue_positive] at he
  exact Complex.ofReal_injective he

variable (U : Ultrafilter ℕ)

def scalarCoefficientAWMap :
    lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞ →⋆ₐ[ℂ] F.MatrixUltraAW hmono hF U :=
  (ultralimitCompletionMap (F.normalizedPositiveLevel hmono) U
    (F.normalizedPositiveLevel_unit hmono hF) (F.normalizedPositiveLevel_metricSize_add hmono)).comp
      scalarCoefficientProductHom

lemma scalarCoefficientAWMap_commute (x : A) (u : lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞) :
    Commute (F.matrixDiagonalAWMap hmono hF U x) (F.scalarCoefficientAWMap hmono hF U u) := by
  let φ := ultralimitCompletionMap (F.normalizedPositiveLevel hmono) U
    (F.normalizedPositiveLevel_unit hmono hF) (F.normalizedPositiveLevel_metricSize_add hmono)
  exact (scalarCoefficientProductHom_commute (A := A) x u).map φ

lemma scalarCoefficientAWMap_eq (u v : lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞) :
    scalarCoefficientAWMap F hmono hF U u = scalarCoefficientAWMap F hmono hF U v ↔
      (filteredQuasitraceNullIdeal scalarMatrixPositiveTrace (U : Filter ℕ)
        scalarMatrixPositiveTrace_metricSize_add).ringCon u v := by
  dsimp only [scalarCoefficientAWMap,StarAlgHom.comp_apply]
  rw [ultralimitCompletionMap_eq,TwoSidedIdeal.rel_iff,TwoSidedIdeal.rel_iff,
    filteredQuasitraceNullIdeal_mem,filteredQuasitraceNullIdeal_mem]
  have he (n : ℕ) : F.normalizedPositiveLevel hmono n
      (Positive.starMul (scalarCoefficientMatrixHom (u n)-scalarCoefficientMatrixHom (v n))) =
        scalarMatrixPositiveTrace n (Positive.starMul (u n-v n)) := by
    rw [← map_sub]
    have hp : Positive.starMul (scalarCoefficientMatrixHom (A := A) (u n-v n)) =
        Positive.map scalarCoefficientMatrixHom.toNonUnitalStarAlgHom (Positive.starMul (u n-v n)) := by
      apply Subtype.ext
      change star (scalarCoefficientMatrixHom (u n-v n))*scalarCoefficientMatrixHom (u n-v n) =
        scalarCoefficientMatrixHom (star (u n-v n)*(u n-v n))
      rw [map_mul,map_star]
    rw [hp,F.normalizedScalarPositive hmono hF]
  have hev (w : lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞) (n : ℕ) :
      scalarCoefficientProductHom (A := A) w n = scalarCoefficientMatrixHom (A := A) (w n) := rfl
  simp only [lp.coeFn_sub,Pi.sub_apply,hev,he]

def scalarTracialMatrixAWEmbedding :
    ScalarTracialMatrixUltraproduct U →⋆ₐ[ℂ] F.MatrixUltraAW hmono hF U :=
  filteredQuasitraceLift scalarMatrixPositiveTrace (U : Filter ℕ)
    scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit
    (scalarCoefficientAWMap F hmono hF U)
    (fun u v h => (scalarCoefficientAWMap_eq F hmono hF U u v).mpr h)

lemma scalarTracialMatrixAWEmbedding_map (u : lp (fun n : ℕ => FinMatrix ℂ (n+1)) ∞) :
    scalarTracialMatrixAWEmbedding F hmono hF U
      (filteredQuasitraceQuotientMap scalarMatrixPositiveTrace (U : Filter ℕ)
        scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit u) =
      scalarCoefficientAWMap F hmono hF U u := rfl

lemma scalarTracialMatrixAWEmbedding_injective :
    Function.Injective (scalarTracialMatrixAWEmbedding F hmono hF U) :=
  filteredQuasitraceLift_injective scalarMatrixPositiveTrace (U : Filter ℕ)
    scalarMatrixPositiveTrace_metricSize_add scalarMatrixPositiveTrace_unit
    (scalarCoefficientAWMap F hmono hF U)
    (fun u v h => (scalarCoefficientAWMap_eq F hmono hF U u v).mpr h)
    (fun u v h => (scalarCoefficientAWMap_eq F hmono hF U u v).mp h)

lemma scalarTracialMatrixAWEmbedding_isometry :
    Isometry (scalarTracialMatrixAWEmbedding F hmono hF U) :=
  NonUnitalStarAlgHom.isometry (scalarTracialMatrixAWEmbedding F hmono hF U).toNonUnitalStarAlgHom
    (scalarTracialMatrixAWEmbedding_injective F hmono hF U)

lemma scalarTracialMatrixAWEmbedding_commute (x : A) (z : ScalarTracialMatrixUltraproduct U) :
    Commute (F.matrixDiagonalAWMap hmono hF U x)
      (scalarTracialMatrixAWEmbedding F hmono hF U z) := by
  refine Quotient.inductionOn z ?_
  intro u
  exact scalarCoefficientAWMap_commute F hmono hF U x u
end CuntzPureness.CompatibleFiniteQuasitrace

end

end OAI
