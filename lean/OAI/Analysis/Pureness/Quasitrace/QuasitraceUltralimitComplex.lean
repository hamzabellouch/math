import OAI.Analysis.Pureness.Quasitrace.QuasitraceUltralimitPositive
import OAI.Analysis.Pureness.Quasitrace.QuasitraceNaturality

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder ComplexStarModule
variable {ι : Type*} {D : ι → Type*}
variable [∀ i, CStarAlgebra (D i)] [∀ i, PartialOrder (D i)]
  [∀ i, StarOrderedRing (D i)] [∀ i, Nontrivial (D i)]
local instance : Module ℝ (lp D ∞) := Module.restrictScalars ℝ ℂ (lp D ∞)
local instance : Algebra ℝ (lp D ∞) := Algebra.restrictScalars ℝ ℂ (lp D ∞)

variable (T : ∀ i, PositiveQuasitrace (D i)) (U : Ultrafilter ι)
variable (hunit : ∀ i, T i ⟨1,zero_le_one⟩ = 1)

lemma quasitraceUltraSelfAdjoint_tendsto (a : selfAdjoint (lp D ∞)) :
    Tendsto (fun i => (T i).selfAdjointValue
      (starHomSelfAdjointMap (boundedProductEval i).toNonUnitalStarAlgHom a))
      (U : Filter ι) (nhds ((ultralimitPositiveQuasitrace T U hunit).selfAdjointValue a)) := by
  have he (i : ι) : (T i).selfAdjointValue
      (starHomSelfAdjointMap (boundedProductEval i).toNonUnitalStarAlgHom a) =
        T i (boundedProductPositiveEval i ⟨a.1⁺,CFC.posPart_nonneg _⟩) -
          T i (boundedProductPositiveEval i ⟨a.1⁻,CFC.negPart_nonneg _⟩) := by
    unfold PositiveQuasitrace.selfAdjointValue
    change T i ⟨((boundedProductEval i).toNonUnitalStarAlgHom a.1)⁺,_⟩ -
      T i ⟨((boundedProductEval i).toNonUnitalStarAlgHom a.1)⁻,_⟩ = _
    rw [← positiveMap_posPart (boundedProductEval i).toNonUnitalStarAlgHom a,
      ← positiveMap_negPart (boundedProductEval i).toNonUnitalStarAlgHom a]
    rfl
  simp only [he]
  exact (quasitraceUltraPositive_tendsto T U hunit ⟨a.1⁺,CFC.posPart_nonneg _⟩).sub
    (quasitraceUltraPositive_tendsto T U hunit ⟨a.1⁻,CFC.negPart_nonneg _⟩)

lemma quasitraceUltraComplex_tendsto (u : lp D ∞) :
    Tendsto (fun i => (T i).complexValue (u i)) (U : Filter ι)
      (nhds ((ultralimitPositiveQuasitrace T U hunit).complexValue u)) := by
  have hr := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (quasitraceUltraSelfAdjoint_tendsto T U hunit (ℜ u))
  have hi := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (quasitraceUltraSelfAdjoint_tendsto T U hunit (ℑ u))
  have he := hr.add (hi.const_mul Complex.I)
  have er (i : ι) : starHomSelfAdjointMap (boundedProductEval i).toNonUnitalStarAlgHom (ℜ u) = ℜ (u i) :=
    Subtype.ext (map_realPart (boundedProductEval i) u)
  have ei (i : ι) : starHomSelfAdjointMap (boundedProductEval i).toNonUnitalStarAlgHom (ℑ u) = ℑ (u i) :=
    Subtype.ext (map_imaginaryPart (boundedProductEval i) u)
  simpa only [Function.comp_def,er,ei,PositiveQuasitrace.complexValue] using he
end CuntzPureness

end

end OAI
