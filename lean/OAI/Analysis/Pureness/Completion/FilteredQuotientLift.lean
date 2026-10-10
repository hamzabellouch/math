import OAI.Analysis.Pureness.Quasitrace.QuasitraceUltraproductAWEmbedding

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {ι : Type*} {D : ι → Type*} {E : Type*}
variable [∀ i, CStarAlgebra (D i)] [∀ i, PartialOrder (D i)]
  [∀ i, StarOrderedRing (D i)] [∀ i, Nontrivial (D i)] [CStarAlgebra E]
variable (T : ∀ i, PositiveQuasitrace (D i)) (F : Filter ι)
variable (hadd : ∀ i (x y : D i), (T i).metricSize (x+y) ≤ (T i).metricSize x+(T i).metricSize y)
variable (hunit : ∀ i, T i ⟨1,zero_le_one⟩ = 1)
variable (φ : lp D ∞ →⋆ₐ[ℂ] E)
variable (hφ : ∀ u v, (filteredQuasitraceNullIdeal T F hadd).ringCon u v → φ u=φ v)

def filteredQuasitraceLift : FilteredQuasitraceQuotient T F hadd hunit →⋆ₐ[ℂ] E :=
  { (filteredQuasitraceNullIdeal T F hadd).ringCon.liftₐ φ.toAlgHom hφ with
    map_star' := by
      intro z
      obtain ⟨u,rfl⟩ := (filteredQuasitraceClosedIdeal T F hadd hunit).quotientMap_surjective z
      exact map_star φ u }

lemma filteredQuasitraceLift_apply (u : lp D ∞) :
    filteredQuasitraceLift T F hadd hunit φ hφ (filteredQuasitraceQuotientMap T F hadd hunit u) = φ u := rfl

lemma filteredQuasitraceLift_injective
    (hker : ∀ u v, φ u=φ v → (filteredQuasitraceNullIdeal T F hadd).ringCon u v) :
    Function.Injective (filteredQuasitraceLift T F hadd hunit φ hφ) := by
  intro z w h
  obtain ⟨u,rfl⟩ := (filteredQuasitraceClosedIdeal T F hadd hunit).quotientMap_surjective z
  obtain ⟨v,rfl⟩ := (filteredQuasitraceClosedIdeal T F hadd hunit).quotientMap_surjective w
  exact Quotient.sound (hker u v h)
end CuntzPureness

end

end OAI
