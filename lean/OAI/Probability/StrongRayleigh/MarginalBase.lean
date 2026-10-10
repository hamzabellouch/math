import OAI.Probability.StrongRayleigh.Model

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate
namespace Problem336AdditiveD139

def finiteMarginal {I : Type u_1} (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) :
    ProbabilityMeasure (S → Bool) :=
  μ.map (fun a i => a i.1)

lemma finiteMarginal_apply_singleton {I : Type u_2} (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (x : S → Bool) :
    ((finiteMarginal μ S : Measure (S → Bool)) {x}).toReal = marginalMass μ S x := by
  classical
  unfold finiteMarginal marginalMass
  rw [ProbabilityMeasure.map_apply' _
    (Measurable.of_eval (fun i => measurable_pi_apply i.1)).aemeasurable
    (measurableSet_singleton x)]
  congr 2
  ext a
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  exact funext_iff

lemma finiteGeneratingValue_finiteMarginal {I : Type u_3}
    (μ : ProbabilityMeasure (I → Bool)) (S : Finset I) (z : S → ℂ) :
    finiteGeneratingValue (finiteMarginal μ S) z = marginalGeneratingValue μ S z := by
  classical
  unfold finiteGeneratingValue marginalGeneratingValue
  simp_rw [finiteMarginal_apply_singleton]
  exact Finset.sum_congr (by ext; simp) (by intros; rfl)

lemma positiveContractionFinite_restrict {I : Type u_4} (K : I → I → ℂ)
    (hK : PositiveContractionKernel K) (S : Finset I) :
    PositiveContractionFinite (fun i j : S => K i.1 j.1) := by
  exact ⟨fun i j => hK.1 i.1 j.1, hK.2 S⟩

lemma marginalGeneratingValue_empty {I : Type u_5} (μ : ProbabilityMeasure (I → Bool))
    (z : (∅ : Finset I) → ℂ) : marginalGeneratingValue μ ∅ z = 1 := by
  classical
  simp [marginalGeneratingValue, marginalMass]

end Problem336AdditiveD139

end

end OAI
