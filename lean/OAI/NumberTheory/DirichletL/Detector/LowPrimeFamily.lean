import OAI.NumberTheory.DirichletL.Detector.LowSlotMarks
import OAI.NumberTheory.DirichletL.Detector.LowSlotWeights
import OAI.NumberTheory.DirichletL.Reflection.Canonical

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowCanonicalSelectedPrime_maximal {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    (lowCanonicalSelectedPrime T hT J b i).val.IsMaximal :=
  (Ideal.isPrime_of_prime (lowCanonicalSelectedPrime T hT J b i).property).isMaximal
    (lowCanonicalSelectedPrime T hT J b i).property.ne_zero

lemma lowCanonicalSelectedPrime_good {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    ConcretePrimeRowBridge.goodLambda∉(lowCanonicalSelectedPrime T hT J b i).val ∧
      ringChar (O⧸(lowCanonicalSelectedPrime T hT J b i).val)≠2 := by
  have hs := hT i.val _ (lowCanonicalSelectedPrime_mem T hT J b i)
  exact hs.2 _ ((Ideal.mem_normalizedFactors_iff hs.1).mpr
    ⟨Ideal.isPrime_of_prime (lowCanonicalSelectedPrime T hT J b i).property,le_rfl⟩)

def lowCanonicalPrimeFamily {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    InverseReflectedPhase.PrimeFamily (SelectedSlot J) where
  ideal i := (lowCanonicalSelectedPrime T hT J b i).val
  maximal := lowCanonicalSelectedPrime_maximal T hT J b
  good i := (lowCanonicalSelectedPrime_good T hT J b i).1

lemma lowCanonicalPrimeFamily_generator {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    (lowCanonicalPrimeFamily T hT J b).generator i=(b i).val := by
  let := lowCanonicalSelectedPrime_maximal T hT J b i
  change primaryPrime (lowCanonicalSelectedPrime T hT J b i).val=(b i).val
  rw [primaryPrime_eq_primaryGenerator]
  have hh := congrArg Subtype.val ((canonicalSlotEquiv (T i.val) (hT i.val)).apply_symm_apply (b i))
  simpa only [canonicalSlotEquiv_val,lowCanonicalSelectedPrime] using hh

lemma lowCanonicalPrimeFamily_pairwise {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    Pairwise (Function.onFun IsCoprime (lowCanonicalPrimeFamily T hT J b).ideal) := by
  intro i j hij
  exact primeIdeal_coprime _ _ (fun h=>hij (lowCanonicalSelectedPrime_injective T hT hdis J b h))

lemma lowCanonicalPrimeFamily_odd {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) (i : SelectedSlot J) :
    ringChar (O⧸(lowCanonicalPrimeFamily T hT J b).ideal i)≠2 :=
  (lowCanonicalSelectedPrime_good T hT J b i).2

lemma lowCanonicalPrimeFamily_product {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (J : Finset (Fin K))
    (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
    lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b=
      ∏i : SelectedSlot J,(lowCanonicalPrimeFamily T hT J b).ideal i := by
  rw [lowSelectedIdeal_eq_product]
  simp_rw [lowCanonicalSelectedPrime_span T hT J b]
  rfl

theorem lowCanonicalInverseRow_eq {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J)
    (R t : ℝ) (σ : RayRing) (m : O) :
    lowMarkedInverseRow η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b) R t σ m=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (calibrationForSet S hS).generator 1 m)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) R
          (fun A=>∏i : SelectedSlot J,if (lowCanonicalPrimeFamily T hT J b).ideal i∣A then (1:ℂ) else 0) := by
  unfold lowMarkedInverseRow
  have he : (fun A : Id=>if lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
      (fun A : Id=>∏i : SelectedSlot J,if (lowCanonicalPrimeFamily T hT J b).ideal i∣A then (1:ℂ) else 0) := by
    funext A
    exact lowCanonicalSelected_mark T hT hdis J b A
  rw [he]

end SevenEighths.ProbePhysical
end

end OAI
