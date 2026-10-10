import OAI.NumberTheory.DirichletL.Detector.LowPrimeFamily

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open RayFourExpansion CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowCorrectionEnergy : ℝ := ∑χ : RayCharacter,‖ProbeCompleted.correctionCoeff χ‖^2

lemma lowCorrectionEnergy_nonneg : 0≤lowCorrectionEnergy :=
  Finset.sum_nonneg (fun _ _=>sq_nonneg _)

lemma fixed_correction_energy {ι κ : Type*} [Fintype ι] (R : Finset κ) (c : ι→ℂ) (F : ι→κ→ℂ) :
    (∑m∈R,‖∑χ : ι,c χ*F χ m‖^2)≤
      (∑χ : ι,‖c χ‖^2)*∑χ : ι,∑m∈R,‖F χ m‖^2 := by
  calc
    _≤∑m∈R,(∑χ : ι,‖c χ‖^2)*(∑χ : ι,‖F χ m‖^2) := by
      apply Finset.sum_le_sum
      intro m hm
      calc
        _≤(∑χ : ι,‖c χ‖*‖F χ m‖)^2 := by
          apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>by positivity))).mpr
          simpa only [norm_mul] using norm_sum_le Finset.univ (fun χ=>c χ*F χ m)
        _≤_ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _=_ := by rw [←Finset.mul_sum,Finset.sum_comm]

theorem lowSelectedInverseRow_energy {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (T t : ℝ) (σ : RayRing) (R : Finset O) :
    (∑m∈R,‖lowSelectedInverseRow F c η S hS D T t σ m‖^2)≤
      lowCorrectionEnergy*∑χ : RayCharacter,∑m∈R,
        ‖∑k∈F,c k*InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (calibrationForSet S hS).generator 1 m)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) T
          (fun A=>if D k∣A then (1:ℂ) else 0)‖^2 := by
  simp_rw [lowSelectedInverseRow_correction]
  exact fixed_correction_energy R ProbeCompleted.correctionCoeff _

theorem lowCanonicalSelected_energy {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→CanonicalQuadraticSieve.Supported P.val)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (X t : ℝ) (σ : RayRing) (R : Finset O) :
    (∑m∈R,‖lowSelectedInverseRow Finset.univ
      (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W P t)
      η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ m‖^2)≤
      lowCorrectionEnergy*∑χ : RayCharacter,∑m∈R,
        ‖∑b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J,
          (∏i : SelectedSlot J,lowSingleSlotWeight η (W i.val) (P i.val) t (b i).val)*
          InverseMoment.markedCompletedT
            (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
              (calibrationForSet S hS).generator 1 m)
            (CompletedHeight.normTwistedSource gaussianFixedWindow t) X
            (fun A=>∏i : SelectedSlot J,if (lowCanonicalPrimeFamily T hT J b).ideal i∣A then (1:ℂ) else 0)‖^2 := by
  have hh := lowSelectedInverseRow_energy Finset.univ
    (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W P t)
    η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ R
  simp_rw [lowSelectedWeight_eq_product] at hh
  have he (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
      (fun A : Id=>if lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
        (fun A=>∏i : SelectedSlot J,if (lowCanonicalPrimeFamily T hT J b).ideal i∣A then (1:ℂ) else 0) := by
    funext A
    exact lowCanonicalSelected_mark T hT hdis J b A
  simp_rw [he] at hh
  exact hh

end SevenEighths.ProbePhysical
end

end OAI
