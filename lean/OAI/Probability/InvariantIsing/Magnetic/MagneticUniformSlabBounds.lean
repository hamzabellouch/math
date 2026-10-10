import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationJet

namespace OAI

/-! Spatial bounds for the actual Gaussian transition, uniform in its
variance. These are used to control both endpoints of inverse coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def MagneticSlabBound (f : ℝ≥0 → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ v z, |f v z| ≤ C

namespace MagneticSlabBound

lemma const (c : ℝ) : MagneticSlabBound (fun _ _ => c) :=
  ⟨|c|, abs_nonneg _, fun _ _ => le_rfl⟩

lemma add {f g : ℝ≥0 → ℝ → ℝ} (hf : MagneticSlabBound f)
    (hg : MagneticSlabBound g) : MagneticSlabBound (fun v z => f v z + g v z) := by
  obtain ⟨C, hC, bC⟩ := hf
  obtain ⟨D, hD, bD⟩ := hg
  exact ⟨C + D, add_nonneg hC hD, fun v z =>
    (abs_add_le _ _).trans (add_le_add (bC v z) (bD v z))⟩

lemma sub {f g : ℝ≥0 → ℝ → ℝ} (hf : MagneticSlabBound f)
    (hg : MagneticSlabBound g) : MagneticSlabBound (fun v z => f v z - g v z) := by
  obtain ⟨C, hC, bC⟩ := hf
  obtain ⟨D, hD, bD⟩ := hg
  exact ⟨C + D, add_nonneg hC hD, fun v z =>
    (abs_sub _ _).trans (add_le_add (bC v z) (bD v z))⟩

lemma mul {f g : ℝ≥0 → ℝ → ℝ} (hf : MagneticSlabBound f)
    (hg : MagneticSlabBound g) : MagneticSlabBound (fun v z => f v z * g v z) := by
  obtain ⟨C, hC, bC⟩ := hf
  obtain ⟨D, hD, bD⟩ := hg
  refine ⟨C * D, mul_nonneg hC hD, fun v z => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (bC v z) (bD v z) (abs_nonneg _) hC

lemma transition (ζ : ℝ) {F A : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hA : MagneticContinuationBound A) :
    MagneticSlabBound (fun v => fieldSpinTransition ζ v F A) := by
  obtain ⟨C, hC, bC⟩ := hA
  exact ⟨C, hC, fun v => fieldSpinTransition_bound ζ v hF hG bC⟩

lemma spatial (ζ : ℝ) {F M A B : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : MagneticContinuationBound M) (hA : MagneticContinuationBound A)
    (hB : MagneticContinuationBound B) :
    MagneticSlabBound (fun v => fieldTiltSpatial ζ v F M A B) := by
  obtain ⟨C, hC, bC⟩ := hM
  obtain ⟨D, hD, bD⟩ := hA
  obtain ⟨E, _, bE⟩ := hB
  exact ⟨E + 2 * |ζ| * D * C, by positivity,
    fun v => fieldSpinTransition_derivative_bound ζ v hF hG hC hD bC bD bE⟩

end MagneticSlabBound

lemma magneticContinuationSecond_uniform (ζ : ℝ)
    {F M Q A B C : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : MagneticContinuationBound M) (hQ : MagneticContinuationBound Q)
    (hA : MagneticContinuationBound A) (hB : MagneticContinuationBound B)
    (hC : MagneticContinuationBound C) :
    MagneticSlabBound (fun v => magneticContinuationSecond ζ v F M Q A B C) := by
  have T {A : ℝ → ℝ} (hA : MagneticContinuationBound A) :=
    MagneticSlabBound.transition ζ hF hG hA
  have D {A B : ℝ → ℝ} (hA : MagneticContinuationBound A) (hB : MagneticContinuationBound B) :=
    MagneticSlabBound.spatial ζ hF hG hM hA hB
  exact (D hB hC).add ((MagneticSlabBound.const ζ).mul
    ((D (hA.mul hM) ((hB.mul hM).add (hA.mul hQ))).sub
      (((D hA hB).mul (T hM)).add ((T hA).mul (D hM hQ)))))

lemma magneticContinuationThird_uniform (ζ : ℝ)
    {F M Q R A B C D : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : MagneticContinuationBound M) (hQ : MagneticContinuationBound Q)
    (hR : MagneticContinuationBound R) (hA : MagneticContinuationBound A)
    (hB : MagneticContinuationBound B) (hC : MagneticContinuationBound C)
    (hD : MagneticContinuationBound D) :
    MagneticSlabBound (fun v => magneticContinuationThird ζ v F M Q R A B C D) := by
  have T {A : ℝ → ℝ} (hA : MagneticContinuationBound A) :=
    MagneticSlabBound.transition ζ hF hG hA
  have S {A B : ℝ → ℝ} (hA : MagneticContinuationBound A) (hB : MagneticContinuationBound B) :=
    MagneticSlabBound.spatial ζ hF hG hM hA hB
  have D2 {A B C : ℝ → ℝ} (hA : MagneticContinuationBound A)
      (hB : MagneticContinuationBound B) (hC : MagneticContinuationBound C) :=
    magneticContinuationSecond_uniform ζ hF hG hM hQ hA hB hC
  have hb2 := (hB.mul hM).add (hA.mul hQ)
  have hb3 := ((hC.mul hM).add
    (((MagneticContinuationBound.const 2).mul hB).mul hQ)).add (hA.mul hR)
  exact (D2 hB hC hD).add ((MagneticSlabBound.const ζ).mul
    ((D2 (hA.mul hM) hb2 hb3).sub
      ((((D2 hA hB hC).mul (T hM)).add
        ((((MagneticSlabBound.const 2).mul (S hA hB)).mul (S hM hQ)))).add
          ((T hA).mul (D2 hM hQ hR)))))

lemma MagneticContinuationJet.transition_second_uniform (A P : MagneticContinuationJet)
    (ζ : ℝ) (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) :
    MagneticSlabBound (fun v z => (A.transition P ζ v F hF hG dF).second z) :=
  magneticContinuationSecond_uniform ζ hF hG P.bValue P.bFirst A.bValue A.bFirst A.bSecond

lemma MagneticContinuationJet.transition_third_uniform (A P : MagneticContinuationJet)
    (ζ : ℝ) (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) :
    MagneticSlabBound (fun v z => (A.transition P ζ v F hF hG dF).third z) :=
  magneticContinuationThird_uniform ζ hF hG P.bValue P.bFirst P.bSecond
    A.bValue A.bFirst A.bSecond A.bThird

end InvariantIsing

end

end OAI
