import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationSpatial

namespace OAI

/-! Measurability and finite spatial derivative bounds for the actual
Gaussian continuation formulas through order three. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def MagneticContinuationBound (f : ℝ → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |f x| ≤ K

namespace MagneticContinuationBound

lemma const (c : ℝ) : MagneticContinuationBound (fun _ => c) :=
  ⟨|c|, abs_nonneg _, fun _ => le_rfl⟩

lemma add {f g : ℝ → ℝ} (hf : MagneticContinuationBound f)
    (hg : MagneticContinuationBound g) : MagneticContinuationBound (fun x => f x + g x) := by
  obtain ⟨K, hK, bK⟩ := hf
  obtain ⟨L, hL, bL⟩ := hg
  exact ⟨K + L, add_nonneg hK hL, fun x =>
    (abs_add_le _ _).trans (add_le_add (bK x) (bL x))⟩

lemma sub {f g : ℝ → ℝ} (hf : MagneticContinuationBound f)
    (hg : MagneticContinuationBound g) : MagneticContinuationBound (fun x => f x - g x) := by
  obtain ⟨K, hK, bK⟩ := hf
  obtain ⟨L, hL, bL⟩ := hg
  exact ⟨K + L, add_nonneg hK hL, fun x =>
    (abs_sub _ _).trans (add_le_add (bK x) (bL x))⟩

lemma mul {f g : ℝ → ℝ} (hf : MagneticContinuationBound f)
    (hg : MagneticContinuationBound g) : MagneticContinuationBound (fun x => f x * g x) := by
  obtain ⟨K, hK, bK⟩ := hf
  obtain ⟨L, hL, bL⟩ := hg
  refine ⟨K * L, mul_nonneg hK hL, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (bK x) (bL x) (abs_nonneg _) hK

lemma transition (ζ : ℝ) (v : ℝ≥0) {F A : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hA : MagneticContinuationBound A) :
    MagneticContinuationBound (fieldSpinTransition ζ v F A) := by
  obtain ⟨K, hK, bK⟩ := hA
  exact ⟨K, hK, fieldSpinTransition_bound ζ v hF hG bK⟩

lemma spatial (ζ : ℝ) (v : ℝ≥0) {F M A B : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : MagneticContinuationBound M) (hA : MagneticContinuationBound A)
    (hB : MagneticContinuationBound B) :
    MagneticContinuationBound (fieldTiltSpatial ζ v F M A B) := by
  obtain ⟨K, hK, bK⟩ := hM
  obtain ⟨L, hL, bL⟩ := hA
  obtain ⟨C, hC, bC⟩ := hB
  exact ⟨C + 2 * |ζ| * L * K, by positivity,
    fieldSpinTransition_derivative_bound ζ v hF hG hK hL bK bL bC⟩

end MagneticContinuationBound

lemma measurable_magneticContinuationSecond (ζ : ℝ) (v : ℝ≥0)
    {F M Q A B C : ℝ → ℝ} (hF : Measurable F)
    (hM : Measurable M) (hQ : Measurable Q)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) :
    Measurable (magneticContinuationSecond ζ v F M Q A B C) := by
  have hS := measurable_fieldTiltSpatial ζ v hF hM hB hC
  have hSA := measurable_fieldTiltSpatial ζ v hF hM hA hB
  have hSM := measurable_fieldTiltSpatial ζ v hF hM hM hQ
  have hSAM := measurable_fieldTiltSpatial ζ v hF hM (hA.mul hM)
    ((hB.mul hM).add (hA.mul hQ))
  have hTA := measurable_fieldSpinTransition ζ v hF hA
  have hTM := measurable_fieldSpinTransition ζ v hF hM
  exact hS.add ((hSAM.sub ((hSA.mul hTM).add (hTA.mul hSM))).const_mul ζ)

lemma magneticContinuationSecond_bounded (ζ : ℝ) (v : ℝ≥0)
    {F M Q A B C : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : MagneticContinuationBound M) (hQ : MagneticContinuationBound Q)
    (hA : MagneticContinuationBound A) (hB : MagneticContinuationBound B)
    (hC : MagneticContinuationBound C) :
    MagneticContinuationBound (magneticContinuationSecond ζ v F M Q A B C) := by
  have T {A : ℝ → ℝ} (hA : MagneticContinuationBound A) :=
    MagneticContinuationBound.transition ζ v hF hG hA
  have D {A B : ℝ → ℝ} (hA : MagneticContinuationBound A) (hB : MagneticContinuationBound B) :=
    MagneticContinuationBound.spatial ζ v hF hG hM hA hB
  exact (D hB hC).add ((MagneticContinuationBound.const ζ).mul
    ((D (hA.mul hM) ((hB.mul hM).add (hA.mul hQ))).sub
      (((D hA hB).mul (T hM)).add ((T hA).mul (D hM hQ)))))

lemma measurable_magneticContinuationThird (ζ : ℝ) (v : ℝ≥0)
    {F M Q R A B C D : ℝ → ℝ} (hF : Measurable F)
    (hM : Measurable M) (hQ : Measurable Q) (hR : Measurable R)
    (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) (hD : Measurable D) :
    Measurable (magneticContinuationThird ζ v F M Q R A B C D) := by
  have h1 := measurable_magneticContinuationSecond ζ v hF hM hQ hB hC hD
  have h2 := measurable_magneticContinuationSecond ζ v hF hM hQ (hA.mul hM)
    ((hB.mul hM).add (hA.mul hQ))
    (((hC.mul hM).add (((measurable_const (a := (2 : ℝ))).mul hB).mul hQ)).add (hA.mul hR))
  have h3 := measurable_magneticContinuationSecond ζ v hF hM hQ hA hB hC
  have h4 := measurable_magneticContinuationSecond ζ v hF hM hQ hM hQ hR
  have hTA := measurable_fieldSpinTransition ζ v hF hA
  have hTM := measurable_fieldSpinTransition ζ v hF hM
  have hSA := measurable_fieldTiltSpatial ζ v hF hM hA hB
  have hSM := measurable_fieldTiltSpatial ζ v hF hM hM hQ
  exact h1.add ((h2.sub (((h3.mul hTM).add
    ((measurable_const.mul hSA).mul hSM)).add (hTA.mul h4))).const_mul ζ)

lemma magneticContinuationThird_bounded (ζ : ℝ) (v : ℝ≥0)
    {F M Q R A B C D : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : MagneticContinuationBound M) (hQ : MagneticContinuationBound Q)
    (hR : MagneticContinuationBound R) (hA : MagneticContinuationBound A)
    (hB : MagneticContinuationBound B) (hC : MagneticContinuationBound C)
    (hD : MagneticContinuationBound D) :
    MagneticContinuationBound (magneticContinuationThird ζ v F M Q R A B C D) := by
  have T {A : ℝ → ℝ} (hA : MagneticContinuationBound A) :=
    MagneticContinuationBound.transition ζ v hF hG hA
  have S {A B : ℝ → ℝ} (hA : MagneticContinuationBound A) (hB : MagneticContinuationBound B) :=
    MagneticContinuationBound.spatial ζ v hF hG hM hA hB
  have D2 {A B C : ℝ → ℝ} (hA : MagneticContinuationBound A)
      (hB : MagneticContinuationBound B) (hC : MagneticContinuationBound C) :=
    magneticContinuationSecond_bounded ζ v hF hG hM hQ hA hB hC
  have hb2 := (hB.mul hM).add (hA.mul hQ)
  have hb3 := ((hC.mul hM).add
    (((MagneticContinuationBound.const 2).mul hB).mul hQ)).add (hA.mul hR)
  exact (D2 hB hC hD).add ((MagneticContinuationBound.const ζ).mul
    ((D2 (hA.mul hM) hb2 hb3).sub
      ((((D2 hA hB hC).mul (T hM)).add
        ((((MagneticContinuationBound.const 2).mul (S hA hB)).mul (S hM hQ)))).add
          ((T hA).mul (D2 hM hQ hR)))))

end InvariantIsing

end

end OAI
