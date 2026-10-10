import OAI.Geometry.Relativity.CKS.CKSFoliationJet
import OAI.Geometry.Relativity.CKS.MixedCoefficientRealization

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def foliationDenField (z : Point → ℝ) (f : MassFields) : Point → ℝ := fun y =>
  1+z y^3*cksVField z f y
def lapseCorrectionField (z : Point → ℝ) (f : MassFields) : Point → ℝ := fun y =>
  -(cksVField z f y*(Real.sqrt (foliationDenField z f y)*(1+Real.sqrt (foliationDenField z f y)))⁻¹)
def uCorrectionField (z : Point → ℝ) (f : MassFields) : Point → ℝ := fun y =>
  cksDField z f y+lapseCorrectionField z f y+z y^3*(cksDField z f y*lapseCorrectionField z f y)

lemma foliationDenField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    ContDiffAt ℝ 2 (foliationDenField z f) x :=
  contDiffAt_const.add (((hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)).pow 3).mul (cksVField_diff hz hf h0))
lemma actual_foliationDen {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) :
    actualScalarJet (foliationDenField z f) x = foliationDen (actualThreeJet z x,massInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hv := cksVField_diff hz hf h0
  unfold foliationDenField foliationDen
  rw [actualScalarJet_add contDiffAt_const ((hz2.pow 3).mul hv),actualScalarJet_const,
    actualScalarJet_mul (hz2.pow 3) hv,actualScalarJet_pow hz2,cksVField_realized hz hf h0]
  rfl
lemma lapseCorrectionField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) (hp : 0 < foliationDenField z f x) :
    ContDiffAt ℝ 2 (lapseCorrectionField z f) x := by
  have hs := (foliationDenField_diff hz hf h0).sqrt hp.ne'
  have hp' : Real.sqrt (foliationDenField z f x)*(1+Real.sqrt (foliationDenField z f x)) ≠ 0 := by positivity
  exact ((cksVField_diff hz hf h0).mul ((hs.mul (contDiffAt_const.add hs)).inv hp')).neg
lemma uCorrectionField_diff {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) (hp : 0 < foliationDenField z f x) :
    ContDiffAt ℝ 2 (uCorrectionField z f) x := by
  have hd := cksDField_diff hz hf h0
  have hl := lapseCorrectionField_diff hz hf h0 hp
  exact (hd.add hl).add (((hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)).pow 3).mul (hd.mul hl))

lemma actual_lapseCorrection {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) (hp : 0 < foliationDenField z f x) :
    actualScalarJet (lapseCorrectionField z f) x = lapseCorrection (actualThreeJet z x,massInputOf f x) := by
  have hs := (foliationDenField_diff hz hf h0).sqrt hp.ne'
  have hv := cksVField_diff hz hf h0
  have hp' : Real.sqrt (foliationDenField z f x)*(1+Real.sqrt (foliationDenField z f x)) ≠ 0 := by positivity
  have hi := actual_reciprocal (hs.mul (contDiffAt_const.add hs)) hp'
  simp only [one_div] at hi
  unfold lapseCorrectionField lapseCorrection
  erw [actualScalarJet_neg (hv.mul ((hs.mul (contDiffAt_const.add hs)).inv hp')),
    actualScalarJet_mul hv ((hs.mul (contDiffAt_const.add hs)).inv hp'),
    hi,
    actualScalarJet_mul hs (contDiffAt_const.add hs),actualScalarJet_add contDiffAt_const hs,
    actualScalarJet_const,actualScalarJet_sqrt (foliationDenField_diff hz hf h0) hp,
    actual_foliationDen hz hf h0,cksVField_realized hz hf h0]

lemma actual_uCorrection {z : Point → ℝ} {f : MassFields} {x : Point}
    (hz : ContDiffAt ℝ 3 z x) (hf : f.RegularAt x)
    (h0 : determinant (cksQField z f x) ≠ 0) (hp : 0 < foliationDenField z f x) :
    actualScalarJet (uCorrectionField z f) x = uCorrection (actualThreeJet z x,massInputOf f x) := by
  have hz2 := hz.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hd := cksDField_diff hz hf h0
  have hl := lapseCorrectionField_diff hz hf h0 hp
  unfold uCorrectionField uCorrection
  rw [actualScalarJet_add (hd.add hl) ((hz2.pow 3).mul (hd.mul hl))]
  rw [actualScalarJet_add hd hl]
  rw [actualScalarJet_mul (hz2.pow 3) (hd.mul hl)]
  rw [actualScalarJet_pow hz2,actualScalarJet_mul hd hl]
  rw [cksDField_realized hz hf h0,actual_lapseCorrection hz hf h0 hp]
  simp only [actualThreeJet]

lemma reciprocal_sqrt_factor {z V : ℝ} (hp : 0 < 1+z^3*V) :
    (Real.sqrt (1+z^3*V))⁻¹-1 = z^3*(-(V*(Real.sqrt (1+z^3*V)*(1+Real.sqrt (1+z^3*V)))⁻¹)) := by
  have hs := Real.sqrt_pos.mpr hp
  have hsq := Real.sq_sqrt hp.le
  have hh : 1+Real.sqrt (1+z^3*V) ≠ 0 := by positivity
  field_simp
  nlinarith

end
end CKSMixedGeometry

end

end OAI
