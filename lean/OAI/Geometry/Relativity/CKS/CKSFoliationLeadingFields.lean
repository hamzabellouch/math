import OAI.Geometry.Relativity.CKS.CollarFieldJets
import OAI.Geometry.Relativity.CKS.CKSFoliationLeading

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def leadingDField (f : MassFields) : Point → ℝ := fun y =>
  (-3/4:ℝ)*traceProduct (inverse (f.sigma y)) (f.mg y)
def leadingTField (f : MassFields) : Point → ℝ := fun y =>
  (1/2:ℝ)*traceProduct (inverse (f.sigma y)) (f.mK y-f.mg y)
def leadingLapseField (f : MassFields) : Point → ℝ := fun y => (-1/2:ℝ)*f.mr y
def leadingUField (f : MassFields) : Point → ℝ := fun y => leadingDField f y+leadingLapseField f y

lemma leadingDField_diff {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (f.sigma x) ≠ 0) : ContDiffAt ℝ 2 (leadingDField f) x := by
  have hs := hf.sigma.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hg := hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact (traceProduct_diff (inverse_diff_at hs h0) hg).const_smul (-3/4:ℝ)
lemma leadingTField_diff {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (f.sigma x) ≠ 0) : ContDiffAt ℝ 2 (leadingTField f) x := by
  have hs := hf.sigma.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hg := hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  exact (traceProduct_diff (inverse_diff_at hs h0) (hf.mK.sub hg)).const_smul (1/2:ℝ)
lemma leadingLapseField_diff {f : MassFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (leadingLapseField f) x := hf.mr.const_smul (-1/2:ℝ)
lemma leadingUField_diff {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (f.sigma x) ≠ 0) : ContDiffAt ℝ 2 (leadingUField f) x :=
  (leadingDField_diff hf h0).add (leadingLapseField_diff hf)

lemma leadingDField_realized {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (f.sigma x) ≠ 0) :
    actualScalarJet (leadingDField f) x = leadingD (massInputOf f x) := by
  have hs := hf.sigma.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hg := hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at hs h0
  unfold leadingDField leadingD
  rw [actualScalarJet_smul _ (traceProduct_diff hi hg),actual_traceProductJet hi hg,
    actual_inverseJets hs h0]
  rfl
lemma leadingTField_realized {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (f.sigma x) ≠ 0) :
    actualScalarJet (leadingTField f) x = leadingT (massInputOf f x) := by
  have hs := hf.sigma.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hg := hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3)
  have hi := inverse_diff_at hs h0
  unfold leadingTField leadingT
  rw [actualScalarJet_smul _ (traceProduct_diff hi (hf.mK.sub hg)),
    actual_traceProductJet hi (hf.mK.sub hg),actual_inverseJets hs h0]
  have hsub : matrixScalarJets (fun y => f.mK y-f.mg y) x =
      matrixScalarJets f.mK x-matrixScalarJets f.mg x := by
    funext i j
    exact actualScalarJet_sub (contDiffAt_pi.mp (contDiffAt_pi.mp hf.mK i) j) (contDiffAt_pi.mp (contDiffAt_pi.mp hg i) j)
  rw [hsub]
  rfl
lemma leadingLapseField_realized {f : MassFields} {x : Point} (hf : f.RegularAt x) :
    actualScalarJet (leadingLapseField f) x = leadingLapse (massInputOf f x) := by
  exact actualScalarJet_smul _ hf.mr
lemma leadingUField_realized {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (f.sigma x) ≠ 0) :
    actualScalarJet (leadingUField f) x = leadingU (massInputOf f x) := by
  unfold leadingUField leadingU
  rw [actualScalarJet_add (leadingDField_diff hf h0) (leadingLapseField_diff hf),
    leadingDField_realized hf h0,leadingLapseField_realized hf]

end
end CKSMixedGeometry

end

end OAI
