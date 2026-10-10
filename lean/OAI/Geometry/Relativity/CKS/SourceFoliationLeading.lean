import OAI.Geometry.Relativity.CKS.CKSFoliationLeadingFields
import OAI.Geometry.Relativity.CKS.CKSLogData

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant inverse)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def sourceLeadingD (f : SourceMassFields) : Point → ℝ := leadingDField f.logFields

def sourceLeadingT (f : SourceMassFields) : Point → ℝ := leadingTField f.logFields

def sourceLeadingLapse (f : SourceMassFields) : Point → ℝ := leadingLapseField f.logFields

def sourceLeadingU (f : SourceMassFields) : Point → ℝ := leadingUField f.logFields

lemma sourceLeadingD_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y)
    (h0 : determinant (f.sigma (angularProjection y)) ≠ 0) : ContDiffAt ℝ 2 (sourceLeadingD f) y := by
  have hs := angularLift_diff (hf.sigma.of_le (by norm_num : (2:ℕ∞ω) ≤ 3))
  have hg := angularLift_diff (hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3))
  exact (traceProduct_diff (inverse_diff_at hs h0) hg).const_smul (-3/4:ℝ)
lemma sourceLeadingT_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y)
    (h0 : determinant (f.sigma (angularProjection y)) ≠ 0) : ContDiffAt ℝ 2 (sourceLeadingT f) y := by
  have hs := angularLift_diff (hf.sigma.of_le (by norm_num : (2:ℕ∞ω) ≤ 3))
  have hg := angularLift_diff (hf.mg.of_le (by norm_num : (2:ℕ∞ω) ≤ 3))
  have hk := angularLift_diff hf.mK
  exact (traceProduct_diff (inverse_diff_at hs h0) (hk.sub hg)).const_smul (1/2:ℝ)
lemma sourceLeadingLapse_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y) :
    ContDiffAt ℝ 2 (sourceLeadingLapse f) y := (angularLift_diff hf.mr).const_smul (-1/2:ℝ)
lemma sourceLeadingU_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y)
    (h0 : determinant (f.sigma (angularProjection y)) ≠ 0) : ContDiffAt ℝ 2 (sourceLeadingU f) y :=
  (sourceLeadingD_regular hf h0).add (sourceLeadingLapse_regular hf)

lemma sourceLeadingD_pullback (f : SourceMassFields) (x : Point) :
    sourceLeadingD f (logRadiusChart x) = leadingDField f.logFields x := by
  simp only [sourceLeadingD,leadingDField,SourceMassFields.logFields,angularLift,angularProjection_logRadiusChart]
lemma sourceLeadingT_pullback (f : SourceMassFields) (x : Point) :
    sourceLeadingT f (logRadiusChart x) = leadingTField f.logFields x := by
  simp only [sourceLeadingT,leadingTField,SourceMassFields.logFields,angularLift,angularProjection_logRadiusChart]
lemma sourceLeadingLapse_pullback (f : SourceMassFields) (x : Point) :
    sourceLeadingLapse f (logRadiusChart x) = leadingLapseField f.logFields x := by
  simp only [sourceLeadingLapse,leadingLapseField,SourceMassFields.logFields,angularLift,angularProjection_logRadiusChart]
lemma sourceLeadingU_pullback (f : SourceMassFields) (x : Point) :
    sourceLeadingU f (logRadiusChart x) = leadingUField f.logFields x := by
  exact congrArg₂ (·+·) (sourceLeadingD_pullback f x) (sourceLeadingLapse_pullback f x)

end
end CKSMixedGeometry

end

end OAI
