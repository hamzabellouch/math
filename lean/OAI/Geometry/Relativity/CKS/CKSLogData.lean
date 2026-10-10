import OAI.Geometry.Relativity.CKS.LogRadialIdentity
import OAI.Geometry.Relativity.CKS.CKSScaledBounds

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

structure SourceMassFields where
  sigma : Angle → Mat
  mg : Angle → Mat
  mK : Angle → Mat
  mr : Angle → ℝ
  eg : Point → Mat
  ek : Point → Mat
  b : Point → Angle
  err : Point → ℝ

def SourceMassFields.logFields (f : SourceMassFields) : MassFields where
  sigma := angularLift f.sigma
  mg := angularLift f.mg
  mK := angularLift f.mK
  mr := angularLift f.mr
  eg := fun y => f.eg (logRadiusChart y)
  ek := fun y => f.ek (logRadiusChart y)
  b := fun y => f.b (logRadiusChart y)
  err := fun y => f.err (logRadiusChart y)
  er := 0

lemma angularProjection_logRadiusChart (x : Point) :
    angularProjection (logRadiusChart x) = angularProjection x := by
  ext a
  simp [angularProjection,logRadiusChart]

structure SourceMassFields.RegularAt (f : SourceMassFields) (y : Point) : Prop where
  sigma : ContDiffAt ℝ 3 f.sigma (angularProjection y)
  mg : ContDiffAt ℝ 3 f.mg (angularProjection y)
  mK : ContDiffAt ℝ 2 f.mK (angularProjection y)
  mr : ContDiffAt ℝ 2 f.mr (angularProjection y)
  eg : ContDiffAt ℝ 3 f.eg y
  ek : ContDiffAt ℝ 2 f.ek y
  b : ContDiffAt ℝ 3 f.b y
  err : ContDiffAt ℝ 2 f.err y

lemma source_logFields_regular {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x)) : f.logFields.RegularAt x := by
  have hσ := hf.sigma
  have hmg := hf.mg
  have hmk := hf.mK
  have hmr := hf.mr
  rw [angularProjection_logRadiusChart] at hσ hmg hmk hmr
  have hc3 := ((logRadiusChart_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).contDiffAt (x := x))
  have hc2 := ((logRadiusChart_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt (x := x))
  exact ⟨angularLift_diff hσ,angularLift_diff hmg,hf.eg.comp x hc3,contDiffAt_const,
    angularLift_diff hmk,hf.ek.comp x hc2,hf.b.comp x hc3,angularLift_diff hmr,hf.err.comp x hc2⟩

lemma source_logGammaRadial_actual {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x)) :
    logGammaRadial f.logFields x = (1/Real.exp (x 0)) • radialMatrixD (logGamma f.logFields) x := by
  have hσ := hf.sigma
  have hmg := hf.mg
  rw [angularProjection_logRadiusChart] at hσ hmg
  exact logGammaRadial_actual (source_logFields_regular hf)
    (radialMatrixD_angularLift (hσ.of_le (by norm_num)))
    (radialMatrixD_angularLift (hmg.of_le (by norm_num)))

def sourceGamma (f : SourceMassFields) : Point → Mat := fun y =>
  (y 0)^2 • f.sigma (angularProjection y)+(1/(y 0)) • f.mg (angularProjection y)+f.eg y

def sourceTangentialK (f : SourceMassFields) : Point → Mat := fun y =>
  (y 0)^2 • f.sigma (angularProjection y)+(1/(y 0)) • f.mK (angularProjection y)+f.ek y

def sourceRadialMetric (f : SourceMassFields) : Point → ℝ := fun y =>
  1/(1+(y 0)^2)+f.mr (angularProjection y)/(y 0)^5+f.err y

lemma sourceGamma_pullback (f : SourceMassFields) :
    (fun y => sourceGamma f (logRadiusChart y)) = logGamma f.logFields := by
  funext y
  simp [sourceGamma,logGamma,SourceMassFields.logFields,angularLift,
    angularProjection_logRadiusChart,logRadiusChart]

lemma sourceTangentialK_pullback (f : SourceMassFields) :
    (fun y => sourceTangentialK f (logRadiusChart y)) = logTangentialK f.logFields := by
  funext y
  simp [sourceTangentialK,logTangentialK,SourceMassFields.logFields,angularLift,
    angularProjection_logRadiusChart,logRadiusChart]

lemma sourceRadialMetric_pullback (f : SourceMassFields) :
    (fun y => sourceRadialMetric f (logRadiusChart y)) = logRadialMetric f.logFields := by
  funext y
  simp [sourceRadialMetric,logRadialMetric,SourceMassFields.logFields,angularLift,
    angularProjection_logRadiusChart,logRadiusChart]

structure SourceMassFields.ComponentBounds (f : SourceMassFields) (B : ℝ) (y : Point) : Prop where
  eg : ∀ i k, ScaledComponentBound (fun z => f.eg z i k) 3 2 B y
  ek : ∀ i k, ScaledComponentBound (fun z => f.ek z i k) 2 2 B y
  b : ∀ a, ScaledComponentBound (fun z => f.b z a) 3 3 B y
  err : ScaledComponentBound f.err 2 6 B y

lemma source_log_remainder_bounds {f : SourceMassFields} {x : Point} {B : ℝ} (hB : 0 ≤ B)
    (hf : f.RegularAt (logRadiusChart x)) (hb : f.ComponentBounds B (logRadiusChart x)) :
    ‖matrixThreeJets f.logFields.eg x‖ ≤ B/Real.exp (x 0)^2 ∧
    ‖matrixScalarJets f.logFields.ek x‖ ≤ B/Real.exp (x 0)^2 ∧
    ‖fun a => actualThreeJet (fun y => f.logFields.b y a) x‖ ≤ B/Real.exp (x 0)^3 ∧
    ‖actualScalarJet f.logFields.err x‖ ≤ B/Real.exp (x 0)^6 := by
  refine ⟨source_matrix_three_bound hB hf.eg hb.eg,source_matrix_two_bound hB hf.ek hb.ek,?_,
    source_two_jet_bound hB hf.err hb.err⟩
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  exact source_three_jet_bound hB (contDiffAt_pi.mp hf.b a) (hb.b a)

end
end CKSMixedGeometry

end

end OAI
