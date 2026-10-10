import OAI.Geometry.Relativity.CKS.CKSLogData

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant inverse determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def sourceMetric (f : SourceMassFields) (y : Point) : Matrix (Fin 3) (Fin 3) ℝ :=
  CKSAngularGeometry.metricBlock (sourceRadialMetric f y) (f.b y) (sourceGamma f y)

lemma sourceMetric_pullback (f : SourceMassFields) (x : Point) :
    sourceMetric f (logRadiusChart x) = logMetric f.logFields x := by
  have hq := congrFun (sourceGamma_pullback f) x
  have hr := congrFun (sourceRadialMetric_pullback f) x
  unfold sourceMetric logMetric
  rw [hq,hr]
  rfl

lemma sourceGamma_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y) (hy : y 0 ≠ 0) :
    ContDiffAt ℝ 3 (sourceGamma f) y := by
  have hr : ContDiffAt ℝ 3 (fun z : Point => z 0) y := by fun_prop
  exact (((hr.pow 2).smul (angularLift_diff hf.sigma)).add
      ((contDiffAt_const.fun_div hr hy).smul (angularLift_diff hf.mg))).add hf.eg

def sourceShift (f : SourceMassFields) : Point → Angle := fun y a =>
  ∑ b, inverse (sourceGamma f y) a b*f.b y b

def sourceSchur (f : SourceMassFields) : Point → ℝ := fun y =>
  sourceRadialMetric f y-∑ i, ∑ k, inverse (sourceGamma f y) i k*(f.b y i*f.b y k)

def sourceGammaRadial (f : SourceMassFields) : Point → Mat := radialMatrixD (sourceGamma f)

def sourceExpansion (f : SourceMassFields) : Point → ℝ := fun y =>
  (y 0)/4*traceProduct (inverse (sourceGamma f y))
    (sourceGammaRadial f y-(show Mat from normalizedLie (sourceGamma f) (sourceShift f) y))

def sourcePhysicalMass (f : SourceMassFields) : Point → ℝ := fun y =>
  (y 0)/2*(1+((y 0)/2*traceProduct (inverse (sourceGamma f y)) (sourceTangentialK f y))^2-
    ((1/Real.sqrt (sourceSchur f y))*sourceExpansion f y)^2)

lemma sourceShift_regular {f : SourceMassFields} {y : Point} (hf : f.RegularAt y) (hy : y 0 ≠ 0)
    (h0 : determinant (sourceGamma f y) ≠ 0) : ContDiffAt ℝ 3 (sourceShift f) y := by
  have hi := inverse_diff_at (sourceGamma_regular hf hy) h0
  apply contDiffAt_pi.mpr
  intro a
  exact ContDiffAt.sum fun b _ => (component_diff hi a b).mul (contDiffAt_pi.mp hf.b b)

lemma sourceShift_pullback (f : SourceMassFields) :
    (fun y => sourceShift f (logRadiusChart y)) = logShift f.logFields := by
  funext x a
  unfold sourceShift logShift
  have hq := congrFun (sourceGamma_pullback f) x
  rw [hq]
  rfl

lemma sourceSchur_pullback (f : SourceMassFields) :
    (fun y => sourceSchur f (logRadiusChart y)) = logSchur f.logFields := by
  funext x
  unfold sourceSchur logSchur
  have hq := congrFun (sourceGamma_pullback f) x
  have hr := congrFun (sourceRadialMetric_pullback f) x
  rw [hq,hr]
  rfl

lemma normalizedLie_pullback {q : Point → Mat} {S : Point → Angle} {x : Point}
    (hq : ContDiffAt ℝ 1 q (logRadiusChart x)) (hS : ContDiffAt ℝ 1 S (logRadiusChart x)) (i k : A) :
    normalizedLie (fun y => q (logRadiusChart y)) (fun y => S (logRadiusChart y)) x i k =
      normalizedLie q S (logRadiusChart x) i k := by
  unfold normalizedLie
  apply Finset.sum_congr rfl
  intro a _
  have hqd (i k : A) := (component_diff hq i k).differentiableAt (by norm_num)
  have hSd (i : A) := (contDiffAt_pi.mp hS i).differentiableAt (by norm_num)
  erw [D_pullback a.succ (hqd i k),D_pullback i.succ (hSd a),D_pullback k.succ (hSd a)]
  simp [scaledD,radialFactor]

lemma sourceGammaRadial_pullback {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x)) :
    sourceGammaRadial f (logRadiusChart x) = logGammaRadial f.logFields x := by
  rw [source_logGammaRadial_actual hf,← sourceGamma_pullback]
  funext i k
  change D (basis 0) (fun y => sourceGamma f y i k) (logRadiusChart x) =
    (1/Real.exp (x 0))*D (basis 0) (fun y => sourceGamma f (logRadiusChart y) i k) x
  have hr : (logRadiusChart x) 0 ≠ 0 := by simp [logRadiusChart]
  have hd := (component_diff (sourceGamma_regular hf hr) i k).differentiableAt (by norm_num)
  erw [D_pullback 0 hd]
  simp [scaledD,radialFactor,logRadiusChart]

lemma sourceExpansion_pullback {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x))
    (h0 : determinant (sourceGamma f (logRadiusChart x)) ≠ 0) :
    sourceExpansion f (logRadiusChart x) = logExpansion f.logFields x := by
  have hr : (logRadiusChart x) 0 ≠ 0 := by simp [logRadiusChart]
  have hq := sourceGamma_regular hf hr
  have hS := sourceShift_regular hf hr h0
  have hLie : (show Mat from normalizedLie (sourceGamma f) (sourceShift f) (logRadiusChart x)) =
      (show Mat from normalizedLie (logGamma f.logFields) (logShift f.logFields) x) := by
    funext i k
    rw [← sourceGamma_pullback,← sourceShift_pullback]
    exact (normalizedLie_pullback (hq.of_le (by norm_num)) (hS.of_le (by norm_num)) i k).symm
  unfold sourceExpansion logExpansion
  rw [sourceGammaRadial_pullback hf,hLie]
  have hγ := congrFun (sourceGamma_pullback f) x
  rw [hγ]
  rfl

lemma sourcePhysicalMass_pullback {f : SourceMassFields} {x : Point}
    (hf : f.RegularAt (logRadiusChart x))
    (hp : (sourceMetric f (logRadiusChart x)).PosDef) :
    sourcePhysicalMass f (logRadiusChart x) = logPhysicalMass f.logFields x := by
  have h0 : determinant (sourceGamma f (logRadiusChart x)) ≠ 0 := by
    rw [determinant_eq]
    exact (CKSAngularGeometry.metricBlock_leaf_posDef hp).det_pos.ne'
  unfold sourcePhysicalMass logPhysicalMass
  rw [sourceExpansion_pullback hf h0]
  have hγ := congrFun (sourceGamma_pullback f) x
  have hk := congrFun (sourceTangentialK_pullback f) x
  have hs := congrFun (sourceSchur_pullback f) x
  rw [hγ,hk,hs]
  rfl

end
end CKSMixedGeometry

end

end OAI
