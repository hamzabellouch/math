import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.ConstraintCanonical
import OAI.Geometry.Relativity.CKS.SchwarzschildRoundMetric
import OAI.Geometry.Relativity.CKS.SchwarzschildBoundary
import OAI.Geometry.Relativity.CKS.SchwarzschildHorizon
import OAI.Geometry.Relativity.CKS.SurfaceBarrier
import OAI.Geometry.Relativity.CKS.SurfaceParameter
import OAI.Geometry.Relativity.CKS.TransferDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildRadialDecay

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology InnerProductSpace
namespace CKSMain
open CKSSchwarzschild
attribute [local instance] manifold_regular
attribute [local instance] CKSIntrinsicConstraints.halfSpaceDimension_neZero
attribute [local instance] CKSSpatialManifold.real_id_isometric
  CKSLorentz.real_smulCommClass CKSLorentz.spatialDual_smulCommClass

lemma coefficientAtlas_exists {N : Type*} [TopologicalSpace N] [ChartedSpace H3 N]
    [IsManifold I3 ∞ N] {q : SmoothMetric I3 (M := N)} {k : InnerField I3 (M := N)}
    (h : PhysicalDEC I3 q.inner k) : Nonempty (CoefficientAtlas q k) := by
  classical
  exact ⟨fun x => Classical.choose (chart_exists_of_DECAt (h x))⟩

def schwarzschildAtlas {m : ℝ} (hm : 0 < m) :
    CoefficientAtlas (smoothMetric hm) (tensorInner m) :=
  let atlas : ∀ p, ConstraintChart (metricInner m) (tensorInner m) p := fun p => {
    domain := univ
    coordinate := position m
    metric := cartMetric m
    tensor := cartTensor m
    isOpen := isOpen_univ
    mem := mem_univ p
    smooth := by
      run_tac do
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.setType (← Lean.Core.betaReduce (← Lean.instantiateMVars (← goal.getType)))
        let mass := Lean.mkIdent `m
        Lean.Elab.Tactic.evalTactic (← `(tactic| exact (position_smooth $mass).contMDiffOn))
    fullRank := by
      run_tac do
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.setType (← Lean.Core.betaReduce (← Lean.instantiateMVars (← goal.getType)))
        let mass := Lean.mkIdent `m
        let massPositive := Lean.mkIdent `hm
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          exact fun _ _ =>
            endInner_fullRank (smoothMetric $massPositive) (position $mass) (cartMetric $mass) rfl))
    coefficientSmooth := by
      run_tac do
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.setType (← Lean.Core.betaReduce (← Lean.instantiateMVars (← goal.getType)))
        let mass := Lean.mkIdent `m
        let massPositive := Lean.mkIdent `hm
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          exact fun y _ =>
            ⟨cartMetric_smoothAt $massPositive
              (by rw [norm_position $massPositive]; exact radius_ge $mass y),
             cartTensor_smoothAt $massPositive
              (by rw [norm_position $massPositive]; exact radius_ge $mass y)⟩))
    positiveSymmetric := by
      run_tac do
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.setType (← Lean.Core.betaReduce (← Lean.instantiateMVars (← goal.getType)))
        let mass := Lean.mkIdent `m
        let massPositive := Lean.mkIdent `hm
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          exact fun y _ => ⟨cartMetric_symm $mass _,
            cartMetric_pos $massPositive
              (by rw [norm_position $massPositive]; exact radius_ge $mass y),
            cartTensor_symm $mass _⟩))
    represents := by
      exact fun _ _ => ⟨rfl,rfl⟩ }
  atlas

def horizonNormal (p : Boundary Exterior) : TangentSpace I3 p.val :=
  EuclideanSpace.single 0 1

lemma horizon_radius {m : ℝ} (hm : 0 < m) (p : Boundary Exterior) :
    ‖position m p.val‖ = 2*m := by simp [norm_position hm,radius,boundary_height p]

lemma horizonNormal_coordinate {m : ℝ} (hm : 0 < m) (p : Boundary Exterior) :
    mfderiv I3 𝓘(ℝ,E3) (position m) p.val (horizonNormal p) =
      radialNormal m (position m p.val) := by
  have hd : dropPlane (EuclideanSpace.single 0 1) = 0 := by
    ext i
    simp [dropPlane_apply]
  have hz : ambientDerivative directionAmbient p.val (EuclideanSpace.single 0 1) = 0 := by
    change mfderiv I3 𝓘(ℝ,E3) directionAmbient p.val (EuclideanSpace.single 0 1) = 0
    rw [mfderiv_directionAmbient]
    change mfderiv I2 𝓘(ℝ,E3) (Subtype.val : CKSSchwarzschild.Sphere → E3) p.val.2
      (dropPlane (EuclideanSpace.single 0 1)) = 0
    rw [hd]
    change (mfderiv I2 𝓘(ℝ,E3) (Subtype.val : CKSSchwarzschild.Sphere → E3) p.val.2)
      (0 : TangentSpace I2 p.val.2) = 0
    exact map_zero _
  change ambientDerivative (position m) p.val (EuclideanSpace.single 0 1) = _
  rw [mfderiv_position,hz]
  simp [radialNormal,horizon_radius hm p,lapse_horizon hm,radialUnit_position hm]

def schwarzschildBoundary {m : ℝ} (hm : 0 < m) :
    BoundaryGeometry (smoothMetric hm) (tensorInner m) where
  normal := horizonNormal
  unit p := by
    change cartMetric m (position m p.val)
      (mfderiv I3 𝓘(ℝ,E3) (position m) p.val (horizonNormal p))
      (mfderiv I3 𝓘(ℝ,E3) (position m) p.val (horizonNormal p)) = 1
    rw [horizonNormal_coordinate hm p]
    exact radialNormal_unit hm (by rw [horizon_radius hm p])
  orthogonal p a := by
    change cartMetric m (position m p.val)
      (mfderiv I3 𝓘(ℝ,E3) (position m) p.val (horizonNormal p))
      (mfderiv I3 𝓘(ℝ,E3) (position m) p.val
        (mfderiv I2 I3 (Subtype.val : Boundary Exterior → Exterior) p a)) = 0
    rw [horizonNormal_coordinate hm p,(CKSBoundarySurface.inclusion_hasMFDeriv p).mfderiv]
    apply radialNormal_orthogonal
    exact (position_radial_inner hm p.val (liftPlane a)).trans (liftPlane_zero a)
  inward p := by change 0 < (EuclideanSpace.single 0 1 : E3) 0; simp
  chart p := schwarzschildAtlas hm p.val
  normal_smooth p := by
    change ContMDiffAt I2 𝓘(ℝ,E3) ∞
      (fun z : Boundary Exterior =>
        mfderiv I3 𝓘(ℝ,E3) (position m) z.val (horizonNormal z)) p
    have he : (fun z : Boundary Exterior =>
        mfderiv I3 𝓘(ℝ,E3) (position m) z.val (horizonNormal z)) =
        directionAmbient ∘ (Subtype.val : Boundary Exterior → Exterior) := by
      funext z
      rw [horizonNormal_coordinate hm z]
      simp [radialNormal,horizon_radius hm z,lapse_horizon hm,radialUnit_position hm]
      rfl
    rw [he]
    exact (directionAmbient_smooth.comp CKSBoundarySurface.inclusion_smooth) p

lemma constant_radius_hessian {f : E2 → E3} {y : E2}
    (hf : ContDiffAt ℝ ∞ f y) (hn : ∀ z, ‖f z‖ = ‖f y‖) (a : E2) :
    ⟪f y, fderiv ℝ (fun z => fderiv ℝ f z a) y a⟫_ℝ =
      -⟪fderiv ℝ f y a,fderiv ℝ f y a⟫_ℝ := by
  have hc : ContDiffAt ℝ ∞ (fun t : ℝ => f (y+t•a)) 0 := by
    have hh : ContDiffAt ℝ ∞ f (y+(0:ℝ)•a) := by simpa using hf
    exact hh.comp 0 (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have he : (fun t : ℝ => ‖f (y+t•a)‖^2) = (fun _ : ℝ => ‖f y‖^2) :=
    funext (fun t => congrArg (fun r : ℝ => r^2) (hn (y+t•a)))
  have h := curve_normSq_second hc
  rw [he,line_second_deriv hf a,line_deriv (hf.differentiableAt (by simp)) a] at h
  simp only [deriv_const',deriv_const,zero_smul,add_zero] at h
  linarith

lemma constant_radius_second_form {m : ℝ} (hm : 0 < m)
    {f : E2 → E3} {y : E2} (hf : ContDiffAt ℝ ∞ f y)
    (hn : ∀ z, ‖f z‖ = ‖f y‖) (hr : 2*m ≤ ‖f y‖)
    (a : E2) (ha : cartMetric m (f y) (fderiv ℝ f y a) (fderiv ℝ f y a) = 1) :
    parameterSecondForm m f y (radialNormal m (f y)) a a = lapse m ‖f y‖/‖f y‖ := by
  have hmax : IsLocalMax (fun z => ‖f z‖^2) y :=
    Filter.Eventually.of_forall (fun z => by dsimp; rw [hn z])
  have ht := maximum_radius_tangent (hf.differentiableAt (by simp)) hmax a
  have hau : ⟪fderiv ℝ f y a,fderiv ℝ f y a⟫_ℝ = 1 := by
    rwa [cartMetric_tangent m _ _ _ ht] at ha
  have hh := constant_radius_hessian hf hn a
  rw [hau] at hh
  have hs : ⟪radialUnit (f y),fderiv ℝ (fun z => fderiv ℝ f z a) y a⟫_ℝ = -1/‖f y‖ := by
    simp only [radialUnit,real_inner_smul_left,hh,div_eq_mul_inv]
    ring
  rw [parameterSecondForm,metric_normal_pair hm hr,christoffel_tangent_radial hm hr _ _ ht ht,
    hau,mul_one,hs]
  have hu := lapse_pos hm hr
  have hp : 0 < ‖f y‖ := lt_of_lt_of_le (by positivity) hr
  field_simp
  ring

lemma constant_radius_mean {m : ℝ} (hm : 0 < m)
    {f : E2 → E3} {y : E2} (hf : ContDiffAt ℝ ∞ f y)
    (hn : ∀ z, ‖f z‖ = ‖f y‖) (hr : 2*m ≤ ‖f y‖)
    (hi : Function.Injective (fderiv ℝ f y)) :
    parameterMeanCurvature m f y (radialNormal m (f y)) = 2*lapse m ‖f y‖/‖f y‖ := by
  have ha := constant_radius_second_form hm hf hn hr _ (firstFrame_unit _ _ (cartMetric_pos hm hr) hi)
  have hb := constant_radius_second_form hm hf hn hr _ (secondFrame_unit _ _ (cartMetric_pos hm hr) hi)
  dsimp only [parameterMeanCurvature]
  rw [ha,hb]
  ring

lemma schwarzschildMarginal {m : ℝ} (hm : 0 < m) :
    MarginalBoundary (smoothMetric hm) (tensorInner m) := by
  refine ⟨schwarzschildBoundary hm,?_⟩
  intro p
  let F : Boundary Exterior → E3 := position m ∘ Subtype.val
  let f := surfaceParameter F p
  let y := (extChartAt I2 p) p
  have hf := surfaceParameter_smooth ((position_smooth m).comp CKSBoundarySurface.inclusion_smooth) p
  change ContDiffAt ℝ ∞ f y at hf
  have hy : f y = position m p.val := surfaceParameter_center F p
  have hn (z : E2) : ‖f z‖ = 2*m := horizon_radius hm ((extChartAt I2 p).symm z)
  have hc : ∀ z, ‖f z‖ = ‖f y‖ := fun z => (hn z).trans (hn y).symm
  have hi : Function.Injective (fderiv ℝ f y) := by
    rw [surfaceParameter_derivative ((position_smooth m).comp CKSBoundarySurface.inclusion_smooth)]
    rw [mfderiv_comp p ((position_smooth m).mdifferentiable (by simp) _)
      (CKSBoundarySurface.inclusion_smooth.mdifferentiable (by simp) _)]
    exact (position_derivative_injective hm _).comp (CKSBoundarySurface.inclusion_mfderiv_injective p)
  have hr : 2*m ≤ ‖f y‖ := (hn y).ge
  have hH := constant_radius_mean hm hf hc hr hi
  have hmax : IsLocalMax (fun z => ‖f z‖^2) y :=
    Filter.Eventually.of_forall (fun z => by dsimp; rw [hc z])
  have hK := tangent_surface_tensor_trace hm (hf.differentiableAt (by simp)) hmax hr hi
  change parameterMeanCurvature m f y
      (mfderiv I3 𝓘(ℝ,E3) (position m) p.val (horizonNormal p)) + parameterTensorTrace m f y = 0
  rw [horizonNormal_coordinate hm p,← hy,hH,hK,hn y,lapse_horizon hm,velocity_near m _ (by linarith)]
  ring

end CKSMain

end

end OAI
