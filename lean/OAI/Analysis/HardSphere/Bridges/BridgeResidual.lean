import Mathlib
import OAI.Analysis.HardSphere.Bridges.PrefixMap
import OAI.Analysis.HardSphere.Bridges.WienerGaussian
import OAI.Analysis.HardSphere.Geometry.ConfigurationPath

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def centerMap : C(Time,ℝ) →L[ℝ] C(Time,ℝ) :=
  ContinuousLinearMap.id ℝ _ - (ContinuousMap.evalCLM ℝ (1:Time)).smulRight linearPath

@[simp] lemma centerMap_apply (f : C(Time,ℝ)) (s : Time) :
    centerMap f s=f s-(s:ℝ)*f 1 := by
  change f s-f 1*(s:ℝ)=_
  ring

lemma centerMap_path (ω : Noise) : centerMap (path ω)=bridge ω := by
  ext s
  simpa only [centerMap_apply] using (bridge_apply ω s).symm

lemma bridgeLaw_center : bridgeLaw=wiener.map centerMap := by
  rw [bridgeLaw,wiener,Measure.map_map centerMap.continuous.measurable measurable_path]
  congr 1
  funext ω
  exact (centerMap_path ω).symm

instance bridgeLaw_isGaussian : IsGaussian bridgeLaw := by
  rw [bridgeLaw_center]
  infer_instance

lemma finite_bridge_gaussian {ι : Type*} [Fintype ι] (t : ι → Time) :
    HasGaussianLaw (fun ω i ↦ bridge ω (t i)) law := by
  classical
  let loc : Option ι → Time := fun i ↦ i.elim 1 t
  let L : (Option ι → ℝ) →L[ℝ] (ι → ℝ) := ContinuousLinearMap.pi
    (fun i ↦ ContinuousLinearMap.proj (some i) - (t i:ℝ) • ContinuousLinearMap.proj none)
  convert! (finite_path_gaussian loc).map_fun L using 1
  funext ω i
  simp [L,loc,bridge_apply]

lemma bridge_eval_law (t : Time) :
    HasLaw (fun ω ↦ bridge ω t) (gaussianReal 0 (Real.toNNReal ((t:ℝ)-(t:ℝ)^2))) law := by
  simpa only [Fintype.sum_unique,mul_one,one_mul,min_self,pow_two] using
    bridge_projection_law (fun _ : Unit ↦ (1:ℝ)) (fun _ ↦ t)

lemma bridge_covariance (s t : Time) :
    cov[fun ω ↦ bridge ω s,fun ω ↦ bridge ω t;law]=min (s:ℝ) (t:ℝ)-(s:ℝ)*(t:ℝ) := by
  have hp (v : Time) := (path_eval_law v).hasGaussianLaw.memLp_two
  simp only [bridge_apply]
  rw [covariance_fun_sub_fun_sub (hp s) ((hp 1).const_mul (s:ℝ)) (hp t) ((hp 1).const_mul (t:ℝ))]
  simp only [covariance_const_mul_left,covariance_const_mul_right,path_covariance]
  have hs : min (s:ℝ) (1:ℝ)=(s:ℝ) := min_eq_left s.property.2
  have ht : min (1:ℝ) (t:ℝ)=(t:ℝ) := min_eq_right t.property.2
  change min (s:ℝ) (t:ℝ)-(t:ℝ)*min (s:ℝ) 1-(s:ℝ)*min 1 (t:ℝ)+(t:ℝ)*((s:ℝ)*min (1:ℝ) 1)=_
  rw [hs,ht,min_self]
  ring

def bridgeRemainder (u : Time) : C(Time,ℝ) →L[ℝ] C(Time,ℝ) :=
  ContinuousMap.compCLM ℝ ℝ (suffixTime u) - (ContinuousMap.evalCLM ℝ u).smulRight (1-linearPath)

@[simp] lemma bridgeRemainder_apply (u : Time) (f : C(Time,ℝ)) (s : Time) :
    bridgeRemainder u f s=f (suffixTime u s)-(1-(s:ℝ))*f u := by
  change f (suffixTime u s)-f u*(1-(s:ℝ))=_
  ring

lemma bridgeRemainder_eq (u : Time) (ω : Noise) :
    bridgeRemainder u (bridge ω)=centerMap (suffixMap u (path ω)) := by
  ext s
  simp only [bridgeRemainder_apply,bridge_apply,centerMap_apply,suffixMap_apply]
  have he : suffixTime u 1=1 := by apply Subtype.ext; change (u:ℝ)+(1-(u:ℝ))*1=1; ring
  rw [he]
  change path ω (suffixTime u s)-((u:ℝ)+(1-(u:ℝ))*(s:ℝ))*path ω 1-
    (1-(s:ℝ))*(path ω u-(u:ℝ)*path ω 1)=_
  ring

lemma bridgeRemainder_law (u : Time) :
    law.map (fun ω ↦ bridgeRemainder u (bridge ω)) =
      bridgeLaw.map (fun β ↦ Real.sqrt (1-(u:ℝ)) • β) := by
  calc
    _ = (law.map (fun ω ↦ suffixMap u (path ω))).map centerMap := by
      rw [Measure.map_map (f:=fun ω ↦ suffixMap u (path ω)) centerMap.continuous.measurable
        ((suffixMap u).continuous.measurable.comp measurable_path)]
      congr 1
      funext ω
      exact bridgeRemainder_eq u ω
    _ = (law.map (fun ω ↦ Real.sqrt (1-(u:ℝ)) • path ω)).map centerMap := by rw [suffix_law]
    _ = _ := by
      rw [Measure.map_map (f:=fun ω ↦ Real.sqrt (1-(u:ℝ)) • path ω) centerMap.continuous.measurable
        ((show Continuous (fun w : C(Time,ℝ) ↦ Real.sqrt (1-(u:ℝ)) • w) from by fun_prop).measurable.comp measurable_path),bridgeLaw,
        Measure.map_map (by fun_prop) measurable_bridge]
      congr 1
      funext ω
      exact (centerMap.map_smul _ _).trans (congrArg (fun β ↦ Real.sqrt (1-(u:ℝ)) • β) (centerMap_path ω))

lemma bridgeRemainder_joint_gaussian (u : Time) :
    IsGaussianProcess (Sum.elim (fun _ : Unit ↦ fun ω ↦ bridge ω u)
      (fun s ω ↦ bridgeRemainder u (bridge ω) s)) law := by
  classical
  constructor
  intro I
  let loc : Option I → Time := fun i ↦ i.elim u (fun j ↦ j.val.elim (fun _ ↦ u) (suffixTime u))
  let ev (i : Option I) : (Option I → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let L : (Option I → ℝ) →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi
    (fun j ↦ match j.val with
      | .inl _ => ev (some j)
      | .inr s => ev (some j) - (1-(s:ℝ)) • ev none)
  convert! (finite_bridge_gaussian loc).map_fun L using 1
  funext ω j
  cases hj : j.val <;> simp [L,loc,ev,hj]

lemma bridgeRemainder_independent (u : Time) :
    IndepFun (fun ω ↦ bridge ω u) (fun ω ↦ bridgeRemainder u (bridge ω)) law := by
  have hc (_ : Unit) (s : Time) :
      cov[fun ω ↦ bridge ω u,fun ω ↦ bridgeRemainder u (bridge ω) s;law]=0 := by
    simp only [bridgeRemainder_apply]
    rw [covariance_fun_sub_right (bridge_eval_law u).hasGaussianLaw.memLp_two
      (bridge_eval_law _).hasGaussianLaw.memLp_two ((bridge_eval_law u).hasGaussianLaw.memLp_two.const_mul _),
      covariance_const_mul_right,bridge_covariance,bridge_covariance,min_self,min_eq_left (le_suffixTime u s)]
    change (u:ℝ)-(u:ℝ)*((u:ℝ)+(1-(u:ℝ))*(s:ℝ))-(1-(s:ℝ))*((u:ℝ)-(u:ℝ)*(u:ℝ))=0
    ring
  have hi := (bridgeRemainder_joint_gaussian u).indepFun_of_covariance_eq_zero
    (fun _ ↦ ((continuous_eval_const u).measurable.comp measurable_bridge).aemeasurable)
    (fun s ↦ ((continuous_eval_const s).measurable.comp ((bridgeRemainder u).continuous.measurable.comp measurable_bridge)).aemeasurable) hc
  have hid := hi.comp (measurable_pi_apply ())
    (Measurable.of_eval fun index ↦ measurable_pi_apply (TopologicalSpace.denseSeq Time index))
  have hh := hid.comp measurable_id denseEval_embedding.measurable_invFun
  convert hh using 1
  · rfl
  · funext ω
    exact (denseEval_embedding.leftInverse_invFun _).symm

end HardSphere.Wiener

namespace HardSphere
open Wiener

def coordinateBridge (N : ℕ) : Measure (CoordinatePaths N) := Measure.pi (fun _ ↦ bridgeLaw)
instance coordinateBridge_probability (N : ℕ) : IsProbabilityMeasure (coordinateBridge N) := by
  unfold coordinateBridge
  infer_instance

def gaussianCoordinates (N : ℕ) : Measure (Direction N → ℝ) := Measure.pi (fun _ ↦ gaussianReal 0 1)
instance gaussianCoordinates_probability (N : ℕ) : IsProbabilityMeasure (gaussianCoordinates N) := by
  unfold gaussianCoordinates
  infer_instance

def reconstructCoordinates (N : ℕ) (p : (Direction N → ℝ)×CoordinatePaths N) : CoordinatePaths N :=
  fun j ↦ p.1 j • linearPath+p.2 j

lemma reconstructCoordinates_continuous (N : ℕ) : Continuous (reconstructCoordinates N) := by
  unfold reconstructCoordinates
  fun_prop

lemma reconstructCoordinates_preserving (N : ℕ) :
    MeasurePreserving (reconstructCoordinates N) ((gaussianCoordinates N).prod (coordinateBridge N)) (coordinateWiener N) := by
  refine ⟨(reconstructCoordinates_continuous N).measurable,?_⟩
  have h := measurePreserving_arrowProdEquivProdArrow ℝ C(Time,ℝ) (Direction N)
    (fun _ ↦ gaussianReal 0 1) (fun _ ↦ bridgeLaw)
  change (Measure.prod (Measure.pi (fun _ : Direction N ↦ gaussianReal 0 1))
    (Measure.pi (fun _ : Direction N ↦ bridgeLaw))).map _=Measure.pi (fun _ ↦ wiener)
  rw [←h.map_eq,Measure.map_map (reconstructCoordinates_continuous N).measurable h.measurable]
  change (Measure.pi (fun _ : Direction N ↦ (gaussianReal 0 1).prod bridgeLaw)).map
    (fun p j ↦ (p j).1 • linearPath+(p j).2)=_
  rw [Measure.pi_map_pi (fun _ ↦ (show Measurable (fun p : ℝ×C(Time,ℝ) ↦ p.1 • linearPath+p.2) from by fun_prop).aemeasurable)]
  simp_rw [←wiener_disintegration]

lemma bridge_endpoints : ∀ᵐ β ∂bridgeLaw, β (0:Time)=0 ∧ β (1:Time)=0 := by
  have hm : MeasurableSet {β : C(Time,ℝ) | β (0:Time)=0 ∧ β (1:Time)=0} :=
    ((isClosed_eq (continuous_eval_const (0:Time)) continuous_const).inter (isClosed_eq (continuous_eval_const (1:Time)) continuous_const)).measurableSet
  rw [bridgeLaw,ae_map_iff measurable_bridge.aemeasurable hm]
  exact ae_of_all _ (fun ω ↦ ⟨bridge_at_zero ω,bridge_at_one ω⟩)

lemma coordinateBridge_endpoints (N : ℕ) :
    ∀ᵐ β ∂coordinateBridge N, ∀j, β j (0:Time)=0 ∧ β j (1:Time)=0 := by
  apply ae_all_iff.mpr
  intro j
  exact (measurePreserving_eval (fun _ : Direction N ↦ bridgeLaw) j).quasiMeasurePreserving.ae bridge_endpoints

lemma reconstruct_free_endpoints (N : ℕ) (L : Length) (t : ℝ) :
    ∀ᵐ β ∂coordinateBridge N, ∀ z : Direction N → ℝ, ∀ X : Configuration N L,
      freeTrajectory N L t (reconstructCoordinates N (z,β)) X 0=X ∧
      freeTrajectory N L t (reconstructCoordinates N (z,β)) X 1=
        fun i j ↦ X i j+((Real.sqrt (2*t)*z (i,j):ℝ):AddCircle L.val) := by
  filter_upwards [coordinateBridge_endpoints N] with β hβ z X
  constructor <;> ext i j
  · change X i j+((Real.sqrt (2*t)*(z (i,j)*0+β (i,j) 0):ℝ):AddCircle L.val)=X i j
    rw [(hβ (i,j)).1]
    simp
  · change X i j+((Real.sqrt (2*t)*(z (i,j)*1+β (i,j) 1):ℝ):AddCircle L.val)=_
    rw [(hβ (i,j)).2]
    simp

end HardSphere

end

end OAI
