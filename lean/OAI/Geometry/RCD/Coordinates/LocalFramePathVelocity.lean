import OAI.Geometry.RCD.Coordinates.FrameTestPlanVelocityDefect
import OAI.Geometry.RCD.Coordinates.FrameVelocityErrorLocality

namespace OAI

/-! # Scalar path derivatives for local coordinate representatives -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem local_frame_path_velocity (μ : Measure X) (Q : QuadraticCheegerEnergy μ)
    {n : ℕ} (u U : Fin n → SobolevSpace μ Q) (g : SobolevSpace μ Q)
    (v W : X → Euclidean n) (φ : X → ℝ) (hW : Continuous W) (hφ : Continuous φ)
    (hU : ∀ i, SobolevSpace.toLp μ Q (U i) =ᵐ[μ] fun x => W x i)
    (hg : SobolevSpace.toLp μ Q g =ᵐ[μ] φ)
    {Ω : Set X} (hΩ : MeasurableSet Ω)
    (hu : ∀ i, SobolevSpace.toLp μ Q (U i) =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q (u i))
    (hv : EqOn W v Ω)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C≠∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (hstay : ∀ᵐ γ ∂π, ∀ t : Time, γ t∈Ω) :
    ∀ᵐ γ ∂π,
      AbsolutelyContinuousOnInterval (fun t => φ (geodesicExtension γ t)) 0 1 ∧
      (∀ i, AbsolutelyContinuousOnInterval (fun t => v (geodesicExtension γ t) i) 0 1) ∧
      ∀ᵐ t : ℝ, t∈Ioo (0:ℝ) 1 →
        (deriv (fun s => φ (geodesicExtension γ s)) t-
          ∑ i, localGamma μ Q (u i) g (geodesicExtension γ t)*
            deriv (fun s => v (geodesicExtension γ s) i) t)^2≤
          (dist (γ 0) (γ 1))^2*frameVelocityError μ Q u g (geodesicExtension γ t) := by
  have hvel := frame_testPlan_velocity_defect μ Q U g W φ hW hφ hU hg π hgeo hC hcomp hD
  have hf := (SobolevSpace.minimalSlope_isRelaxed μ Q g).testPlan_ae_absolutelyContinuous
    μ π hgeo hC hcomp hD hφ hg
  have hc (i : Fin n) := (SobolevSpace.minimalSlope_isRelaxed μ Q (U i)).testPlan_ae_absolutelyContinuous
    μ π hgeo hC hcomp hD ((EuclideanSpace.proj i).continuous.comp hW) (hU i)
  have hG (i : Fin n) := localGamma_pair_congr_ae μ Q (hu i)
    (show SobolevSpace.toLp μ Q g =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q g
      from Eventually.of_forall (fun _ => rfl))
  have hloc : ∀ᵐ x ∂μ.restrict Ω,
      frameVelocityError μ Q U g x=frameVelocityError μ Q u g x ∧
      ∀ i, localGamma μ Q (U i) g x=localGamma μ Q (u i) g x :=
    (frameVelocityError_frame_congr_ae μ Q g hu).and (ae_all_iff.mpr hG)
  have hp := testPlan_eval_property_on μ π hcomp hΩ hstay hloc
  filter_upwards [hvel,hf,ae_all_iff.mpr hc,hstay,hp] with γ hvel hf hc hstay hp
  have heq : (fun t => W (geodesicExtension γ t))=(fun t => v (geodesicExtension γ t)) := by
    funext t
    exact hv (hstay (Set.projIcc 0 1 zero_le_one t))
  refine ⟨hf.1,?_,?_⟩
  · intro i
    have heqi := congrArg (fun F : ℝ → Euclidean n => fun t => F t i) heq
    exact heqi ▸ (hc i).1
  · have hp' := (ae_restrict_iff' measurableSet_Icc).mp hp
    filter_upwards [hvel,hp'] with t ht hp htI
    have hb := (ht htI).2
    change _≤(dist (γ 0) (γ 1))^2*frameVelocityError μ Q U g (geodesicExtension γ t) at hb
    rw [(hp (Ioo_subset_Icc_self htI)).1] at hb
    have hvect : gradientFrameCoefficients μ Q U g (geodesicExtension γ t)=
        gradientFrameCoefficients μ Q u g (geodesicExtension γ t) :=
      congrArg (WithLp.toLp 2) (funext (hp (Ioo_subset_Icc_self htI)).2)
    rw [hvect] at hb
    have hder : coordinateDerivative (fun s => W (geodesicExtension γ s)) t=
        coordinateDerivative (fun s => v (geodesicExtension γ s)) t := congrArg (fun F => coordinateDerivative F t) heq
    rw [hder] at hb
    simpa only [gradientFrameCoefficients,coordinateDerivative,PiLp.inner_apply,
      RCLike.inner_apply,conj_trivial,mul_comm] using hb

end RegularPointCoordinates

end

end OAI
