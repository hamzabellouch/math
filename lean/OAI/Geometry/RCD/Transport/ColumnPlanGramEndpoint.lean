import OAI.Geometry.RCD.Harmonic.GramQuadraticDefect
import OAI.Geometry.RCD.Heat.ACDerivativeL2Endpoint
import OAI.Geometry.RCD.Transport.CompressedSegmentIntegral
import OAI.Geometry.RCD.Transport.TestPlanLocalProperty

namespace OAI

/-! # Scalar column endpoints controlled by the integrated Gram defect -/

open Set Filter MeasureTheory
open scoped InnerProductSpace ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem column_plan_gram_endpoint (μ : Measure X) (Q : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ Q) (v : X → Euclidean n) (hv : Continuous v)
    (hu : ∀ i, SobolevSpace.toLp μ Q (u i) =ᵐ[μ] fun x => v x i)
    (a : Euclidean n) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C≠∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {Ω : Set X} (hΩ : MeasurableSet Ω)
    (hstay : ∀ᵐ γ ∂π, ∀ t : Time, γ t∈Ω)
    (hE : IntegrableOn (gramDefect μ Q u) Ω μ) :
    ∀ᵐ γ ∂π,
      ⟪v (γ 1)-v (γ 0),a⟫_ℝ^2≤(dist (γ 0) (γ 1))^2*‖a‖^2*
        (1+∫ t in Icc (0:ℝ) 1, gramDefect μ Q u (geodesicExtension γ t)) := by
  let g := sobolevColumnMap μ Q u a
  let φ x := ⟪v x,a⟫_ℝ
  have hφ : Continuous φ := hv.inner continuous_const
  have hg : SobolevSpace.toLp μ Q g =ᵐ[μ] φ := by
    simpa only [Measure.restrict_univ] using sobolevColumnMap_representative μ Q u univ v
      (fun i => by simpa only [Measure.restrict_univ] using hu i) a
  have hgrad : ∀ᵐ x ∂μ.restrict Ω,
      (SobolevSpace.minimalSlope μ Q g x)^2≤‖a‖^2*(1+gramDefect μ Q u x) := by
    filter_upwards [ae_restrict_of_ae (localGamma_column_defect μ Q u a),
      ae_restrict_of_ae (localGamma_self μ Q g)] with x hx he
    rw [← he]
    have hh := (abs_le.mp hx).2
    dsimp only [g]
    nlinarith
  have htime := testPlan_eval_property_on μ π hcomp hΩ hstay hgrad
  have hstay' (t : Time) : ∀ᵐ x ∂π.map (fun γ => γ t), x∈Ω := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable hΩ).mpr
    filter_upwards [hstay] with γ hγ
    exact hγ t
  have hEI := (compressed_segment_integral μ π hC hcomp hstay' hE
    (Eventually.of_forall (gramDefect_nonneg μ Q u))).2.1
  have hd := (SobolevSpace.minimalSlope_isRelaxed μ Q g).testPlan_ae_derivative
    μ π hgeo hC hcomp hD hφ hg
  have hac := (SobolevSpace.minimalSlope_isRelaxed μ Q g).testPlan_ae_absolutelyContinuous
    μ π hgeo hC hcomp hD hφ hg
  filter_upwards [hd,hac,htime,hEI] with γ hd hac htime hEI
  have htime' := (ae_restrict_iff' measurableSet_Icc).mp htime
  have hder : ∀ᵐ t : ℝ, t∈Ioo (0:ℝ) 1 →
      (deriv (fun s => φ (geodesicExtension γ s)) t-0)^2≤
        (dist (γ 0) (γ 1)*‖a‖)^2*(1+gramDefect μ Q u (geodesicExtension γ t)) := by
    filter_upwards [hd,htime'] with t ht hg htI
    have hs := mul_self_le_mul_self (abs_nonneg _) (ht htI).2
    have hb := mul_le_mul_of_nonneg_left (hg (Ioo_subset_Icc_self htI)) (sq_nonneg (dist (γ 0) (γ 1)))
    calc
      _≤(dist (γ 0) (γ 1))^2*(SobolevSpace.minimalSlope μ Q g (geodesicExtension γ t))^2 := by
        simpa only [sub_zero,← pow_two,sq_abs,mul_pow] using hs
      _≤_ := by convert hb using 1; ring
  have h1 : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Icc (0:ℝ) 1) := integrableOn_const (by simp)
  have h0 : IntegrableOn (fun _ : ℝ => (0:ℝ)) (Icc (0:ℝ) 1) := integrableOn_const (by simp)
  have hI : IntegrableOn (fun t => 1+gramDefect μ Q u (geodesicExtension γ t)) (Icc (0:ℝ) 1) :=
    h1.add hEI
  have hh := ac_endpoint_L2_error hac.1 h0 hI hder
  have he0 : geodesicExtension γ 0=γ 0 := geodesicExtension_eq γ (0:Time)
  have he1 : geodesicExtension γ 1=γ 1 := geodesicExtension_eq γ (1:Time)
  have hi1 : (∫ _t in Icc (0:ℝ) 1, (1:ℝ))=1 := by simp
  have hi : (∫ t in Icc (0:ℝ) 1, 1+gramDefect μ Q u (geodesicExtension γ t))=
      1+∫ t in Icc (0:ℝ) 1, gramDefect μ Q u (geodesicExtension γ t) := by
    rw [integral_add h1 hEI,hi1]
  simp only [integral_zero,sub_zero,he0,he1,φ,← inner_sub_left,hi,mul_pow] at hh
  exact hh

end RegularPointCoordinates

end

end OAI
