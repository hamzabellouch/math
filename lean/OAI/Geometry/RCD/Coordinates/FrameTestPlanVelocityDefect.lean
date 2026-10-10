import OAI.Geometry.RCD.Coordinates.CoordinatePathVelocity
import OAI.Geometry.RCD.Harmonic.AffinePathDerivative
import OAI.Geometry.RCD.Transport.TestPlanLocalProperty

namespace OAI

/-! # Scalar velocities with the actual finite frame errors -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem frame_testPlan_velocity_defect (μ : Measure X) (Q : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ Q) (g : SobolevSpace μ Q)
    (v : X → Euclidean n) (φ : X → ℝ) (hv : Continuous v) (hφ : Continuous φ)
    (hu : ∀ i, SobolevSpace.toLp μ Q (u i) =ᵐ[μ] fun x => v x i)
    (hg : SobolevSpace.toLp μ Q g =ᵐ[μ] φ)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C≠∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π) :
    ∀ᵐ γ ∂π, ∀ᵐ s : ℝ, s∈Ioo (0:ℝ) 1 →
      DifferentiableAt ℝ (fun r => φ (geodesicExtension γ r)) s ∧
      (deriv (fun r => φ (geodesicExtension γ r)) s-
        ⟪gradientFrameCoefficients μ Q u g (geodesicExtension γ s),
          coordinateDerivative (fun r => v (geodesicExtension γ r)) s⟫_ℝ)^2≤
        (dist (γ 0) (γ 1))^2*(|frameEnergyError μ Q u g (geodesicExtension γ s)|+
          gramDefect μ Q u (geodesicExtension γ s)*
            ‖gradientFrameCoefficients μ Q u g (geodesicExtension γ s)‖^2) := by
  let b : ℕ → Euclidean n := denseSeq (Euclidean n)
  let f (k : ℕ) := g-sobolevColumnMap μ Q u (b k)
  let ψ (k : ℕ) (x : X) := φ x-⟪v x,b k⟫_ℝ
  have hψ (k : ℕ) : Continuous (ψ k) := hφ.sub (hv.inner continuous_const)
  have hf (k : ℕ) : SobolevSpace.toLp μ Q (f k) =ᵐ[μ] ψ k := by
    have hcol := sobolevColumnMap_representative μ Q u univ v
      (fun i => by simpa only [Measure.restrict_univ] using hu i) (b k)
    rw [Measure.restrict_univ] at hcol
    change SobolevSpace.toLpCLM μ Q (g-sobolevColumnMap μ Q u (b k)) =ᵐ[μ] _
    rw [map_sub]
    filter_upwards [hg,hcol,Lp.coeFn_sub (SobolevSpace.toLp μ Q g)
      (SobolevSpace.toLp μ Q (sobolevColumnMap μ Q u (b k)))] with x hx hy hz
    exact hz.trans (congrArg₂ (·-·) hx hy)
  have hres (k : ℕ) := (SobolevSpace.minimalSlope_isRelaxed μ Q (f k)).testPlan_ae_derivative
    μ π hgeo hC hcomp hD (hψ k) (hf k)
  have henergy (k : ℕ) : ∀ᵐ γ ∂π, ∀ᵐ s : ℝ, s∈Icc (0:ℝ) 1 →
      (SobolevSpace.minimalSlope μ Q (f k) (geodesicExtension γ s))^2≤
        ‖gradientFrameCoefficients μ Q u g (geodesicExtension γ s)-b k‖^2+
        |frameEnergyError μ Q u g (geodesicExtension γ s)|+
        gramDefect μ Q u (geodesicExtension γ s)*‖b k‖^2 := by
    have he : ∀ᵐ x ∂μ, (SobolevSpace.minimalSlope μ Q (f k) x)^2≤
        ‖gradientFrameCoefficients μ Q u g x-b k‖^2+|frameEnergyError μ Q u g x|+
          gramDefect μ Q u x*‖b k‖^2 := by
      filter_upwards [frame_residual_energy_le μ Q u g (b k),localGamma_self μ Q (f k)] with x hx hy
      exact hy.symm.trans_le hx
    have ht := testPlan_eval_property_on μ π hcomp MeasurableSet.univ
      (Eventually.of_forall (fun _ _ => mem_univ _))
      (show ∀ᵐ x ∂μ.restrict univ, _ from by simpa only [Measure.restrict_univ] using he)
    filter_upwards [ht] with γ hγ
    exact (ae_restrict_iff' measurableSet_Icc).mp hγ
  have hcoordinate (i : Fin n) :=
    (SobolevSpace.minimalSlope_isRelaxed μ Q (u i)).testPlan_ae_derivative μ π hgeo hC hcomp hD
      ((EuclideanSpace.proj i).continuous.comp hv) (hu i)
  have hd := (SobolevSpace.minimalSlope_isRelaxed μ Q g).testPlan_ae_derivative
    μ π hgeo hC hcomp hD hφ hg
  filter_upwards [hd,ae_all_iff.mpr hres,ae_all_iff.mpr henergy,ae_all_iff.mpr hcoordinate]
    with γ hd hr he hco
  have hr' : ∀ᵐ s : ℝ, ∀ k, s∈Ioo (0:ℝ) 1 →
      DifferentiableAt ℝ (fun r => ψ k (geodesicExtension γ r)) s ∧
      |deriv (fun r => ψ k (geodesicExtension γ r)) s|≤
        dist (γ 0) (γ 1)*SobolevSpace.minimalSlope μ Q (f k) (geodesicExtension γ s) :=
    ae_all_iff.mpr hr
  filter_upwards [hd,hr',ae_all_iff.mpr he,ae_all_iff.mpr hco] with s hds hrs hes hcos hs
  have hdiff := (hds hs).1
  refine ⟨hdiff,?_⟩
  apply velocity_defect_of_dense_residual_bounds
    (gradientFrameCoefficients μ Q u g (geodesicExtension γ s))
    (coordinateDerivative (fun r => v (geodesicExtension γ r)) s) _ (dist (γ 0) (γ 1))
    |frameEnergyError μ Q u g (geodesicExtension γ s)|
    (gramDefect μ Q u (geodesicExtension γ s)) (denseRange_denseSeq (Euclidean n))
  rintro _ ⟨k,rfl⟩
  have hi := coordinate_inner_hasDerivAt (fun r => v (geodesicExtension γ r))
    (fun i => (hcos i hs).1) (b k)
  have hsub : HasDerivAt (fun r => ψ k (geodesicExtension γ r))
      (deriv (fun r => φ (geodesicExtension γ r)) s-
        ⟪b k,coordinateDerivative (fun r => v (geodesicExtension γ r)) s⟫_ℝ) s := by
    simpa only [ψ,real_inner_comm] using! hdiff.hasDerivAt.sub hi
  have hb := (hrs k hs).2
  rw [hsub.deriv] at hb
  have hsq := mul_self_le_mul_self (abs_nonneg _) hb
  rw [← sq,← sq,mul_pow,sq_abs] at hsq
  exact hsq.trans (mul_le_mul_of_nonneg_left (hes k (Ioo_subset_Icc_self hs)) (sq_nonneg _))

end RegularPointCoordinates

end

end OAI
