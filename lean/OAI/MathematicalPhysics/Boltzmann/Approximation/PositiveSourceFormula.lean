import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLossScaling
import OAI.MathematicalPhysics.Boltzmann.Branching.CompactParameterConvergence
import OAI.MathematicalPhysics.Boltzmann.Branching.RadialReflectionChangeVariables
import OAI.MathematicalPhysics.Boltzmann.Collision.SphereDirectionAbsolute
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedKernelAction
import OAI.MathematicalPhysics.Boltzmann.Model
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.WithDensity
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Sequences

namespace OAI

section

/-! # Positive gain comparison retaining the principal input action -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem chartGain_le_principal_add_remainders
    {c d e k : Measure Velocity} (hcd : c ≤ d+e+k)
    (q : ℝ) (v : Velocity) {f : Velocity → ℝ≥0∞} (hf : ∀ p, f p ≤ 1) :
    chartGain c (fun p => ENNReal.ofReal (H q p/H q v)*f p) v ≤
      chartGain d (fun p => ENNReal.ofReal (H q p/H q v)*f p) v+
      normalizedChartGain e q v+normalizedChartGain k q v := by
  apply (chartGain_mono_measure hcd _ v).trans
  rw [chartGain_add_measure,chartGain_add_measure]
  have h (μ : Measure Velocity) :
      chartGain μ (fun p => ENNReal.ofReal (H q p/H q v)*f p) v ≤
        normalizedChartGain μ q v := by
    apply chartGain_mono_right
    intro p
    simpa only [mul_one] using mul_le_mul' le_rfl (hf p)
  exact add_le_add (add_le_add le_rfl (h e)) (h k)

end BoltzmannNonuniqueness

end

end

section

/-! # Finite positive measures associated with integrable collision densities -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

def positiveDensityMeasure (μ : Measure X) (f : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (f x))

theorem positiveDensityMeasure_finite {μ : Measure X} {f : X → ℝ}
    (hi : Integrable f μ) (hn : ∀ᵐ x ∂μ, 0 ≤ f x) :
    IsFiniteMeasure (positiveDensityMeasure μ f) := by
  exact isFiniteMeasure_withDensity ((hasFiniteIntegral_iff_ofReal hn).mp hi.2).ne

theorem positiveDensityMeasure_integral {μ : Measure X} {f : X → ℝ}
    (hm : AEMeasurable f μ) (hn : ∀ᵐ x ∂μ, 0 ≤ f x) (ψ : X → ℝ) :
    (∫ x, ψ x ∂positiveDensityMeasure μ f) = ∫ x, ψ x*f x ∂μ := by
  rw [positiveDensityMeasure,integral_withDensity_eq_integral_toReal_smul₀ hm.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hn] with x hx
  rw [ENNReal.toReal_ofReal hx,smul_eq_mul,mul_comm]

end BoltzmannNonuniqueness

end

end

section

/-! # A bounded comparison variable for two positive characteristic equations -/
noncomputable section
namespace BoltzmannNonuniqueness.TransportPrimitive

def positiveDifference (u v : ℝ) : ℝ := (u-v)/(1+u+v)

def positiveDifferenceDamping (u v a b k l e f : ℝ) : ℝ :=
  (a+b+e+f+(k+l)/2)/(1+u+v)

def positiveDifferenceForcing (u v a b k l e f : ℝ) : ℝ :=
  (a-b+e-f)/(1+u+v)+(l-k)*(u+v+4*u*v)/(2*(1+u+v)^2)

theorem positiveDifference_derivative_identity {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (a b k l e f : ℝ) :
    (((a-k*u+e)-(b-l*v+f))*(1+u+v)-
      (u-v)*((a-k*u+e)+(b-l*v+f)))/(1+u+v)^2 =
      positiveDifferenceForcing u v a b k l e f-
        positiveDifferenceDamping u v a b k l e f*positiveDifference u v := by
  have hd : (1+u+v) ≠ 0 := by positivity
  unfold positiveDifferenceForcing positiveDifferenceDamping positiveDifference
  field_simp
  ring

theorem positiveDifference_damping_nonneg {u v a b k l e f : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hk : 0 ≤ k) (hl : 0 ≤ l) (he : 0 ≤ e) (hf : 0 ≤ f) :
    0 ≤ positiveDifferenceDamping u v a b k l e f := by
  unfold positiveDifferenceDamping
  positivity

theorem positiveDifference_forcing_bound {u v a b k l e f : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (he : 0 ≤ e) (hf : 0 ≤ f) :
    |positiveDifferenceForcing u v a b k l e f| ≤
      |a-b|/(1+u+v)+e/(1+u)+f/(1+v)+|k-l| := by
  let d := 1+u+v
  have hd : 0 < d := by dsimp [d]; positivity
  have hp : 0 ≤ u+v+4*u*v := by positivity
  have hp' : u+v+4*u*v ≤ 2*d^2 := by dsimp [d]; nlinarith [sq_nonneg (u-v)]
  have hc : (u+v+4*u*v)/(2*d^2) ≤ 1 := (div_le_one (by positivity)).mpr hp'
  have hfq : |(l-k)*(u+v+4*u*v)/(2*d^2)| ≤ |k-l| := by
    rw [mul_div_assoc,abs_mul,abs_of_nonneg (div_nonneg hp (by positivity)),abs_sub_comm]
    exact mul_le_of_le_one_right (abs_nonneg _) hc
  have hab : |a-b+e-f| ≤ |a-b|+e+f := by
    calc
      _ ≤ |a-b+e|+|f| := abs_sub _ _
      _ ≤ (|a-b|+|e|)+|f| := add_le_add (abs_add_le _ _) le_rfl
      _ = _ := by rw [abs_of_nonneg he,abs_of_nonneg hf]
  have heq : e/d ≤ e/(1+u) := div_le_div_of_nonneg_left he (by positivity) (by dsimp [d]; linarith)
  have hfq' : f/d ≤ f/(1+v) := div_le_div_of_nonneg_left hf (by positivity) (by dsimp [d]; linarith)
  calc
    _ ≤ |(a-b+e-f)/d|+|(l-k)*(u+v+4*u*v)/(2*d^2)| := abs_add_le _ _
    _ ≤ (|a-b|+e+f)/d+|k-l| := by
      gcongr
      · rw [abs_div,abs_of_pos hd]
        exact div_le_div_of_nonneg_right hab hd.le
    _ = |a-b|/d+e/d+f/d+|k-l| := by ring
    _ ≤ _ := by dsimp [d] at *; linarith

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # Nonnegative smooth compact tests determine finite phase measures -/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

theorem positive_smooth_compact_approximation {f : X → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hn : ∀ x, 0 ≤ f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      (∀ x, 0 ≤ g x) ∧ ∀ x, |g x-f x| ≤ 2*ε := by
  obtain ⟨g,hg,hgf⟩ := (hc.uniformContinuous_of_continuous hf).exists_contDiff_dist_le hε
  obtain ⟨R,hR,hball⟩ := hc.isBounded.subset_ball_lt 0 (0 : X)
  let b : ContDiffBump (0 : X) := ⟨R,R+1,hR,by linarith⟩
  have hbf (x : X) : b x*f x = f x := by
    by_cases hx : x ∈ tsupport f
    · rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall (hball hx)),one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero]
  have hgε (x : X) : |g x-f x| < ε := by
    simpa only [Real.dist_eq] using hgf x
  refine ⟨fun x => b x*(g x+ε),b.contDiff.mul (hg.add contDiff_const),
    b.hasCompactSupport.mul_right,?_,?_⟩
  · intro x
    have := (abs_lt.mp (hgε x)).1
    exact mul_nonneg b.nonneg (by linarith [hn x])
  · intro x
    have he : b x*(g x+ε)-f x = b x*(g x-f x+ε) := by
      calc
        _ = b x*(g x+ε)-b x*f x := by rw [hbf]
        _ = _ := by ring
    rw [he,abs_mul,abs_of_nonneg b.nonneg]
    have hb : b x ≤ 1 := b.le_one
    have hh : |g x-f x+ε| ≤ 2*ε := by
      calc
        _ ≤ |g x-f x|+|ε| := abs_add_le _ _
        _ ≤ 2*ε := by rw [abs_of_pos hε]; linarith [hgε x]
    exact (mul_le_mul_of_nonneg_left hh b.nonneg).trans (by nlinarith)

variable [MeasurableSpace X] [BorelSpace X]

theorem finite_measure_eq_of_positive_smooth_tests
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : X → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      (∀ x, 0 ≤ f x) → ∫ x, f x ∂μ = ∫ x, f x ∂ν) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro f
  let F : X → ℝ := fun x => (f x : ℝ)
  have hF : Continuous F := NNReal.continuous_coe.comp f.continuous
  have hFc : HasCompactSupport F := f.hasCompactSupport.comp_left rfl
  have hFn : ∀ x, 0 ≤ F x := fun x => (f x).coe_nonneg
  have hFiμ : Integrable F μ := hF.integrable_of_hasCompactSupport hFc
  have hFiν : Integrable F ν := hF.integrable_of_hasCompactSupport hFc
  apply eq_of_abs_sub_le_all
  intro δ hδ
  let ε := δ/(2*(μ.real univ+ν.real univ+1))
  have hmass : 0 < μ.real univ+ν.real univ+1 := by positivity
  have hε : 0 < ε := div_pos hδ (mul_pos (by norm_num) hmass)
  obtain ⟨g,hg,hgc,hgn,hgF⟩ := positive_smooth_compact_approximation hF hFc hFn hε
  have hgiμ : Integrable g μ := hg.continuous.integrable_of_hasCompactSupport hgc
  have hgiν : Integrable g ν := hg.continuous.integrable_of_hasCompactSupport hgc
  have hμ : |(∫ x, F x ∂μ)-(∫ x, g x ∂μ)| ≤ 2*ε*μ.real univ := by
    rw [← integral_sub hFiμ hgiμ]
    change ‖∫ x, F x-g x ∂μ‖ ≤ _
    exact norm_integral_le_of_norm_le_const (ae_of_all μ (fun x => by
      simpa only [Real.norm_eq_abs,abs_sub_comm] using hgF x))
  have hν : |(∫ x, g x ∂ν)-(∫ x, F x ∂ν)| ≤ 2*ε*ν.real univ := by
    rw [← integral_sub hgiν hFiν]
    change ‖∫ x, g x-F x ∂ν‖ ≤ _
    exact norm_integral_le_of_norm_le_const (ae_of_all ν (fun x => by
      simpa only [Real.norm_eq_abs] using hgF x))
  have he : (∫ x, g x ∂μ) = ∫ x, g x ∂ν := h g hg hgc hgn
  calc
    |(∫ x, F x ∂μ)-(∫ x, F x ∂ν)| ≤
        |(∫ x, F x ∂μ)-(∫ x, g x ∂μ)|+
        |(∫ x, g x ∂ν)-(∫ x, F x ∂ν)| := by
      rw [he]
      exact abs_sub_le _ _ _
    _ ≤ 2*ε*(μ.real univ+ν.real univ) := by linarith
    _ ≤ δ := by
      calc
        _ ≤ 2*ε*(μ.real univ+ν.real univ+1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = δ := by
          dsimp [ε]
          field_simp


end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # The angular change of variables on one normal hemisphere -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace BoltzmannNonuniqueness

def positiveReflectionTest (e : Sphere) (f : Sphere → ℝ≥0∞) (n : Sphere) : ℝ≥0∞ :=
  if 0 < inner ℝ e.1 n.1 then
    ENNReal.ofReal (inner ℝ e.1 n.1)*f (normalReflection e n) else 0

theorem positiveReflectionTest_measurable (e : Sphere) {f : Sphere → ℝ≥0∞} (hf : Measurable f) :
    Measurable (positiveReflectionTest e f) := by
  apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
  · exact (show Measurable (fun n : Sphere => ENNReal.ofReal (inner ℝ e.1 n.1)) by fun_prop).mul
      (hf.comp (normalReflection_measurable e))
  · exact measurable_const

theorem sphereBallLift_radialReflection (e n : Sphere) (f : Sphere → ℝ≥0∞)
    (r : Ioi (0:ℝ)) :
    sphereBallLift e f (radialReflection e ((r:ℝ) • n.1)) =
      if (r:ℝ) < 1 then f (normalReflection e n) else 0 := by
  rw [sphereBallLift,sphereDirection_radialReflection e n r.property,
    radialReflection_norm,norm_smul,Real.norm_eq_abs,abs_of_pos r.property,
    mem_sphere_zero_iff_norm.mp n.property,mul_one]
  simp only [sq_lt_one_iff₀ (le_of_lt (show (0:ℝ) < r from r.property))]

theorem north_reflection_radial_integrand (f : Sphere → ℝ≥0∞) (n : Sphere)
    (r : Ioi (0:ℝ)) :
    (if 0 < ((r:ℝ) • n.1) 0 then
      ENNReal.ofReal (8*((r:ℝ) • n.1) 0*‖(r:ℝ) • n.1‖^2)*
        sphereBallLift northSphere f (radialReflection northSphere ((r:ℝ) • n.1)) else 0) =
      (if (r:ℝ) < 1 then ENNReal.ofReal ((r:ℝ)^3) else 0)*
        (8*positiveReflectionTest northSphere f n) := by
  have hrp : (0:ℝ) < r := r.property
  rw [sphereBallLift_radialReflection,norm_smul,Real.norm_eq_abs,abs_of_pos r.property,
    mem_sphere_zero_iff_norm.mp n.property,mul_one]
  simp only [PiLp.smul_apply,smul_eq_mul,positiveReflectionTest,northSphere,
    EuclideanSpace.inner_single_left,map_one,one_mul]
  have hp : 0 < (r:ℝ)*n.1 0 ↔ 0 < n.1 0 := mul_pos_iff_of_pos_left r.property
  simp only [hp]
  by_cases hn : 0 < n.1 0
  · rw [ite_eq_left hn,ite_eq_left hn]
    have hc : ENNReal.ofReal (8*((r:ℝ)*n.1 0)*(r:ℝ)^2) =
        ENNReal.ofReal ((r:ℝ)^3)*(8*ENNReal.ofReal (n.1 0)) := by
      rw [← ENNReal.ofReal_ofNat 8,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8),
        ← ENNReal.ofReal_mul (pow_nonneg hrp.le 3)]
      congr 1
      ring
    rw [hc]
    by_cases hr : (r:ℝ) < 1 <;> simp only [hr,ite_true,ite_false,mul_zero,zero_mul,mul_assoc]
  · simp [hn]

theorem positive_hemisphere_reflection (f : Sphere → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ n, f n ∂sphereArea) = 4*∫⁻ n, positiveReflectionTest northSphere f n ∂sphereArea := by
  have hA := positiveReflectionTest_measurable northSphere hf
  have hM : Measurable (fun x : Velocity => if 0 < x 0 then
      ENNReal.ofReal (8*x 0*‖x‖^2)*sphereBallLift northSphere f (radialReflection northSphere x)
        else 0) := by
    apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
    · exact (show Measurable (fun x : Velocity => ENNReal.ofReal (8*x 0*‖x‖^2)) by fun_prop).mul ((sphereBallLift_measurable northSphere hf).comp
        (radialReflection_continuous northSphere).measurable)
    · exact measurable_const
  have h := lintegral_radialReflection_north (sphereBallLift northSphere f)
  rw [sphereBallLift_integral northSphere hf] at h
  rw [← lintegral_indicator (measurableSet_lt measurable_const (by fun_prop))] at h
  change (3:ℝ≥0∞)⁻¹*(∫⁻ n, f n ∂sphereArea) =
    ∫⁻ x : Velocity, (if 0 < x 0 then _ else 0) at h
  rw [lintegral_velocity_polar hM] at h
  simp_rw [north_reflection_radial_integrand] at h
  rw [radial_cubic_factor (A := fun n => 8*positiveReflectionTest northSphere f n) (measurable_const.mul hA),lintegral_const_mul _ hA] at h
  have hh := congrArg (fun z : ℝ≥0∞ => 3*z) h
  have hthree : (3:ℝ≥0∞)*3⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hscale : (3:ℝ≥0∞)*6⁻¹*8 = 4 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  simpa only [← mul_assoc,hthree,hscale,one_mul] using hh

end BoltzmannNonuniqueness

end

end

section

/-! # A countable positive smooth family determining finite phase measures -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

private abbrev PositivePhaseTest (n : ℕ) :=
  {f : C(Velocity × Velocity,ℝ) // ContDiff ℝ (⊤ : ℕ∞) (f : _ → ℝ) ∧
    tsupport (f : _ → ℝ) ⊆ Metric.closedBall 0 (n+1 : ℝ) ∧ ∀ p, 0 ≤ f p}

private instance (n : ℕ) : Nonempty (PositivePhaseTest n) :=
  ⟨⟨0,contDiff_const,by simp,by simp⟩⟩

private instance (n : ℕ) : SecondCountableTopology (PositivePhaseTest n) :=
  TopologicalSpace.Subtype.secondCountableTopology _

private def positivePhaseSeq (n m : ℕ) : PositivePhaseTest n :=
  TopologicalSpace.denseSeq (PositivePhaseTest n) m

def positivePhaseTest (j : ℕ) : Velocity × Velocity → ℝ :=
  (positivePhaseSeq (Nat.unpair j).1 (Nat.unpair j).2).1

theorem positivePhaseTest_smooth (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (positivePhaseTest j) :=
  (positivePhaseSeq (Nat.unpair j).1 (Nat.unpair j).2).2.1

theorem positivePhaseTest_compact (j : ℕ) : HasCompactSupport (positivePhaseTest j) :=
  (isCompact_closedBall (0 : Velocity × Velocity) ((Nat.unpair j).1+1 : ℝ)).of_isClosed_subset
    (isClosed_tsupport _) (positivePhaseSeq (Nat.unpair j).1 (Nat.unpair j).2).2.2.1

theorem positivePhaseTest_nonneg (j : ℕ) (p : Velocity × Velocity) :
    0 ≤ positivePhaseTest j p :=
  (positivePhaseSeq (Nat.unpair j).1 (Nat.unpair j).2).2.2.2 p

theorem finite_phase_measure_eq_of_countable_tests
    (μ ν : Measure (Velocity × Velocity)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ j, ∫ p, positivePhaseTest j p ∂μ = ∫ p, positivePhaseTest j p ∂ν) : μ = ν := by
  apply finite_measure_eq_of_positive_smooth_tests μ ν
  intro φ hφ hc hn
  obtain ⟨R,_hR,hball⟩ := hc.isBounded.subset_ball_lt 0 (0 : Velocity × Velocity)
  obtain ⟨n,hnR⟩ := exists_nat_gt R
  have hsupp : tsupport φ ⊆ Metric.closedBall (0 : Velocity × Velocity) (n+1 : ℝ) := by
    intro p hp
    have hpR : ‖p‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hball hp
    rw [Metric.mem_closedBall,dist_zero_right]
    linarith
  let t : PositivePhaseTest n := ⟨⟨φ,hφ.continuous⟩,hφ,hsupp,hn⟩
  have hd : DenseRange (positivePhaseSeq n) :=
    TopologicalSpace.denseRange_denseSeq (PositivePhaseTest n)
  obtain ⟨a,ha,hat⟩ := mem_closure_iff_seq_limit.mp (hd t)
  choose b hb using ha
  have hat' : Tendsto (fun m => (positivePhaseSeq n (b m)).1) atTop (𝓝 t.1) := by
    have he : (fun m => positivePhaseSeq n (b m)) = a := funext hb
    have hseq : Tendsto (fun m => positivePhaseSeq n (b m)) atTop (𝓝 t) := by
      rw [he]
      exact hat
    exact continuous_subtype_val.continuousAt.tendsto.comp hseq
  have hμ := tendsto_integral_mul_common_support (integrable_const (1 : ℝ) (μ := μ))
    (isCompact_closedBall (0 : Velocity × Velocity) (n+1 : ℝ))
    (fun m => (positivePhaseSeq n (b m)).2.2.1) hsupp hat'
  have hν := tendsto_integral_mul_common_support (integrable_const (1 : ℝ) (μ := ν))
    (isCompact_closedBall (0 : Velocity × Velocity) (n+1 : ℝ))
    (fun m => (positivePhaseSeq n (b m)).2.2.1) hsupp hat'
  simp only [mul_one] at hμ hν
  have heq (m) : (∫ p, (positivePhaseSeq n (b m)).1 p ∂μ) =
      ∫ p, (positivePhaseSeq n (b m)).1 p ∂ν := by
    have hj := h (Nat.pair n (b m))
    unfold positivePhaseTest at hj
    rw [Nat.unpair_pair] at hj
    exact hj
  simp_rw [heq] at hμ
  exact tendsto_nhds_unique hμ hν

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Finite positive measure histories below a renewal supersolution -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.PositiveMeasureHistories

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem comp_mono_measure (K : Kernel X Y) {μ ν : Measure X} (h : μ ≤ ν) :
    K ∘ₘ μ ≤ K ∘ₘ ν := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA K.aemeasurable,Measure.bind_apply hA K.aemeasurable]
  exact lintegral_mono' h le_rfl

def historySum (K : Kernel X X) (seed : Measure X) : ℕ → Measure X
  | 0 => 0
  | n+1 => seed+K ∘ₘ historySum K seed n

theorem historySum_le (K : Kernel X X) {seed μ : Measure X}
    (h : seed+K ∘ₘ μ ≤ μ) (n : ℕ) : historySum K seed n ≤ μ := by
  induction n with
  | zero => exact bot_le
  | succ n ih => exact (add_le_add le_rfl (comp_mono_measure K ih)).trans h

theorem historySum_succ (K : Kernel X X) (seed : Measure X) (n : ℕ) :
    historySum K seed (n+1) = historySum K seed n+(K^n) ∘ₘ seed := by
  induction n with
  | zero =>
    simp only [historySum,pow_zero,zero_add]
    have hz : K ∘ₘ (0 : Measure X) = 0 := by
      ext A hA
      rw [Measure.bind_apply hA K.aemeasurable,lintegral_zero_measure]
      rfl
    rw [hz,add_zero]
    have hid : (1 : Kernel X X) = Kernel.id := rfl
    rw [hid]
    ext A hA
    rw [Measure.bind_apply hA Kernel.id.aemeasurable]
    simp only [Kernel.id_apply,Measure.dirac_apply' _ hA]
    exact (lintegral_indicator_one hA).symm
  | succ n ih =>
    change seed+K ∘ₘ historySum K seed (n+1) =
      (seed+K ∘ₘ historySum K seed n)+(K^(n+1)) ∘ₘ seed
    rw [ih,Measure.comp_add,Measure.comp_assoc]
    have he : (K ∘ₖ (K^n)) = K^(n+1) := (pow_succ' K n).symm
    rw [he]
    change seed+(K ∘ₘ historySum K seed n+(K^(n+1)) ∘ₘ seed) =
      (seed+K ∘ₘ historySum K seed n)+(K^(n+1)) ∘ₘ seed
    exact (add_assoc _ _ _).symm

theorem historySum_eq_sum (K : Kernel X X) (seed : Measure X) (n : ℕ) :
    historySum K seed n = ∑ j ∈ Finset.range n, (K^j) ∘ₘ seed := by
  induction n with
  | zero => simp [historySum]
  | succ n ih => rw [historySum_succ,Finset.sum_range_succ,ih]

theorem finite_histories_le (K : Kernel X X) {seed μ : Measure X}
    (h : seed+K ∘ₘ μ ≤ μ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (K^j) ∘ₘ seed ≤ μ := by
  rw [← historySum_eq_sum]
  exact historySum_le K h n

theorem endpoint_histories_le (K : Kernel X X) (L : Kernel X Y) {seed μ : Measure X}
    (h : seed+K ∘ₘ μ ≤ μ) (n : ℕ) :
    L ∘ₘ (∑ j ∈ Finset.range n, (K^j) ∘ₘ seed) ≤ L ∘ₘ μ :=
  comp_mono_measure L (finite_histories_le K h n)

end BoltzmannNonuniqueness.PositiveMeasureHistories

end

end

section

/-! # A positive gain-and-retention kernel acting on an occupation density -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

def positiveSourceKernel (K : Kernel X X) [IsSFiniteKernel K] (b r : X → ℝ) : Kernel X X :=
  K.withDensity (fun _ x => ENNReal.ofReal (b x))+
    Kernel.id.withDensity (fun _ x => ENNReal.ofReal (b x*r x))

instance positiveSourceKernel_sFinite (K : Kernel X X) [IsSFiniteKernel K] (b r : X → ℝ) :
    IsSFiniteKernel (positiveSourceKernel K b r) := by
  have : IsSFiniteKernel (K.withDensity (fun _ x => ENNReal.ofReal (b x))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  have : IsSFiniteKernel (Kernel.id.withDensity (fun (_ : X) x => ENNReal.ofReal (b x*r x))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  unfold positiveSourceKernel
  infer_instance

theorem positiveSourceKernel_comp_density (K : Kernel X X) [IsSFiniteKernel K]
    (μ : Measure X) {F b r : X → ℝ} (hF : Measurable F) (hFn : ∀ x, 0 ≤ F x)
    (hb : Measurable b) (hr : Measurable r) :
    positiveSourceKernel K b r ∘ₘ positiveDensityMeasure μ F =
      positiveDensityMeasure (K ∘ₘ positiveDensityMeasure μ F) b+
      positiveDensityMeasure μ (fun x => F x*(b x*r x)) := by
  rw [positiveSourceKernel,Measure.add_comp,← Measure.withDensity_comp hb.ennreal_ofReal,
    ← Measure.withDensity_comp (f' := fun x => ENNReal.ofReal (b x*r x))
      (hb.mul hr).ennreal_ofReal]
  have hid : Kernel.id ∘ₘ positiveDensityMeasure μ F = positiveDensityMeasure μ F := by
    rw [Kernel.id,Measure.deterministic_comp_eq_map measurable_id]
    exact Measure.map_id
  rw [hid]
  congr 1
  unfold positiveDensityMeasure
  rw [← withDensity_mul μ (f := fun x => ENNReal.ofReal (F x))
    (g := fun x => ENNReal.ofReal (b x*r x)) hF.ennreal_ofReal (hb.mul hr).ennreal_ofReal]
  congr 1
  funext x
  exact (ENNReal.ofReal_mul (hFn x)).symm

end BoltzmannNonuniqueness

end

end

section

/-! # Finite collision histories below an occupation renewal equation -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.PositiveMeasureHistories

variable {X : Type*} [MeasurableSpace X]

theorem restrict_kernel_comp (K : Kernel X X) (μ : Measure X)
    {A : Set X} (hA : MeasurableSet A) :
    K.restrict hA ∘ₘ μ = (K ∘ₘ μ).restrict A := by
  ext S hS
  rw [Measure.bind_apply hS (Kernel.aemeasurable _),Measure.restrict_apply hS,
    Measure.bind_apply (hS.inter hA) K.aemeasurable]
  apply lintegral_congr
  intro x
  rw [Kernel.restrict_apply,Measure.restrict_apply hS]

theorem restricted_source_renewal (K R : Kernel X X)
    {occupation source seed : Measure X} {A : Set X} (hA : MeasurableSet A)
    (hoccupation : occupation.restrict A = R ∘ₘ (seed+source.restrict A))
    (hsource : K ∘ₘ occupation ≤ source) :
    seed+((K.restrict hA) ∘ₖ R) ∘ₘ (seed+source.restrict A) ≤ seed+source.restrict A := by
  apply add_le_add le_rfl
  rw [← Measure.comp_assoc,← hoccupation]
  calc
    K.restrict hA ∘ₘ occupation.restrict A ≤ K.restrict hA ∘ₘ occupation :=
      comp_mono_measure _ Measure.restrict_le_self
    _ = (K ∘ₘ occupation).restrict A := restrict_kernel_comp K occupation hA
    _ ≤ source.restrict A := Measure.restrict_mono_measure hsource A

theorem finite_occupation_histories (K R : Kernel X X)
    {occupation source seed : Measure X} {A : Set X} (hA : MeasurableSet A)
    (hoccupation : occupation.restrict A = R ∘ₘ (seed+source.restrict A))
    (hsource : K ∘ₘ occupation ≤ source) (n : ℕ) :
    R ∘ₘ (∑ j ∈ Finset.range n, (((K.restrict hA) ∘ₖ R)^j) ∘ₘ seed) ≤
      occupation.restrict A := by
  rw [hoccupation]
  exact endpoint_histories_le _ R (restricted_source_renewal K R hA hoccupation hsource) n

end BoltzmannNonuniqueness.PositiveMeasureHistories

end

end

section

/-! # Positive density measures under restriction and characteristic transport -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem positiveDensityMeasure_restrict (μ : Measure X) (f : X → ℝ)
    {s : Set X} (hs : MeasurableSet s) :
    positiveDensityMeasure (μ.restrict s) f = positiveDensityMeasure μ (s.indicator f) := by
  unfold positiveDensityMeasure
  rw [← withDensity_indicator hs]
  congr 1
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

theorem positiveDensityMeasure_map_symm (e : X ≃ᵐ Y) {μ : Measure X} {ν : Measure Y}
    (hp : MeasurePreserving e μ ν) {f : Y → ℝ} (hf : Measurable f) :
    (positiveDensityMeasure ν f).map e.symm =
      positiveDensityMeasure μ (fun x => f (e x)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg e.symm.measurable]
  unfold positiveDensityMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ hf.ennreal_ofReal
      (g := fun y => g (e.symm y)) (hg.comp e.symm.measurable),
    lintegral_withDensity_eq_lintegral_mul _ (f := fun x => ENNReal.ofReal (f (e x)))
      (hf.comp e.measurable).ennreal_ofReal hg]
  change (∫⁻ y, ENNReal.ofReal (f y)*g (e.symm y) ∂ν) =
    ∫⁻ x, ENNReal.ofReal (f (e x))*g x ∂μ
  rw [← hp.lintegral_comp (f := fun y => ENNReal.ofReal (f y)*g (e.symm y))
    (hf.ennreal_ofReal.mul (hg.comp e.symm.measurable))]
  apply lintegral_congr
  intro x
  simp only [MeasurableEquiv.symm_apply_apply]

end BoltzmannNonuniqueness

end

end

section

/-! # A bounded density truncation is controlled by the positive-difference metric -/
noncomputable section
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem min_difference_le_positiveDifference {u v K : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hK : 0 ≤ K) :
    |min u K-min v K| ≤ (1+2*K)*|positiveDifference u v| := by
  have hd : 0 < 1+u+v := by positivity
  rw [positiveDifference,abs_div,abs_of_pos hd,← mul_div_assoc]
  apply (le_div_iff₀ hd).mpr
  by_cases huK : u ≤ K
  · rw [min_eq_left huK]
    by_cases hvK : v ≤ K
    · rw [min_eq_left hvK]
      calc
        _ ≤ |u-v| * (1+2*K) :=
          mul_le_mul_of_nonneg_left (by linarith : 1+u+v ≤ 1+2*K) (abs_nonneg _)
        _ = _ := mul_comm _ _
    · have hKv : K ≤ v := le_of_not_ge hvK
      rw [min_eq_right hKv,abs_of_nonpos (sub_nonpos.mpr huK),
        abs_of_nonpos (sub_nonpos.mpr (huK.trans hKv))]
      nlinarith [mul_nonneg (sub_nonneg.mpr hKv)
        (show 0 ≤ 1+K+u by positivity),sq_nonneg (K-u)]
  · have hKu : K ≤ u := le_of_not_ge huK
    rw [min_eq_right hKu]
    by_cases hvK : v ≤ K
    · rw [min_eq_left hvK,abs_of_nonneg (sub_nonneg.mpr hvK),
        abs_of_nonneg (sub_nonneg.mpr (hvK.trans hKu))]
      nlinarith [mul_nonneg (sub_nonneg.mpr hKu)
        (show 0 ≤ 1+K+v by positivity),sq_nonneg (K-v)]
    · rw [min_eq_right (le_of_not_ge hvK),sub_self,abs_zero,zero_mul]
      exact mul_nonneg (by positivity) (abs_nonneg _)

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # A bounded positive source retains its integral bound under pointwise limits -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem positive_integral_limit {a : ℕ → X → ℝ} {b : X → ℝ} {C : ℝ}
    (hai : ∀ n, Integrable (a n) μ) (han : ∀ n, 0 ≤ᵐ[μ] a n)
    (hbm : AEStronglyMeasurable b μ) (hbn : 0 ≤ᵐ[μ] b)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 (b x)))
    (hC : 0 ≤ C) (hb : ∀ n, (∫ x, a n x ∂μ) ≤ C) :
    Integrable b μ ∧ (∫ x, b x ∂μ) ≤ C := by
  have hfatou : (∫⁻ x, ENNReal.ofReal (b x) ∂μ) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (a n x) ∂μ) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (a n x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ht] with x hx
        exact (ENNReal.tendsto_ofReal hx).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le' (fun n => (hai n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hbound : (∫⁻ x, ENNReal.ofReal (b x) ∂μ) ≤ ENNReal.ofReal C := by
    apply hfatou.trans (liminf_le_of_frequently_le _)
    exact (Eventually.of_forall (fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hai n) (han n)]
      exact ENNReal.ofReal_le_ofReal (hb n))).frequently
  have hbi : Integrable b μ := ⟨hbm,(hasFiniteIntegral_iff_ofReal hbn).mpr
    (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hbi,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hbi hbn] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hbound

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A positive cold fraction makes the dilated loss rate bounded at time zero -/

namespace BoltzmannNonuniqueness.Cap

theorem positive_fraction_loss_scaling {r l ell t E H C P ν : ℝ}
    (hr : 0 < r) (hr₁ : r ≤ 1) (hl : l ∈ Set.Icc (0:ℝ) 1)
    (hell : 0 < ell) (hll : ell/2 ≤ l) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hE : 0 ≤ E) (hH : 0 ≤ H) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hν : ν ≤ P*((r*t+r*l+E)*H+C/(r*t+r*l))) :
    r*ν ≤ P*((2+E)*H+2*C/ell) := by
  have htl : 0 < t+l := by linarith [ht.1]
  have hrt : r*t+r*l ≤ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left ht.2 hr.le,
      mul_le_mul_of_nonneg_left hl.2 hr.le]
  have hfirst : r*((r*t+r*l+E)*H) ≤ (2+E)*H := by
    calc
      _ ≤ 1*((r*t+r*l+E)*H) :=
        mul_le_mul_of_nonneg_right hr₁ (mul_nonneg (by nlinarith [ht.1, hl.1]) hH)
      _ ≤ (2+E)*H := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (show r*t+r*l+E ≤ 2+E by linarith) hH
  have hsecond : r*(C/(r*t+r*l)) ≤ 2*C/ell := by
    calc
      _ = C/(t+l) := by rw [← mul_add]; field_simp
      _ ≤ C/(ell/2) := div_le_div_of_nonneg_left hC (by positivity) (by linarith [ht.1])
      _ = 2*C/ell := by ring
  calc
    r*ν ≤ r*(P*((r*t+r*l+E)*H+C/(r*t+r*l))) :=
      mul_le_mul_of_nonneg_left hν hr.le
    _ = P*(r*((r*t+r*l+E)*H)+r*(C/(r*t+r*l))) := by ring
    _ ≤ P*((2+E)*H+2*C/ell) := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hP

end BoltzmannNonuniqueness.Cap


end

section

/-! # Testing the positive gain-and-retention kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem positiveSourceKernel_lintegral (K : Kernel X X) [IsSFiniteKernel K]
    {b r : X → ℝ} (hb : Measurable b) (hr : Measurable r) (x : X)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂positiveSourceKernel K b r x) =
      (∫⁻ y, ENNReal.ofReal (b y)*f y ∂K x)+ENNReal.ofReal (b x*r x)*f x := by
  rw [positiveSourceKernel,add_apply,lintegral_add_measure,
    Kernel.lintegral_withDensity (f := fun (_ : X) y => ENNReal.ofReal (b y)) K
      (hb.ennreal_ofReal.comp measurable_snd) x hf,
    Kernel.lintegral_withDensity (f := fun (_ : X) y => ENNReal.ofReal (b y*r y)) Kernel.id
      ((hb.mul hr).ennreal_ofReal.comp measurable_snd) x hf,
    Kernel.id_apply,lintegral_dirac' x (f := fun y => ENNReal.ofReal (b y*r y)*f y)
      ((hb.mul hr).ennreal_ofReal.mul hf)]

theorem positiveSourceKernel_one_lintegral (K : Kernel X X) [IsSFiniteKernel K]
    {r : X → ℝ} (hr : Measurable r) (x : X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂positiveSourceKernel K (fun _ => 1) r x) =
      (∫⁻ y, f y ∂K x)+ENNReal.ofReal (r x)*f x := by
  rw [positiveSourceKernel_lintegral K measurable_const hr x hf]
  simp only [ENNReal.ofReal_one,one_mul]

end BoltzmannNonuniqueness

end

end

end OAI
