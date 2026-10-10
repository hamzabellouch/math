import OAI.MathematicalPhysics.Boltzmann.Collision.AngularPairTests
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairRepresentative

namespace OAI

section

/-! # Continuous incoming-velocity tests for the symmetric gain and loss

These use the original normal-sphere parametrization, so no new change of
variables is needed to handle the diagonal where the two velocities coincide.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.CollisionCompactness

def incomingGainTest (φ : Velocity → ℝ) (p : Velocity × Velocity) : ℝ :=
  (1/2 : ℝ) * ∫ ω : Sphere, collisionKernel p.1 p.2 ω *
    (φ (scatterLeft p.1 p.2 ω)+φ (scatterRight p.1 p.2 ω)) ∂sphereArea

def incomingLossTest (φ : Velocity → ℝ) (p : Velocity × Velocity) : ℝ :=
  (2*Real.pi*‖p.1-p.2‖)*φ p.2

theorem incomingGainTest_continuous {φ : Velocity → ℝ} (hφ : Continuous φ) :
    Continuous (incomingGainTest φ) := by
  have hc : Continuous (Function.uncurry (fun (p : Velocity × Velocity) (ω : Sphere) =>
      collisionKernel p.1 p.2 ω *
        (φ (scatterLeft p.1 p.2 ω)+φ (scatterRight p.1 p.2 ω)))) := by
    simp only [collisionKernel,scatterLeft,scatterRight,normalComponent]
    fun_prop
  have hi := continuous_parametric_integral_of_continuous
    (μ := sphereArea) hc (isCompact_univ : IsCompact (univ : Set Sphere))
  unfold incomingGainTest
  simpa only [Measure.restrict_univ] using hi.const_mul (1/2 : ℝ)

theorem incomingLossTest_continuous {φ : Velocity → ℝ} (hφ : Continuous φ) :
    Continuous (incomingLossTest φ) := by
  unfold incomingLossTest
  fun_prop

theorem incomingGainTest_abs_le {φ : Velocity → ℝ}
    {B : ℝ} (hB : ∀ v, |φ v| ≤ B) (p : Velocity × Velocity) :
    |incomingGainTest φ p| ≤ (2*Real.pi*‖p.1-p.2‖)*B := by
  have hb (ω : Sphere) :
      ‖collisionKernel p.1 p.2 ω *
        (φ (scatterLeft p.1 p.2 ω)+φ (scatterRight p.1 p.2 ω))‖ ≤
      collisionKernel p.1 p.2 ω*(2*B) := by
    have hk : 0 ≤ collisionKernel p.1 p.2 ω := abs_nonneg _
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hk]
    apply mul_le_mul_of_nonneg_left _ hk
    apply (abs_add_le _ _).trans
    simpa only [two_mul] using add_le_add (hB (scatterLeft p.1 p.2 ω)) (hB (scatterRight p.1 p.2 ω))
  have hi := norm_integral_le_of_norm_le
    ((integrable_collisionKernel_sphereArea p.1 p.2).mul_const (2*B)) (ae_of_all _ hb)
  rw [integral_mul_const,integral_collisionKernel_sphereArea,Real.norm_eq_abs] at hi
  unfold incomingGainTest
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  calc
    _ ≤ (1/2 : ℝ)*((2*Real.pi*‖p.1-p.2‖)*(2*B)) :=
      mul_le_mul_of_nonneg_left hi (by norm_num)
    _ = _ := by ring

theorem incomingLossTest_abs_le {φ : Velocity → ℝ} {B : ℝ}
    (hB : ∀ v, |φ v| ≤ B) (p : Velocity × Velocity) :
    |incomingLossTest φ p| ≤ (2*Real.pi*‖p.1-p.2‖)*B := by
  unfold incomingLossTest
  rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi*‖p.1-p.2‖)]
  exact mul_le_mul_of_nonneg_left (hB p.2) (by positivity)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Incoming collision measures, including atomic cold partners -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*}

def incomingRate (z : X × (Velocity × Velocity)) : ℝ :=
  2*Real.pi*‖z.2.1-z.2.2‖

theorem incomingRate_nonneg (z : X × (Velocity × Velocity)) : 0 ≤ incomingRate z := by
  unfold incomingRate
  positivity

variable [MeasurableSpace X]

theorem incomingRate_measurable : Measurable (incomingRate (X := X)) := by
  unfold incomingRate
  fun_prop

def incomingCollisionMeasure (μ : Measure (X × (Velocity × Velocity))) :
    Measure ((X × (Velocity × Velocity)) × Sphere) :=
  (μ.prod sphereArea).withDensity
    (fun z => ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2))

theorem incomingCollisionMeasure_mass (μ : Measure (X × (Velocity × Velocity))) [SFinite μ] :
    incomingCollisionMeasure μ univ = ∫⁻ z, ENNReal.ofReal (incomingRate z) ∂μ := by
  rw [incomingCollisionMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)) := by
    unfold collisionKernel normalComponent
    fun_prop
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro z
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_collisionKernel_sphereArea z.2.1 z.2.2)
    (ae_of_all _ (fun ω : Sphere => show 0 ≤ collisionKernel z.2.1 z.2.2 ω from abs_nonneg _)),
    integral_collisionKernel_sphereArea]
  rfl

theorem incomingCollisionMeasure_finite {μ : Measure (X × (Velocity × Velocity))} [SFinite μ]
    (hi : Integrable incomingRate μ) : IsFiniteMeasure (incomingCollisionMeasure μ) := by
  constructor
  rw [incomingCollisionMeasure_mass,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ incomingRate_nonneg)]
  exact ENNReal.ofReal_lt_top

def incomingLeft (z : (X × (Velocity × Velocity)) × Sphere) : X × Velocity :=
  (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)

def incomingRight (z : (X × (Velocity × Velocity)) × Sphere) : X × Velocity :=
  (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)

theorem incomingLeft_measurable : Measurable (incomingLeft (X := X)) := by
  unfold incomingLeft scatterLeft normalComponent
  fun_prop

theorem incomingRight_measurable : Measurable (incomingRight (X := X)) := by
  unfold incomingRight scatterRight normalComponent
  fun_prop

def incomingGainMeasure (μ : Measure (X × (Velocity × Velocity))) : Measure (X × Velocity) :=
  (1/2 : ℝ≥0∞) • ((incomingCollisionMeasure μ).map incomingLeft+
    (incomingCollisionMeasure μ).map incomingRight)

def incomingLossMeasure (μ : Measure (X × (Velocity × Velocity))) : Measure (X × Velocity) :=
  (incomingCollisionMeasure μ).map (fun z => (z.1.1,z.1.2.2))

theorem incomingGainMeasure_mass (μ : Measure (X × (Velocity × Velocity))) :
    incomingGainMeasure μ univ = incomingCollisionMeasure μ univ := by
  rw [incomingGainMeasure,Measure.smul_apply,Measure.add_apply,
    Measure.map_apply incomingLeft_measurable MeasurableSet.univ,
    Measure.map_apply incomingRight_measurable MeasurableSet.univ]
  simp only [preimage_univ,smul_eq_mul]
  rw [← two_mul,← mul_assoc]
  rw [one_div,ENNReal.inv_mul_cancel (by norm_num : (2:ℝ≥0∞) ≠ 0) (by simp),one_mul]

theorem incomingLossMeasure_mass (μ : Measure (X × (Velocity × Velocity))) :
    incomingLossMeasure μ univ = incomingCollisionMeasure μ univ := by
  rw [incomingLossMeasure,Measure.map_apply (by fun_prop) MeasurableSet.univ,preimage_univ]

theorem incomingGainMeasure_finite {μ : Measure (X × (Velocity × Velocity))} [SFinite μ]
    (hi : Integrable incomingRate μ) : IsFiniteMeasure (incomingGainMeasure μ) := by
  let _ := incomingCollisionMeasure_finite hi
  exact ⟨by rw [incomingGainMeasure_mass]; exact measure_lt_top _ _⟩

theorem incomingLossMeasure_finite {μ : Measure (X × (Velocity × Velocity))} [SFinite μ]
    (hi : Integrable incomingRate μ) : IsFiniteMeasure (incomingLossMeasure μ) := by
  let _ := incomingCollisionMeasure_finite hi
  exact ⟨by rw [incomingLossMeasure_mass]; exact measure_lt_top _ _⟩

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Testing the actual incoming gain and loss measures -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem incomingCollisionMeasure_integral (μ : Measure (X × (Velocity × Velocity)))
    (f : (X × (Velocity × Velocity)) × Sphere → ℝ) :
    (∫ z, f z ∂incomingCollisionMeasure μ) =
      ∫ z, collisionKernel z.1.2.1 z.1.2.2 z.2*f z ∂μ.prod sphereArea := by
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)) := by
    unfold collisionKernel normalComponent
    fun_prop
  rw [incomingCollisionMeasure,integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    dsimp only
    rw [ENNReal.toReal_ofReal (show 0 ≤ collisionKernel z.1.2.1 z.1.2.2 z.2 from abs_nonneg _),
      smul_eq_mul])

theorem incomingGainMeasure_integral {μ : Measure (X × (Velocity × Velocity))} [SFinite μ]
    (hi : Integrable incomingRate μ) {f : X × Velocity → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ z, |f z| ≤ B) :
    (∫ z, f z ∂incomingGainMeasure μ) =
      (1/2:ℝ)*((∫ z, f (incomingLeft z) ∂incomingCollisionMeasure μ)+
        (∫ z, f (incomingRight z) ∂incomingCollisionMeasure μ)) := by
  let _ := incomingCollisionMeasure_finite hi
  have hleft : Integrable f ((incomingCollisionMeasure μ).map incomingLeft) :=
    (integrable_const B).mono' hf.aestronglyMeasurable (ae_of_all _ hB)
  have hright : Integrable f ((incomingCollisionMeasure μ).map incomingRight) :=
    (integrable_const B).mono' hf.aestronglyMeasurable (ae_of_all _ hB)
  rw [incomingGainMeasure,integral_smul_measure,integral_add_measure hleft hright,
    integral_map incomingLeft_measurable.aemeasurable hf.aestronglyMeasurable,
    integral_map incomingRight_measurable.aemeasurable hf.aestronglyMeasurable]
  norm_num

theorem incomingLossMeasure_integral {μ : Measure (X × (Velocity × Velocity))}
    {f : X × Velocity → ℝ} (hf : Measurable f) :
    (∫ z, f z ∂incomingLossMeasure μ) =
      ∫ z, f (z.1.1,z.1.2.2) ∂incomingCollisionMeasure μ := by
  rw [incomingLossMeasure,integral_map (by fun_prop) hf.aestronglyMeasurable]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Fubini formulas for incoming collision measures with atomic partners -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem incomingCollisionMeasure_integral_prod
    {μ : Measure (X × (Velocity × Velocity))} [SFinite μ]
    (hi : Integrable incomingRate μ)
    {f : (X × (Velocity × Velocity)) × Sphere → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ z, |f z| ≤ B) :
    (∫ z, f z ∂incomingCollisionMeasure μ) =
      ∫ p, ∫ ω, collisionKernel p.2.1 p.2.2 ω*f (p,ω) ∂sphereArea ∂μ := by
  let _ := incomingCollisionMeasure_finite hi
  have hif : Integrable f (incomingCollisionMeasure μ) :=
    (integrable_const B).mono' hf.aestronglyMeasurable (ae_of_all _ hB)
  have hd : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)) := by
    unfold collisionKernel normalComponent
    fun_prop
  have hw := (integrable_withDensity_iff_integrable_smul' hd
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hif
  have hweight : Integrable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      collisionKernel z.1.2.1 z.1.2.2 z.2*f z) (μ.prod sphereArea) := by
    convert hw using 1
    funext z
    rw [ENNReal.toReal_ofReal (show 0 ≤ collisionKernel z.1.2.1 z.1.2.2 z.2 from abs_nonneg _),
      smul_eq_mul]
  rw [incomingCollisionMeasure_integral]
  exact integral_prod _ hweight

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Integrable normal-collision test densities for a finite incoming rate -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem incomingCollision_weight_integrable
    {μ : Measure (X × (Velocity × Velocity))} [SFinite μ]
    (hi : Integrable incomingRate μ)
    {f : (X × (Velocity × Velocity)) × Sphere → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ z, |f z| ≤ B) :
    Integrable (fun z => collisionKernel z.1.2.1 z.1.2.2 z.2*f z) (μ.prod sphereArea) := by
  let _ := incomingCollisionMeasure_finite hi
  have hif : Integrable f (incomingCollisionMeasure μ) :=
    (integrable_const B).mono' hf.aestronglyMeasurable (ae_of_all _ hB)
  have hd : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)) := by
    unfold collisionKernel normalComponent
    fun_prop
  have hw := (integrable_withDensity_iff_integrable_smul' hd
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hif
  convert hw using 1
  funext z
  rw [ENNReal.toReal_ofReal (show 0 ≤ collisionKernel z.1.2.1 z.1.2.2 z.2 from abs_nonneg _),
    smul_eq_mul]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Linear growth of the continuous incoming gain and loss tests -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

theorem incomingTests_linear_growth {φ : Velocity → ℝ} {B : ℝ}
    (hB : ∀ v, |φ v| ≤ B) (p : Velocity × Velocity) :
    |incomingGainTest φ p| ≤ (2*Real.pi*B)*(1+‖p.1‖+‖p.2‖) ∧
    |incomingLossTest φ p| ≤ (2*Real.pi*B)*(1+‖p.1‖+‖p.2‖) := by
  have hB0 : 0 ≤ B := (abs_nonneg (φ 0)).trans (hB 0)
  have hrate : (2*Real.pi*‖p.1-p.2‖)*B ≤ (2*Real.pi*B)*(1+‖p.1‖+‖p.2‖) := by
    have hn : ‖p.1-p.2‖ ≤ 1+‖p.1‖+‖p.2‖ := (norm_sub_le _ _).trans (by linarith)
    calc
      _ = (2*Real.pi*B)*‖p.1-p.2‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hn
        (mul_nonneg (by positivity : 0 ≤ 2*Real.pi) hB0)
  exact ⟨(incomingGainTest_abs_le hB p).trans hrate,(incomingLossTest_abs_le hB p).trans hrate⟩

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The incoming measures agree with the separated collision tests -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem incomingGainMeasure_separated
    {μ : Measure (X × (Velocity × Velocity))} [SFinite μ] (hi : Integrable incomingRate μ)
    {θ : X → ℝ} (hθ : Measurable θ) {B : ℝ} (hB : 0 ≤ B) (hθB : ∀ x, |θ x| ≤ B)
    {φ : Velocity → ℝ} (hφ : Measurable φ) {C : ℝ} (hφC : ∀ v, |φ v| ≤ C) :
    (∫ z, θ z.1*φ z.2 ∂incomingGainMeasure μ) =
      ∫ z, θ z.1*incomingGainTest φ z.2 ∂μ := by
  let ψ : X × Velocity → ℝ := fun z => θ z.1*φ z.2
  have hψ : Measurable ψ := (hθ.comp measurable_fst).mul (hφ.comp measurable_snd)
  have hψB (z) : |ψ z| ≤ B*C := by
    dsimp only [ψ]
    rw [abs_mul]
    exact mul_le_mul (hθB _) (hφC _) (abs_nonneg _) hB
  let F : (X × (Velocity × Velocity)) × Sphere → ℝ :=
    fun z => (1/2:ℝ)*(ψ (incomingLeft z)+ψ (incomingRight z))
  have hFm : Measurable F := measurable_const.mul
    ((hψ.comp incomingLeft_measurable).add (hψ.comp incomingRight_measurable))
  have hFb (z) : |F z| ≤ B*C := by
    dsimp [F]
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    have hh := (abs_add_le (ψ (incomingLeft z)) (ψ (incomingRight z))).trans
      (add_le_add (hψB _) (hψB _))
    linarith
  let _ := incomingCollisionMeasure_finite hi
  have hL : Integrable (fun z => ψ (incomingLeft z)) (incomingCollisionMeasure μ) :=
    (integrable_const (B*C)).mono' (hψ.comp incomingLeft_measurable).aestronglyMeasurable
      (ae_of_all _ (fun z => hψB _))
  have hR : Integrable (fun z => ψ (incomingRight z)) (incomingCollisionMeasure μ) :=
    (integrable_const (B*C)).mono' (hψ.comp incomingRight_measurable).aestronglyMeasurable
      (ae_of_all _ (fun z => hψB _))
  change (∫ z, ψ z ∂incomingGainMeasure μ) = _
  rw [incomingGainMeasure_integral hi hψ hψB,← integral_add hL hR,← integral_const_mul]
  change (∫ z, F z ∂incomingCollisionMeasure μ) = _
  rw [incomingCollisionMeasure_integral_prod hi hFm hFb]
  apply integral_congr_ae
  filter_upwards [] with z
  unfold incomingGainTest
  dsimp only [F,ψ,incomingLeft,incomingRight]
  calc
    _ = (θ z.1*(1/2:ℝ))*∫ ω : Sphere, collisionKernel z.2.1 z.2.2 ω*
        (φ (scatterLeft z.2.1 z.2.2 ω)+φ (scatterRight z.2.1 z.2.2 ω)) ∂sphereArea := by
      rw [← integral_const_mul]
      congr 1
      funext ω
      ring
    _ = _ := by ring

theorem incomingLossMeasure_separated
    {μ : Measure (X × (Velocity × Velocity))} [SFinite μ] (hi : Integrable incomingRate μ)
    {θ : X → ℝ} (hθ : Measurable θ) {B : ℝ} (hB : 0 ≤ B) (hθB : ∀ x, |θ x| ≤ B)
    {φ : Velocity → ℝ} (hφ : Measurable φ) {C : ℝ} (hφC : ∀ v, |φ v| ≤ C) :
    (∫ z, θ z.1*φ z.2 ∂incomingLossMeasure μ) =
      ∫ z, θ z.1*incomingLossTest φ z.2 ∂μ := by
  have hψ : Measurable (fun z : X × Velocity => θ z.1*φ z.2) :=
    (hθ.comp measurable_fst).mul (hφ.comp measurable_snd)
  rw [incomingLossMeasure_integral hψ]
  have hFm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere => θ z.1.1*φ z.1.2.2) :=
    (hθ.comp measurable_fst.fst).mul (hφ.comp measurable_fst.snd.snd)
  have hFb (z : (X × (Velocity × Velocity)) × Sphere) : |θ z.1.1*φ z.1.2.2| ≤ B*C := by
    rw [abs_mul]
    exact mul_le_mul (hθB _) (hφC _) (abs_nonneg _) hB
  rw [incomingCollisionMeasure_integral_prod hi hFm hFb]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [integral_mul_const,integral_collisionKernel_sphereArea]
  unfold incomingLossTest
  ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Finite incoming collision rates from the proved Gaussian pair moment -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem incomingRate_integrable_of_gaussian {μ : Measure (X × (Velocity × Velocity))}
    (hm : (∫⁻ z, ENNReal.ofReal (weight z.2.1*weight z.2.2) ∂μ) < ∞) :
    Integrable incomingRate μ := by
  have hn : ∀ᵐ z ∂μ, 0 ≤ weight z.2.1*weight z.2.2 :=
    ae_of_all _ (fun z => mul_nonneg (weight_pos z.2.1).le (weight_pos z.2.2).le)
  have hw : Integrable (fun z : X × (Velocity × Velocity) => weight z.2.1*weight z.2.2) μ := by
    refine ⟨by unfold weight; fun_prop,?_⟩
    exact (hasFiniteIntegral_iff_ofReal hn).mpr hm
  apply (hw.const_mul (6*Real.pi)).mono' incomingRate_measurable.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (incomingRate_nonneg z)]
  have hv := norm_sub_le z.2.1 z.2.2
  have hp := pair_weight_le z.2.1 z.2.2
  have hh : ‖z.2.1-z.2.2‖ ≤ 3*(weight z.2.1*weight z.2.2) := by linarith
  have he := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*Real.pi by positivity)
  dsimp only [incomingRate]
  nlinarith

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The incoming loss measure is the incoming rate at the retained velocity -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem incomingLossMeasure_rate_integral
    {μ : Measure (X × (Velocity × Velocity))} [SFinite μ]
    (hi : Integrable incomingRate μ) {ψ : X × Velocity → ℝ}
    (hψ : Measurable ψ) {B : ℝ} (hB : ∀ z, |ψ z| ≤ B) :
    (∫ z, ψ z ∂incomingLossMeasure μ) =
      ∫ z, incomingRate z*ψ (z.1,z.2.2) ∂μ := by
  rw [incomingLossMeasure_integral hψ]
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ψ (z.1.1,z.1.2.2)) := hψ.comp (measurable_fst.fst.prodMk measurable_fst.snd.snd)
  rw [incomingCollisionMeasure_integral_prod hi hm (fun z => hB _)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [integral_mul_const,integral_collisionKernel_sphereArea]
  rfl

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
