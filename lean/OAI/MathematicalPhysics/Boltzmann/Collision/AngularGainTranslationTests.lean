import OAI.MathematicalPhysics.Boltzmann.Branching.DoubleCollisionTests
import OAI.MathematicalPhysics.Boltzmann.Branching.SquareIntegralToL1
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairTranslatedProduct
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

section

/-! # Compact incoming-velocity bounds for bounded angular tests -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

instance incomingBallFinite (R : ℝ) :
    IsFiniteMeasure ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)) :=
  isFiniteMeasure_restrict.mpr ((isCompact_closedBall (0 : Velocity) R).prod
    (isCompact_closedBall (0 : Velocity) R)).measure_lt_top.ne

theorem angularAdjoint_abs_le {ψ : Velocity → ℝ} {C : ℝ}
    (hC : ∀ v, |ψ v| ≤ C) (p : Velocity × Velocity) :
    |angularAdjoint ψ p| ≤ (2*Real.pi*‖p.1-p.2‖)*C := by
  have hi := norm_integral_le_of_norm_le
    ((integrable_collisionKernel_sphereArea p.1 p.2).mul_const C)
    (ae_of_all _ (fun n : Sphere => show
      ‖collisionKernel p.1 p.2 n*ψ (scatterLeft p.1 p.2 n)‖ ≤
        collisionKernel p.1 p.2 n*C by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (collisionKernel_nonneg _ _ _)]
      exact mul_le_mul_of_nonneg_left (hC _) (collisionKernel_nonneg _ _ _)))
  simpa only [angularAdjoint,Real.norm_eq_abs,integral_mul_const,
    integral_collisionKernel_sphereArea] using hi

theorem angularAdjoint_bounded_on (R : ℝ) {ψ : Velocity → ℝ} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ v, |ψ v| ≤ C) {p : Velocity × Velocity}
    (hp : p ∈ incomingBall R) : |angularAdjoint ψ p| ≤ 4*Real.pi*|R| *C := by
  have hv : ‖p.1‖ ≤ |R| := (by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1 : ‖p.1‖ ≤ R).trans (le_abs_self R)
  have hw : ‖p.2‖ ≤ |R| := (by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hp.2 : ‖p.2‖ ≤ R).trans (le_abs_self R)
  apply (angularAdjoint_abs_le hC p).trans
  have hn : ‖p.1-p.2‖ ≤ 2*|R| := (norm_sub_le _ _).trans (by linarith)
  nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_right hn (mul_nonneg Real.pi_pos.le hC0)]

theorem angularAdjoint_integrableOn (R : ℝ) {ψ : Velocity → ℝ}
    (hψ : Measurable ψ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |ψ v| ≤ C) :
    IntegrableOn (angularAdjoint ψ) (incomingBall R) := by
  apply (integrable_const (4*Real.pi*|R| *C)).mono'
    (angularAdjoint_measurable hψ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem ((isCompact_closedBall (0 : Velocity) R).prod
    (isCompact_closedBall (0 : Velocity) R)).measurableSet] with p hp
  exact angularAdjoint_bounded_on R hC0 hC hp

theorem angularAdjoint_square_integrableOn (R : ℝ) {ψ : Velocity → ℝ}
    (hψ : Measurable ψ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |ψ v| ≤ C) :
    IntegrableOn (fun p => (angularAdjoint ψ p)^2) (incomingBall R) := by
  apply (integrable_const ((4*Real.pi*|R| *C)^2)).mono'
    ((angularAdjoint_measurable hψ).pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem ((isCompact_closedBall (0 : Velocity) R).prod
    (isCompact_closedBall (0 : Velocity) R)).measurableSet] with p hp
  rw [Real.norm_of_nonneg (sq_nonneg _),← sq_abs (angularAdjoint ψ p)]
  exact pow_le_pow_left₀ (abs_nonneg _) (angularAdjoint_bounded_on R hC0 hC hp) 2

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Uniform translation control for the physical angular adjoint -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem angularAdjoint_translation_square (R : ℝ) {a : ℕ → Velocity}
    (ha : Tendsto a atTop (𝓝 0)) {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ n, Measurable (ψ n)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n v, |ψ n v| ≤ C) :
    Tendsto (fun n => ∫ p in incomingBall R,
      (angularAdjoint (fun v => ψ n (v+a n)-ψ n v) p)^2) atTop (𝓝 0) := by
  have ht := translated_pair_product_zero (referenceDensity_measurable R)
    (referenceDensity_integrable R) ha hψ hC hbound
  have he n : (∫ p in incomingBall R,
      (angularAdjoint (fun v => ψ n (v+a n)-ψ n v) p)^2) =
      ∫ p, referenceDensity R p*
        ((ψ n (p.1+a n)-ψ n p.1)*(ψ n (p.2+a n)-ψ n p.2)) := by
    apply angularAdjoint_square R
    · exact ((hψ n).comp (measurable_id.add_const (a n))).sub (hψ n)
    · exact mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC
    · intro v
      exact (abs_sub _ _).trans (by linarith [hbound n (v+a n),hbound n v])
  exact ht.congr' (Filter.Eventually.of_forall (fun n => (he n).symm))

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # L1 translation control for bounded measurable angular tests -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem angularAdjoint_translation_L1 (R : ℝ) {a : ℕ → Velocity}
    (ha : Tendsto a atTop (𝓝 0)) {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ n, Measurable (ψ n)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n v, |ψ n v| ≤ C) :
    Tendsto (fun n => ∫ p in incomingBall R,
      |angularAdjoint (fun v => ψ n (v+a n)-ψ n v) p|) atTop (𝓝 0) := by
  have hm n : Measurable (fun v => ψ n (v+a n)-ψ n v) :=
    ((hψ n).comp (measurable_id.add_const (a n))).sub (hψ n)
  have hb n v : |ψ n (v+a n)-ψ n v| ≤ 2*C :=
    (abs_sub _ _).trans (by linarith [hbound n (v+a n),hbound n v])
  have h2C : 0 ≤ 2*C := mul_nonneg (by norm_num) hC
  exact integral_abs_tendsto_zero_of_square
    (fun n => angularAdjoint_integrableOn R (hm n) h2C (hb n))
    (fun n => angularAdjoint_square_integrableOn R (hm n) h2C (hb n))
    (angularAdjoint_translation_square R ha hψ hC hbound)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Angular translation control with a measurable spacetime parameter -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X]

def angularFamily (ψ : X × Velocity → ℝ) (z : X × (Velocity × Velocity)) : ℝ :=
  angularAdjoint (fun v => ψ (z.1,v)) z.2

theorem angularFamily_measurable {ψ : X × Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (angularFamily ψ) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  change Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
    collisionKernel z.1.2.1 z.1.2.2 z.2*ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
  apply Measurable.mul
  · unfold collisionKernel normalComponent
    fun_prop
  · apply hψ.comp
    apply Measurable.prodMk
    · fun_prop
    · unfold scatterLeft normalComponent
      fun_prop

theorem angularFamily_integrable (R : ℝ) {μ : Measure X} [IsFiniteMeasure μ]
    {ψ : X × Velocity → ℝ} (hψ : Measurable ψ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ z, |ψ z| ≤ C) :
    Integrable (angularFamily ψ)
      (μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R))) := by
  apply (integrable_const (4*Real.pi*|R| *C)).mono'
    (angularFamily_measurable hψ).aestronglyMeasurable
  have hp : ∀ᵐ p : Velocity × Velocity ∂volume.restrict (incomingBall R), p ∈ incomingBall R :=
    ae_restrict_mem ((isCompact_closedBall (0 : Velocity) R).prod
      (isCompact_closedBall (0 : Velocity) R)).measurableSet
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hp] with z hz
  exact angularAdjoint_bounded_on R hC0 (fun v => hC (z.1,v)) hz

theorem angularFamily_translation_L1 (R : ℝ) {μ : Measure X} [IsFiniteMeasure μ]
    {a : ℕ → Velocity} (ha : Tendsto a atTop (𝓝 0))
    {ψ : ℕ → X × Velocity → ℝ} (hψ : ∀ n, Measurable (ψ n))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ n z, |ψ n z| ≤ C) :
    Tendsto (fun n => ∫ z,
      |angularFamily (fun q => ψ n (q.1,q.2+a n)-ψ n q) z|
        ∂μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)))
      atTop (𝓝 0) := by
  let d : ℕ → X × Velocity → ℝ := fun n q => ψ n (q.1,q.2+a n)-ψ n q
  have hm n : Measurable (d n) :=
    ((hψ n).comp (measurable_fst.prodMk (measurable_snd.add_const (a n)))).sub (hψ n)
  have hb n q : |d n q| ≤ 2*C :=
    (abs_sub _ _).trans (by linarith [hC n (q.1,q.2+a n),hC n q])
  have h2C : 0 ≤ 2*C := mul_nonneg (by norm_num) hC0
  have hi n := (angularFamily_integrable R (μ := μ) (hm n) h2C (hb n)).abs
  let B := (volume : Measure (Velocity × Velocity)).real (incomingBall R)*(4*Real.pi*|R| *(2*C))
  have hl x : Tendsto (fun n => ∫ p in incomingBall R, |angularFamily (d n) (x,p)|)
      atTop (𝓝 0) := by
    exact angularAdjoint_translation_L1 R ha
      (fun n => (hψ n).comp (measurable_const.prodMk measurable_id)) hC0
      (fun n v => hC n (x,v))
  have ht := tendsto_integral_of_dominated_convergence
    (μ := μ) (F := fun n x => ∫ p in incomingBall R, |angularFamily (d n) (x,p)|)
    (f := fun _ => (0:ℝ)) (fun _ => B)
    (fun n => (hi n).integral_prod_left.aestronglyMeasurable) (integrable_const B)
    (fun n => ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun p => abs_nonneg _))]
      have hix := (angularAdjoint_integrableOn R
        ((hm n).comp (measurable_const.prodMk measurable_id)) h2C (fun v => hb n (x,v))).abs
      calc
        _ ≤ ∫ _p : Velocity × Velocity in incomingBall R, 4*Real.pi*|R| *(2*C) := by
          apply integral_mono_ae hix (integrable_const _)
          filter_upwards [ae_restrict_mem ((isCompact_closedBall (0 : Velocity) R).prod
            (isCompact_closedBall (0 : Velocity) R)).measurableSet] with p hp
          exact angularAdjoint_bounded_on R h2C (fun v => hb n (x,v)) hp
        _ = B := by
          rw [integral_const,smul_eq_mul]
          simp only [Measure.real,Measure.restrict_apply_univ,B]))
    (ae_of_all _ hl)
  simp only [integral_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun n => (integral_prod _ (hi n)).symm)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Bounded incoming densities against arbitrary translated outgoing tests -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem bounded_gain_translation_tests {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (R : ℝ)
    {a : ℕ → Velocity} (ha : Tendsto a atTop (𝓝 0))
    {ψ : ℕ → X × Velocity → ℝ} (hψ : ∀ n, Measurable (ψ n))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ n z, |ψ n z| ≤ C)
    {g : ℕ → X × (Velocity × Velocity) → ℝ} (hg : ∀ n, Measurable (g n))
    {B : ℝ} (hB : ∀ n z, |g n z| ≤ B) :
    Tendsto (fun n => ∫ z, g n z*
      angularFamily (fun q => ψ n (q.1,q.2+a n)-ψ n q) z
      ∂μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)))
      atTop (𝓝 0) := by
  let d : ℕ → X × Velocity → ℝ := fun n q => ψ n (q.1,q.2+a n)-ψ n q
  have hm n : Measurable (d n) :=
    ((hψ n).comp (measurable_fst.prodMk (measurable_snd.add_const (a n)))).sub (hψ n)
  have hb n q : |d n q| ≤ 2*C :=
    (abs_sub _ _).trans (by linarith [hC n (q.1,q.2+a n),hC n q])
  have h2C : 0 ≤ 2*C := mul_nonneg (by norm_num) hC0
  have hi n := angularFamily_integrable R (μ := μ) (hm n) h2C (hb n)
  have hprod n : Integrable (fun z => g n z*angularFamily (d n) z)
      (μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R))) :=
    (hi n).bdd_mul (hg n).aestronglyMeasurable (ae_of_all _ (hB n))
  have ht := angularFamily_translation_L1 R (μ := μ) ha hψ hC0 hC
  apply squeeze_zero_norm' _ (by simpa only [mul_zero] using ht.const_mul B)
  apply Eventually.of_forall
  intro n
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∫ z, ‖g n z*angularFamily (d n) z‖
        ∂μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, B*|angularFamily (d n) z|
        ∂μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)) := by
      apply integral_mono_ae (hprod n).norm ((hi n).abs.const_mul B)
      filter_upwards [] with z
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_right (hB n z) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
