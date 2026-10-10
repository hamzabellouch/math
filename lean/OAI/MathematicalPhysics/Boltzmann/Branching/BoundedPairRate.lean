import OAI.MathematicalPhysics.Boltzmann.Collision.AngularGainTranslationTests
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocitySmoothingError

namespace OAI

section

/-! # Uniform L1 velocity translations of gains from bounded compact incoming densities -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem pairIntegral_localize {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (R : ℝ) (g φ : X × (Velocity × Velocity) → ℝ)
    (hg : ∀ z, z.2 ∉ incomingBall R → g z = 0) :
    (∫ z, g z*φ z ∂μ.prod (volume : Measure (Velocity × Velocity))) =
      ∫ z, g z*φ z ∂μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)) := by
  have he : μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)) =
      (μ.prod (volume : Measure (Velocity × Velocity))).restrict (univ ×ˢ incomingBall R) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := μ) (ν := (volume : Measure (Velocity × Velocity))) univ (incomingBall R))
  rw [he]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hz' : z.2 ∉ incomingBall R := by simpa only [mem_prod,mem_univ,true_and] using hz
  rw [hg z hz',zero_mul]

theorem bounded_pairGain_translation {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (R : ℝ)
    {a : ℕ → Velocity} (ha : Tendsto a atTop (𝓝 0))
    {g : ℕ → X × (Velocity × Velocity) → ℝ} (hg : ∀ n, Measurable (g n))
    {B : ℝ} (hB : ∀ n z, |g n z| ≤ B)
    (hs : ∀ n z, z.2 ∉ incomingBall R → g n z = 0)
    (hi : ∀ n, Integrable (pairPreRate (g n))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Tendsto (fun n => ∫ p, |pairGain (g n) (p.1,p.2+a n)-pairGain (g n) p| ∂μ.prod volume)
      atTop (𝓝 0) := by
  let D : ℕ → X × Velocity → ℝ := fun n p => pairGain (g n) (p.1,p.2+a n)-pairGain (g n) p
  let ψ : ℕ → X × Velocity → ℝ := fun n p => if 0 ≤ D n p then 1 else -1
  have hD n : Measurable (D n) :=
    ((pairGain_measurable (hg n)).comp
      (measurable_fst.prodMk (measurable_snd.add_const (a n)))).sub (pairGain_measurable (hg n))
  have hψ n : Measurable (ψ n) :=
    Measurable.ite (measurableSet_le measurable_const (hD n)) measurable_const measurable_const
  have hψB n p : |ψ n p| ≤ 1 := by dsimp only [ψ]; split <;> norm_num
  have hsign n p : ψ n p*D n p = |D n p| := by
    dsimp only [ψ]
    split_ifs with h
    · rw [one_mul,abs_of_nonneg h]
    · rw [neg_one_mul,abs_of_neg (lt_of_not_ge h)]
  have han : Tendsto (fun n => -a n) atTop (𝓝 0) := by simpa only [neg_zero] using ha.neg
  have ht := bounded_gain_translation_tests (μ := μ) R han hψ (by norm_num : (0:ℝ) ≤ 1) hψB hg hB
  have he n : (∫ p, |D n p| ∂μ.prod volume) =
      ∫ z, g n z*angularFamily (fun q => ψ n (q.1,q.2 + -a n)-ψ n q) z
        ∂μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R)) := by
    have hφ : Measurable (fun q => ψ n (q.1,q.2-a n)-ψ n q) :=
      ((hψ n).comp (measurable_fst.prodMk (measurable_snd.sub_const (a n)))).sub (hψ n)
    have hφB q : |ψ n (q.1,q.2-a n)-ψ n q| ≤ 2 :=
      (abs_sub _ _).trans (by linarith [hψB n (q.1,q.2-a n),hψB n q])
    calc
      _ = ∫ p, ψ n p*(pairGain (g n) (p.1,p.2+a n)-pairGain (g n) p) ∂μ.prod volume := by
        apply integral_congr_ae
        exact ae_of_all _ (fun p => (hsign n p).symm)
      _ = ∫ p, (ψ n (p.1,p.2-a n)-ψ n p)*pairGain (g n) p ∂μ.prod volume :=
        velocityShift_difference_test (pairGain_integrable (hi n)) (hψ n) (hψB n) (a n)
      _ = ∫ z, g n z*angularFamily (fun q => ψ n (q.1,q.2-a n)-ψ n q) z
          ∂μ.prod (volume : Measure (Velocity × Velocity)) := pairGain_test (hi n) hφ hφB
      _ = _ := by
        rw [pairIntegral_localize μ R (g n) _ (hs n)]
        simp only [sub_eq_add_neg]
  exact ht.congr' (Eventually.of_forall (fun n => (he n).symm))

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Integrability of the physical rate for bounded compact incoming pair densities -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

theorem bounded_pairPreRate_integrable {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (R : ℝ)
    {g : X × (Velocity × Velocity) → ℝ} (hg : Measurable g)
    {B : ℝ} (hB : ∀ z, |g z| ≤ B)
    (hs : ∀ z, z.2 ∉ incomingBall R → g z = 0) :
    Integrable (pairPreRate g) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  let S : Set ((X × (Velocity × Velocity)) × Sphere) := (univ ×ˢ incomingBall R) ×ˢ univ
  have he : (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict S) =
      (μ.prod ((volume : Measure (Velocity × Velocity)).restrict (incomingBall R))).prod sphereArea := by
    dsimp only [S]
    rw [← Measure.prod_restrict,Measure.restrict_univ,← Measure.prod_restrict,Measure.restrict_univ]
  have hi : IntegrableOn (pairPreRate g) S
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    rw [IntegrableOn,he]
    apply (integrable_const (2*|R| * |B|)).mono' (pairPreRate_measurable hg).aestronglyMeasurable
    have hp : ∀ᵐ p : Velocity × Velocity ∂volume.restrict (incomingBall R), p ∈ incomingBall R :=
      ae_restrict_mem ((isCompact_closedBall (0 : Velocity) R).prod
        (isCompact_closedBall (0 : Velocity) R)).measurableSet
    have hq : ∀ᵐ z : X × (Velocity × Velocity)
        ∂μ.prod (volume.restrict (incomingBall R)), z.2 ∈ incomingBall R :=
      Measure.quasiMeasurePreserving_snd.ae hp
    have hz : ∀ᵐ z : (X × (Velocity × Velocity)) × Sphere
        ∂(μ.prod (volume.restrict (incomingBall R))).prod sphereArea, z.1.2 ∈ incomingBall R :=
      Measure.quasiMeasurePreserving_fst.ae hq
    filter_upwards [hz] with z hz
    have hv : ‖z.1.2.1‖ ≤ |R| := (by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1 : ‖z.1.2.1‖ ≤ R).trans (le_abs_self R)
    have hw : ‖z.1.2.2‖ ≤ |R| := (by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2 : ‖z.1.2.2‖ ≤ R).trans (le_abs_self R)
    have hk : collisionKernel z.1.2.1 z.1.2.2 z.2 ≤ 2*|R| :=
      (collisionKernel_le_norm _ _ _).trans ((norm_sub_le _ _).trans (by linarith))
    change ‖collisionKernel z.1.2.1 z.1.2.2 z.2*g z.1‖ ≤ _
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (collisionKernel_nonneg _ _ _)]
    exact mul_le_mul hk ((hB z.1).trans (le_abs_self B)) (abs_nonneg _) (by positivity)
  apply hi.integrable_of_forall_notMem_eq_zero
  intro z hz
  have hp : z.1.2 ∉ incomingBall R := by
    simpa only [S,mem_prod,mem_univ,true_and,and_true] using hz
  change collisionKernel _ _ _*g z.1 = 0
  rw [hs z.1 hp,mul_zero]

theorem bounded_pairGain_translation_no_rate_assumption {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (R : ℝ)
    {a : ℕ → Velocity} (ha : Tendsto a atTop (𝓝 0))
    {g : ℕ → X × (Velocity × Velocity) → ℝ} (hg : ∀ n, Measurable (g n))
    {B : ℝ} (hB : ∀ n z, |g n z| ≤ B)
    (hs : ∀ n z, z.2 ∉ incomingBall R → g n z = 0) :
    Tendsto (fun n => ∫ p, |pairGain (g n) (p.1,p.2+a n)-pairGain (g n) p| ∂μ.prod volume)
      atTop (𝓝 0) :=
  bounded_pairGain_translation R ha hg hB hs
    (fun n => bounded_pairPreRate_integrable R (hg n) (hB n) (hs n))

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
