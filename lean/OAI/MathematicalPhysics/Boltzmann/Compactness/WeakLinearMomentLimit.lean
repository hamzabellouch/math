import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedL1Tests
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityCutoffEntropyError
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

section

/-! # Weak L¹ compactness for the countably generated kinetic measure spaces

Uniform integrability and tightness give uniformly accurate, bounded finite-window
truncations. A common weak L² subsequence has truncation limits that are Cauchy
in L¹. Bounded measurable tests then pass to their strong L¹ limit.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
    (μ : Measure X) [SFinite μ]

theorem l1WeakCompactnessInput : L1WeakCompactnessInput μ := by
  intro f hf hui ht
  obtain ⟨F⟩ := exists_L1TruncationFamily f hf hui ht
  obtain ⟨L⟩ := F.exists_limit
  obtain ⟨g,hg⟩ := L.exists_L1_limit
  refine ⟨L.indices,g,L.increasing,L1.measurable_coeFn _,L1.integrable_coeFn _,?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  let D : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  have hD : ∀ x, ‖ψ x‖ ≤ (D : ℝ) := fun x =>
    (hC x).trans (le_max_left _ _)
  have hfi n : Integrable (f n) μ := memLp_one_iff_integrable.mp (hui.memLp n)
  apply scalar_tendsto_of_uniform_approximations
    (fun n => ∫ x, ψ x*f (L.indices n) x ∂μ)
    (fun m n => ∫ x, ψ x*F.value m (L.indices n) x ∂μ)
    (fun m => ∫ x, ψ x*L.value m x ∂μ)
    (∫ x, ψ x*g x ∂μ) (fun m => (D : ℝ)*truncationError m)
  · simpa using truncationError_tendsto.const_mul (D : ℝ)
  · intro m n
    have he := abs_bounded_test_difference (f (L.indices n)) (F.value m (L.indices n))
      (hfi _) (F.integrable _ _) ψ hψ D hD
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ D.coe_nonneg
    exact integral_abs_le_of_eLpNorm_le ((hfi _).sub (F.integrable _ _))
      (truncationError_pos m).le (F.error m (L.indices n))
  · intro m
    exact weak_L2_bounded_tests (F.measurable m) (F.finite m)
      (fun n => F.support m (L.indices n)) (L.weak m) ψ hψ D hD
  · have he (m : ℕ) : (∫ x, ψ x*L.l1Value m x ∂μ) =
        ∫ x, ψ x*L.value m x ∂μ := by
      apply integral_congr_ae
      filter_upwards [(L.integrable m).coeFn_toL1] with x hx
      change L.l1Value m x = L.value m x at hx
      rw [hx]
    simpa only [he] using bounded_test_L1_tendsto hg ψ hψ D hD

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Passing weak L1 convergence through uniform L1 approximations -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Published
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem WeakL1Converges.of_L1_approximations
    {f : ℕ → X → ℝ} {g : X → ℝ}
    (hfi : ∀ n, Integrable (f n) μ) (hgm : Measurable g) (hgi : Integrable g μ)
    {u : ℕ → ℕ → X → ℝ} {v : ℕ → X → ℝ}
    (hui : ∀ j n, Integrable (u j n) μ) (hw : ∀ j, WeakL1Converges μ (u j) (v j))
    {δ : ℕ → ℝ} (hδ0 : ∀ j, 0 ≤ δ j) (hδ : Tendsto δ atTop (𝓝 0))
    (he : ∀ j n, eLpNorm (fun x => f n x-u j n x) 1 μ ≤ ENNReal.ofReal (δ j))
    (hg : ∀ j, eLpNorm (fun x => v j x-g x) 1 μ ≤ ENNReal.ofReal (δ j)) :
    WeakL1Converges μ f g := by
  refine ⟨hgm,hgi,?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  let D : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  have hD x : ‖ψ x‖ ≤ D := (hC x).trans (le_max_left _ _)
  have herr j n : |(∫ x, ψ x*f n x ∂μ)-(∫ x, ψ x*u j n x ∂μ)| ≤ D*δ j := by
    exact (abs_bounded_test_difference _ _ (hfi n) (hui j n) ψ hψ D hD).trans
      (mul_le_mul_of_nonneg_left
        (integral_abs_le_of_eLpNorm_le ((hfi n).sub (hui j n)) (hδ0 j) (he j n)) D.coe_nonneg)
  have hlast j : |(∫ x, ψ x*v j x ∂μ)-(∫ x, ψ x*g x ∂μ)| ≤ D*δ j := by
    exact (abs_bounded_test_difference _ _ (hw j).2.1 hgi ψ hψ D hD).trans
      (mul_le_mul_of_nonneg_left
        (integral_abs_le_of_eLpNorm_le ((hw j).2.1.sub hgi) (hδ0 j) (hg j)) D.coe_nonneg)
  have ht : Tendsto (fun j => (D:ℝ)*δ j) atTop (𝓝 0) := by
    simpa only [mul_zero] using hδ.const_mul (D:ℝ)
  apply scalar_tendsto_of_uniform_approximations _ _ _ _ _ ht herr
    (fun j => (hw j).2.2 ψ hψ ⟨C,hC⟩)
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg) (fun j => by simpa only [Real.dist_eq] using hlast j) ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Entropy tails preserve weak convergence with the first velocity moment -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure (X × Velocity)}

theorem weak_linearMoment {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hfi : ∀ n, Integrable (entropyGauge (f n)) μ)
    (hfb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ) ≤ C)
    (hgm : Measurable g) (hg : ∀ p, 0 ≤ g p)
    (hgi : Integrable (entropyGauge g) μ) (hgb : (∫ p, entropyGauge g p ∂μ) ≤ C)
    (hw : Published.WeakL1Converges μ f g) :
    Published.WeakL1Converges μ (fun n => linearMoment (f n)) (linearMoment g) := by
  let R : ℕ → ℝ := fun j => (j:ℝ)+1
  have hR j : 0 < R j := by dsimp [R]; positivity
  have hC : 0 ≤ C := (integral_nonneg (entropyGauge_nonneg hg)).trans hgb
  let a : ℕ → X × Velocity → ℝ := fun j p => if ‖p.2‖ ≤ R j then 1+‖p.2‖ else 0
  have ham j : Measurable (a j) := (measurable_const.add measurable_snd.norm).ite
    (measurableSet_le measurable_snd.norm measurable_const) measurable_const
  have hab j p : |a j p| ≤ 1+R j := by
    dsimp only [a]
    split_ifs with hp
    · rw [abs_of_nonneg (by positivity)]
      linarith
    · simp only [abs_zero]
      linarith [hR j]
  have he j (u : X × Velocity → ℝ) :
      (fun p => a j p*u p) = velocityLinearCut (R j) u := by
    ext p
    dsimp only [a,velocityLinearCut,linearMoment]
    split_ifs <;> simp only [zero_mul]
  have hc j : Published.WeakL1Converges μ
      (fun n => velocityLinearCut (R j) (f n)) (velocityLinearCut (R j) g) := by
    have h := hw.bounded_mul (ham j) (1+R j) (hab j)
    rw [show (fun n p => a j p*f n p) = (fun n => velocityLinearCut (R j) (f n)) from
      funext (fun n => he j (f n)),he j g] at h
    exact h
  apply Published.WeakL1Converges.of_L1_approximations
    (fun n => linearMoment_integrable (hfm n) (hf n) (hfi n))
    (linearMoment_measurable hgm) (linearMoment_integrable hgm hg hgi)
    (fun j n => velocityLinearCut_integrable (R j) (hfm n) (hf n) (hfi n)) hc
    (δ := fun j => 2*C/R j) (fun j => by positivity)
  · exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  · exact fun j n => velocityLinearCut_L1_error (hR j) (hfm n) (hf n) (hfi n) (hfb n)
  · intro j
    change eLpNorm (velocityLinearCut (R j) g-linearMoment g) 1 μ ≤ _
    rw [eLpNorm_sub_comm]
    exact velocityLinearCut_L1_error (hR j) hgm hg hgi hgb

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
