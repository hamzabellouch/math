import OAI.MathematicalPhysics.Boltzmann.Approximation.CutoffEntropyMeasure
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralFixedPoint
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianEstimates
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyIntegralBalance
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticEntropyErrorLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.JetBarriers
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace OAI

section

/-! # A finite time measure equivalent to Lebesgue measure on every time window -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def timeWeight (t : ℝ) : ℝ := Real.exp (-(t^2))
def finiteTimeMeasure : Measure ℝ := volume.withDensity (fun t => ENNReal.ofReal (timeWeight t))

theorem timeWeight_measurable : Measurable timeWeight := by unfold timeWeight; fun_prop

theorem timeWeight_pos (t : ℝ) : 0 < timeWeight t := Real.exp_pos _

instance finiteTimeMeasure_finite : IsFiniteMeasure finiteTimeMeasure := by
  apply isFiniteMeasure_withDensity
  have hi : Integrable timeWeight := by
    change Integrable (fun t : ℝ => Real.exp (-(t^2)))
    simpa using (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1))
  exact ((hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun t => (timeWeight_pos t).le))).mp hi.2).ne

def windowInverseWeight (T t : ℝ) : ℝ := (Icc 0 T).indicator (fun t => Real.exp (t^2)) t

theorem windowInverseWeight_measurable (T : ℝ) : Measurable (windowInverseWeight T) :=
  (by fun_prop : Measurable (fun t : ℝ => Real.exp (t^2))).indicator measurableSet_Icc

theorem windowInverseWeight_nonneg (T t : ℝ) : 0 ≤ windowInverseWeight T t := by
  exact indicator_nonneg (fun t _ => (Real.exp_pos (t^2)).le) t

theorem windowInverseWeight_bound {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    |windowInverseWeight T t| ≤ Real.exp (T^2) := by
  rw [abs_of_nonneg (windowInverseWeight_nonneg T t)]
  by_cases ht : t ∈ Icc 0 T
  · simp only [windowInverseWeight,indicator_of_mem ht]
    apply Real.exp_le_exp.mpr
    nlinarith [ht.1,ht.2]
  · simp only [windowInverseWeight,indicator_of_notMem ht]
    exact (Real.exp_pos _).le

theorem finiteTimeMeasure_reweight (T : ℝ) :
    finiteTimeMeasure.withDensity (fun t => ENNReal.ofReal (windowInverseWeight T t)) =
      volume.restrict (Icc 0 T) := by
  rw [finiteTimeMeasure,← withDensity_mul _ timeWeight_measurable.ennreal_ofReal
    (windowInverseWeight_measurable T).ennreal_ofReal]
  have he : (fun t => ENNReal.ofReal (timeWeight t) *
      ENNReal.ofReal (windowInverseWeight T t)) = (Icc 0 T).indicator (fun _ => 1) := by
    funext t
    by_cases ht : t ∈ Icc 0 T
    · simp only [windowInverseWeight,indicator_of_mem ht,timeWeight]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      simp
    · simp [windowInverseWeight,ht]
  change volume.withDensity (fun t => ENNReal.ofReal (timeWeight t) *
    ENNReal.ofReal (windowInverseWeight T t)) = _
  rw [he]
  exact withDensity_indicator_one measurableSet_Icc

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Positive local cutoff iteration along the actual free transport -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.GaussianLocal

def state (f : ℝ × JetPrototype.Phase → ℝ) (z : (ℝ × Space) × Velocity) : ℝ :=
  f (z.1.1, (z.1.2, z.2))

def forcing (β b L : ℝ) (f : ℝ × JetPrototype.Phase → ℝ)
    (z : ℝ × JetPrototype.Phase) : ℝ :=
  GaussianCutoff.source β b L (state f) ((z.1, z.2.1), z.2.2)

theorem measurable_state {f : ℝ × JetPrototype.Phase → ℝ} (hf : Measurable f) :
    Measurable (state f) := hf.comp (by fun_prop)

theorem measurable_forcing {f : ℝ × JetPrototype.Phase → ℝ} (hf : Measurable f)
    (β b L : ℝ) : Measurable (forcing β b L f) :=
  (GaussianCutoff.measurable_source (measurable_state hf) β b L).comp (by fun_prop)

theorem measurable_flight : Measurable (fun z : ℝ × JetPrototype.Phase => JetBarrier.flight z.1 z.2) := by
  unfold JetBarrier.flight VelocityWeight.transverse VelocityWeight.axial
  fun_prop

theorem exists_normalized {β b L T A R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hloss : GaussianCutoff.lossConstant β b * R ≤ L)
    (hball : A + T * (GaussianCutoff.gainConstant β b * R ^ 2 + L * R) ≤ R)
    (hsmall : T * (2 * R * (GaussianCutoff.gainConstant β b + GaussianCutoff.lossConstant β b) + L) < 1)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀m : Measurable f₀)
    (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) :
    ∃ f : ℝ × JetPrototype.Phase → ℝ, Measurable f ∧
      (∀ z, 0 ≤ f z ∧ f z ≤ R) ∧
      ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing β b L f) z := by
  let S := GaussianCutoff.gainConstant β b * R ^ 2 + L * R
  let K := 2 * R * (GaussianCutoff.gainConstant β b + GaussianCutoff.lossConstant β b) + L
  have hS : 0 ≤ S := by
    obtain ⟨hG, hC⟩ := GaussianCutoff.constants_nonneg hb β
    dsimp [S]
    positivity
  have hK : 0 ≤ K := by
    obtain ⟨hG, hC⟩ := GaussianCutoff.constants_nonneg hb β
    dsimp [K]
    positivity
  obtain ⟨f, hf⟩ := PositiveIntegral.exists_fixed_point hT hL hA hR hS hK hball hsmall
    measurable_flight hf₀m hf₀
    (fun f => forcing β b L (fun z => f.val z))
    (fun f => measurable_forcing (BoundedMeasurable.measurable _ f.val) β b L)
    (fun f z => GaussianCutoff.source_bounds hβ hb hR hloss
      (fun p => f.property (p.1.1, (p.1.2, p.2))) ((z.1, z.2.1), z.2.2))
    (fun f g z => by
      apply (GaussianCutoff.source_difference hβ hb hL hR (show 0 ≤ dist f g from dist_nonneg)
        (measurable_state (BoundedMeasurable.measurable _ f.val))
        (measurable_state (BoundedMeasurable.measurable _ g.val))
        (fun p => f.property (p.1.1, (p.1.2, p.2)))
        (fun p => g.property (p.1.1, (p.1.2, p.2)))
        (fun p => BoundedMeasurable.dist_apply_le _ f.val g.val (p.1.1, (p.1.2, p.2)))
        ((z.1, z.2.1), z.2.2)))
  exact ⟨fun z => f.val z, BoundedMeasurable.measurable _ f.val, f.property, hf⟩

end BoltzmannNonuniqueness.GaussianLocal

end

end

section

/-! # Countable cold gain sums and the exact hot-source identity -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace BoltzmannNonuniqueness.GaussianCutoff

variable {X I : Type*} [MeasurableSpace X]

theorem gain_family_summable {β b R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b) (hR : 0 ≤ R)
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    Summable (fun i => gain β b (c i) (c i) p) ∧
      (∑' i, gain β b (c i) (c i) p) ≤ gain β b F F p := by
  have hn (i) : 0 ≤ gain β b (c i) (c i) p :=
    gain_nonneg (fun q => (hc i q).1) (fun q => (hc i q).1) β b p
  have hs (s : Finset I) : (∑ i ∈ s, gain β b (c i) (c i) p) ≤ gain β b F F p :=
    finite_sum_gain_le hβ hb hR s (fun i _ => hcm i) hFm
      (fun i _ q => (hc i q).1) (fun i _ q => (hc i q).2) hF (hSum s) p
  exact ⟨summable_of_sum_le hn hs, Real.tsum_le_of_sum_le hn hs⟩

theorem tsum_coldSource {β b R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (L : ℝ) {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    (∑' i, coldSource β b L F (c i) p) =
      (∑' i, gain β b (c i) (c i) p) + (L - frequency β b F p) * (∑' i, c i p) := by
  have hg := (gain_family_summable hβ hb hR hcm hFm hc hF hSum p).1
  have hcs : Summable (fun i => c i p) :=
    summable_of_sum_le (fun i => (hc i p).1) (fun s => hSum s p)
  unfold coldSource
  rw [hg.tsum_add (hcs.mul_left _), tsum_mul_left]

theorem hot_source_identity {β b R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (L : ℝ) {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    source β b L F p - (∑' i, coldSource β b L F (c i) p) =
      (gain β b F F p - ∑' i, gain β b (c i) (c i) p) +
      (L - frequency β b F p) * (F p - ∑' i, c i p) := by
  rw [tsum_coldSource hβ hb hR L hcm hFm hc hF hSum]
  unfold source
  ring

end BoltzmannNonuniqueness.GaussianCutoff

end

end

section

/-! # Uniqueness for the actual normalized positive cutoff equation -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.GaussianLocal

theorem normalized_unique {β b L T R : ℝ} (hβ : 0 < β) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : GaussianCutoff.lossConstant β b * R ≤ L)
    (hsmall : T * (2 * R * (GaussianCutoff.gainConstant β b + GaussianCutoff.lossConstant β b) + L) < 1)
    (f₀ : JetPrototype.Phase → ℝ) {f g : ℝ × JetPrototype.Phase → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ R) (hg : ∀ z, 0 ≤ g z ∧ g z ≤ R)
    (hfeq : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing β b L f) z)
    (hgeq : ∀ z, g z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing β b L g) z) : f = g := by
  let P := ℝ × JetPrototype.Phase
  let f' : BoundedMeasurable.PositiveBall P R :=
    ⟨BoundedMeasurable.ofBounded P f hfm R (fun z => by rw [abs_of_nonneg (hf z).1]; exact (hf z).2), hf⟩
  let g' : BoundedMeasurable.PositiveBall P R :=
    ⟨BoundedMeasurable.ofBounded P g hgm R (fun z => by rw [abs_of_nonneg (hg z).1]; exact (hg z).2), hg⟩
  let S := GaussianCutoff.gainConstant β b * R ^ 2 + L * R
  let K := 2 * R * (GaussianCutoff.gainConstant β b + GaussianCutoff.lossConstant β b) + L
  have hK : 0 ≤ K := by
    obtain ⟨hG,hC⟩ := GaussianCutoff.constants_nonneg hb β
    dsimp [K]
    positivity
  have he : f' = g' := PositiveIntegral.fixed_point_unique hT hL hK hsmall
    measurable_flight f₀ (fun u => forcing β b L (fun z => u.val z))
    (fun u => measurable_forcing (BoundedMeasurable.measurable _ u.val) β b L)
    (fun u z => by
      have h := GaussianCutoff.source_bounds hβ hb hR hloss
        (fun p => u.property (p.1.1,(p.1.2,p.2))) ((z.1,z.2.1),z.2.2)
      change 0 ≤ forcing β b L (fun z => u.val z) z ∧ _ at h
      rw [abs_of_nonneg h.1]
      exact h.2)
    (fun u v z => GaussianCutoff.source_difference hβ hb hL hR
      (show 0 ≤ dist u v from dist_nonneg)
      (measurable_state (BoundedMeasurable.measurable _ u.val))
      (measurable_state (BoundedMeasurable.measurable _ v.val))
      (fun p => u.property (p.1.1,(p.1.2,p.2)))
      (fun p => v.property (p.1.1,(p.1.2,p.2)))
      (fun p => BoundedMeasurable.dist_apply_le _ u.val v.val (p.1.1,(p.1.2,p.2)))
      ((z.1,z.2.1),z.2.2)) hfeq hgeq
  exact funext (fun z => congrArg (fun u : BoundedMeasurable.PositiveBall P R => u.val z) he)

end BoltzmannNonuniqueness.GaussianLocal

end

end

section

/-! # Actual positive mild solutions for bounded Gaussian cutoff data -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.GaussianLocal

def physical (β : ℝ) (f : ℝ × JetPrototype.Phase → ℝ) (z : ℝ × JetPrototype.Phase) : ℝ :=
  JetGaussianMoments.kernel β z.2.2 * f z

theorem physical_source (β b L : ℝ) (f : ℝ × JetPrototype.Phase → ℝ)
    (z : ℝ × JetPrototype.Phase) :
    JetGaussianMoments.kernel β z.2.2 * forcing β b L f z =
      CollisionCutoff.gain b (fun v => physical β f (z.1, (z.2.1, v))) z.2.2 +
      (L - CollisionCutoff.frequency b (fun v => physical β f (z.1, (z.2.1, v))) z.2.2) *
        physical β f z := by
  unfold forcing GaussianCutoff.source
  have he := GaussianCutoff.gain_eq_actual β b (state f) ((z.1, z.2.1), z.2.2)
  dsimp only at he
  rw [mul_add, he]
  simp only [state, physical, GaussianCutoff.frequency, KineticCollisionNullSets.frequency]
  ring

theorem time_eq {T t : ℝ} (ht : t ∈ Icc 0 T) : PositiveIntegral.time T t = t := by
  unfold PositiveIntegral.time
  rw [min_eq_right ht.2, max_eq_right ht.1]

theorem physical_mild {β b L T : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    {f : ℝ × JetPrototype.Phase → ℝ}
    (hf : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing β b L f) z)
    {t : ℝ} (ht : t ∈ Icc 0 T) (p : JetPrototype.Phase) :
    physical β f (t, p) =
      Real.exp (-L * t) * (JetGaussianMoments.kernel β p.2 * f₀ (JetBarrier.flight (-t) p)) +
      ∫ r in 0..t, Real.exp (-L * (t - r)) *
        (CollisionCutoff.gain b
          (fun v => physical β f (r, ((JetBarrier.flight (r-t) p).1, v))) p.2 +
        (L - CollisionCutoff.frequency b
          (fun v => physical β f (r, ((JetBarrier.flight (r-t) p).1, v))) p.2) *
          physical β f (r, JetBarrier.flight (r-t) p)) := by
  change JetGaussianMoments.kernel β p.2 * f (t, p) = _
  rw [hf (t, p), PositiveIntegral.value, time_eq ht, mul_add, ← intervalIntegral.integral_const_mul]
  congr 1
  · ring
  · apply intervalIntegral.integral_congr
    intro r _
    have he := physical_source β b L f (r, JetBarrier.flight (r-t) p)
    change JetGaussianMoments.kernel β p.2 * _ = _ at he
    dsimp only at he ⊢
    rw [mul_left_comm, he]
    rfl

theorem exists_normalized_time {β b A : ℝ} (hβ : 0 < β) (hb : 0 ≤ b) (hA : 0 < A)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀m : Measurable f₀)
    (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) :
    ∃ T L : ℝ, 0 < T ∧ 0 ≤ L ∧
      ∃ f : ℝ × JetPrototype.Phase → ℝ, Measurable f ∧
        (∀ z, 0 ≤ f z ∧ f z ≤ 2 * A) ∧
        ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing β b L f) z := by
  obtain ⟨hG, hC⟩ := GaussianCutoff.constants_nonneg hb β
  let R := 2 * A
  let L := GaussianCutoff.lossConstant β b * R
  let S := GaussianCutoff.gainConstant β b * R ^ 2 + L * R
  let K := 2 * R * (GaussianCutoff.gainConstant β b + GaussianCutoff.lossConstant β b) + L
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hL : 0 ≤ L := mul_nonneg hC hR
  have hS : 0 ≤ S := add_nonneg (mul_nonneg hG (sq_nonneg _)) (mul_nonneg hL hR)
  have hK : 0 ≤ K := add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hR) (add_nonneg hG hC)) hL
  let T := min (A / (S + 1)) ((1 / 2) / (K + 1))
  have hT : 0 < T := lt_min (div_pos hA (by positivity)) (div_pos (by norm_num) (by positivity))
  have hTS : T * (S + 1) ≤ A :=
    (le_div_iff₀ (by positivity : 0 < S + 1)).mp (min_le_left _ _)
  have hTK : T * (K + 1) ≤ 1 / 2 :=
    (le_div_iff₀ (by positivity : 0 < K + 1)).mp (min_le_right _ _)
  have hball : A + T * S ≤ R := by dsimp [R]; nlinarith
  have hsmall : T * K < 1 := by nlinarith
  exact ⟨T, L, hT, hL, exists_normalized hβ hb hL hT.le hA.le hR le_rfl hball hsmall hf₀m hf₀⟩

end BoltzmannNonuniqueness.GaussianLocal

end

end

section

/-! # Fatou's lemma removes positive Gaussian regularization from cutoff dissipation -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem cutoffExtendedDissipation_regularization_le_liminf (μ : Measure X) (b : ℝ)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z) :
    cutoffExtendedDissipation μ b f ≤
      liminf (fun δ : ℝ => cutoffExtendedDissipation μ b (gaussianRegularizedDensity δ f)) (𝓝[>] 0) := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  let w : (X × (Velocity × Velocity)) × Sphere → ℝ≥0∞ := fun z =>
    if ‖z.1.2.1-z.1.2.2‖ < b then ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2) else 0
  let A : (X × (Velocity × Velocity)) × Sphere → ℝ := fun z =>
    f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)
  let B : (X × (Velocity × Velocity)) × Sphere → ℝ := fun z =>
    f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)
  let a : ℝ → (X × (Velocity × Velocity)) × Sphere → ℝ := fun δ z =>
    gaussianRegularizedDensity δ f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*
      gaussianRegularizedDensity δ f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)
  let c : ℝ → (X × (Velocity × Velocity)) × Sphere → ℝ := fun δ z =>
    gaussianRegularizedDensity δ f (z.1.1,z.1.2.1)*gaussianRegularizedDensity δ f (z.1.1,z.1.2.2)
  have hcm (δ : ℝ) : Measurable (c δ) :=
    ((gaussianRegularizedDensity_measurable δ hfm).comp
      (measurable_fst.fst.prodMk measurable_fst.snd.fst)).mul
      ((gaussianRegularizedDensity_measurable δ hfm).comp
        (measurable_fst.fst.prodMk measurable_fst.snd.snd))
  have ham (δ : ℝ) : Measurable (a δ) := (hcm δ).comp scatterTripleEquiv.measurable
  have hwm : Measurable w := by
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) ?_ measurable_const
    apply Measurable.ennreal_ofReal
    unfold collisionKernel normalComponent
    fun_prop
  have hprod := lintegral_extendedEntropyProduction_le_liminf (μ := ν) (l := 𝓝[>] (0:ℝ))
    ham hcm hwm
    (Eventually.of_forall (fun z => mul_nonneg (hfn _) (hfn _)))
    (Eventually.of_forall (fun z => mul_nonneg (hfn _) (hfn _)))
    (A := A) (B := B) (by
      filter_upwards [] with z
      have hlim (p : X × Velocity) : Tendsto (fun δ : ℝ => gaussianRegularizedDensity δ f p)
          (𝓝[>] 0) (𝓝 (f p)) := by
        have hc : Continuous (fun δ : ℝ => f p+δ*Real.exp (-2*‖p.2‖^2)) :=
          continuous_const.add (continuous_id.mul_const _)
        simpa only [gaussianRegularizedDensity,zero_mul,add_zero] using
          (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      exact ⟨(hlim _).mul (hlim _),(hlim _).mul (hlim _)⟩) (by
      filter_upwards [] with z
      have hpos (p : X × Velocity) : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < gaussianRegularizedDensity δ f p := by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact add_pos_of_nonneg_of_pos (hfn _) (mul_pos hδ (Real.exp_pos _))
      exact ⟨(hpos _).and (hpos _) |>.mono (fun δ h => mul_pos h.1 h.2),
        (hpos _).and (hpos _) |>.mono (fun δ h => mul_pos h.1 h.2)⟩)
  have he (g : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
      cutoffExtendedProduction b g z = w z * extendedEntropyProduction
        (g (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*g (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
        (g (z.1.1,z.1.2.1)*g (z.1.1,z.1.2.2)) := by
    dsimp [cutoffExtendedProduction,w]
    split_ifs <;> simp
  have hi : (∫⁻ z, cutoffExtendedProduction b f z ∂ν) ≤
      liminf (fun δ : ℝ => ∫⁻ z, cutoffExtendedProduction b (gaussianRegularizedDensity δ f) z ∂ν)
        (𝓝[>] 0) := by
    simpa only [he,A,B,a,c] using hprod
  have hm := ENNReal.le_liminf_mul (u := fun _ : ℝ => (4:ℝ≥0∞)⁻¹)
    (v := fun δ => ∫⁻ z, cutoffExtendedProduction b (gaussianRegularizedDensity δ f) z ∂ν)
    (f := 𝓝[>] (0:ℝ))
  have hle := (mul_le_mul_right hi (4:ℝ≥0∞)⁻¹).trans (by
    simpa only [liminf_const,Pi.mul_def] using hm)
  exact hle

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Positive local existence for the actual cutoff collision equation -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.GaussianLocal

/-- A bounded Gaussian datum has a positive mild solution for a positive time.
The constant damping is added and subtracted inside the exact collision source. -/
theorem exists_positive_mild {β b A : ℝ} (hβ : 0 < β) (hb : 0 ≤ b) (hA : 0 < A)
    {g₀ : JetPrototype.Phase → ℝ} (hg₀m : Measurable g₀)
    (hg₀ : ∀ p, 0 ≤ g₀ p ∧ g₀ p ≤ A * JetGaussianMoments.kernel β p.2) :
    ∃ T L : ℝ, 0 < T ∧ 0 ≤ L ∧
      ∃ g : ℝ × JetPrototype.Phase → ℝ, Measurable g ∧
        (∀ z, 0 ≤ g z ∧ g z ≤ (2 * A) * JetGaussianMoments.kernel β z.2.2) ∧
        (∀ t ∈ Icc 0 T, ∀ p, g (t, p) =
          Real.exp (-L * t) * g₀ (JetBarrier.flight (-t) p) +
          ∫ r in 0..t, Real.exp (-L * (t - r)) *
            (CollisionCutoff.gain b
              (fun v => g (r, ((JetBarrier.flight (r-t) p).1, v))) p.2 +
            (L - CollisionCutoff.frequency b
              (fun v => g (r, ((JetBarrier.flight (r-t) p).1, v))) p.2) *
              g (r, JetBarrier.flight (r-t) p))) := by
  let f₀ : JetPrototype.Phase → ℝ := fun p => g₀ p / JetGaussianMoments.kernel β p.2
  have hW (v : Velocity) : 0 < JetGaussianMoments.kernel β v := Real.exp_pos _
  have hWm : Measurable (fun p : JetPrototype.Phase => JetGaussianMoments.kernel β p.2) := by
    unfold JetGaussianMoments.kernel
    fun_prop
  have hf₀m : Measurable f₀ := hg₀m.div hWm
  have hf₀ (p) : 0 ≤ f₀ p ∧ f₀ p ≤ A :=
    ⟨div_nonneg (hg₀ p).1 (hW _).le, (div_le_iff₀ (hW _)).mpr (hg₀ p).2⟩
  obtain ⟨T, L, hT, hL, f, hfm, hfb, hfeq⟩ := exists_normalized_time hβ hb hA hf₀m hf₀
  refine ⟨T, L, hT, hL, physical β f, ?_, ?_, ?_⟩
  · exact (hWm.comp measurable_snd).mul hfm
  · intro z
    exact ⟨mul_nonneg (hW _).le (hfb z).1,
      (mul_le_mul_of_nonneg_left (hfb z).2 (hW _).le).trans_eq (mul_comm _ _)⟩
  · intro t ht p
    have h := physical_mild hfeq ht p
    have hi : JetGaussianMoments.kernel β p.2 * f₀ (JetBarrier.flight (-t) p) =
        g₀ (JetBarrier.flight (-t) p) := by
      change JetGaussianMoments.kernel β p.2 *
        (g₀ (JetBarrier.flight (-t) p) / JetGaussianMoments.kernel β p.2) = _
      exact mul_div_cancel₀ _ (ne_of_gt (hW _))
    rwa [hi] at h

end BoltzmannNonuniqueness.GaussianLocal

end

end

end OAI
