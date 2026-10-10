import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralFixedPoint
import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedVelocityIntegral
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedBranchingBlocks
import OAI.MathematicalPhysics.Boltzmann.Branching.GainEntropyTail
import OAI.MathematicalPhysics.Boltzmann.Branching.LinearCharacteristicBalance
import OAI.MathematicalPhysics.Boltzmann.Branching.Moments
import OAI.MathematicalPhysics.Boltzmann.Branching.VaryingBoundedMultiplier
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianEstimates
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyIntegralBalance
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicFiniteMild
import OAI.MathematicalPhysics.Boltzmann.Compactness.RenormalizedIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMassClip
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

section

/-! # The positive iteration preserves the actual velocity support -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem exists_supported_weighted_solution {N T A : ℝ} (hN : 0 < N) (hT : 0 ≤ T)
    {f₀ : Density} (hfm : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A)
    (h₀ : ∀ p, N < ‖p.2‖ → f₀ p = 0) :
    ∃ f : BoundedMeasurable.PositiveBall (ℝ × Phase) (max A 1),
      (∀ z, f.val z = PositiveIntegral.value T (dampingRate N) TorusFlight.flight f₀
        (scaledSource T (scalingRate N) N (fun z => f.val z)) z) ∧
      (∀ z, N < ‖z.2.2‖ → f.val z = 0) := by
  have hR : 1 ≤ max A 1 := le_max_right _ _
  have hL : 0 < dampingRate N :=
    (sourceLipschitz_nonneg N).trans_lt (dampingRate_gt_sourceLipschitz hN)
  have hex : ∃ f : BoundedMeasurable.PositiveBall (ℝ × Phase) (max A 1),
      ∀ z, f.val z = PositiveIntegral.value T (dampingRate N) TorusFlight.flight f₀
        (localize N (scaledSource T (scalingRate N) N (fun z => f.val z))) z := by
    apply PositiveIntegral.exists_damped_fixed_point hT hL (by linarith)
      (sourceLipschitz_nonneg N) (dampingRate_gt_sourceLipschitz hN) TorusFlight.measurable_flight hfm
      (fun p => ⟨(hf₀ p).1,(hf₀ p).2.trans (le_max_left _ _)⟩)
      (fun f => localize N (scaledSource T (scalingRate N) N (fun z => f.val z)))
    · intro f
      exact localize_measurable N (scaledSource_measurable _ _ _ (BoundedMeasurable.measurable _ f.val))
    · intro f z
      apply localize_bounds (mul_nonneg hL.le (by linarith)) _ z
      intro z
      exact scaledSource_ball hN hT hR (BoundedMeasurable.measurable _ f.val)
        (fun z => (f.property z).1) (fun z => (f.property z).2) z
    · intro f g z
      apply localize_difference (mul_nonneg (sourceLipschitz_nonneg N) dist_nonneg) _ z
      intro z
      exact scaledSource_difference hN (BoundedMeasurable.measurable _ f.val)
        (BoundedMeasurable.measurable _ g.val) (fun z => (f.property z).1) (fun z => (g.property z).1)
        (fun z => BoundedMeasurable.dist_apply_le (ℝ × Phase) f.val g.val z) z
  obtain ⟨f,hf⟩ := hex
  have hsupport : ∀ z, N < ‖z.2.2‖ → f.val z = 0 := localized_fixed_point_zero f₀ h₀ hf
  refine ⟨f,?_,hsupport⟩
  rw [localized_scaledSource_eq hN.le hsupport] at hf
  exact hf

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Supported positive mild approximants and their finite entropy class -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

structure BoundedCutoffSolution (N T : ℝ) (f₀ : Density) where
  density : ℝ × Phase → ℝ
  measurable : Measurable density
  nonnegative : ∀ z, 0 ≤ density z
  bounded : ∃ B : ℝ, ∀ z, density z ≤ B
  support : ∀ z, N < ‖z.2.2‖ → density z = 0
  mild : ∀ z, density z = PositiveIntegral.value T (lossBound N) TorusFlight.flight f₀
    (fun w => positiveSource N (fun p => density (w.1,p)) w.2) z

theorem exists_supported_cutoff_solution {N T A : ℝ} (hN : 0 < N) (hT : 0 ≤ T)
    {f₀ : Density} (hfm : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A)
    (h₀ : ∀ p, N < ‖p.2‖ → f₀ p = 0) : Nonempty (BoundedCutoffSolution N T f₀) := by
  obtain ⟨f,hf,hsupport⟩ := exists_supported_weighted_solution hN hT hfm hf₀ h₀
  let F : ℝ × Phase → ℝ := fun z => Real.exp (scalingRate N*PositiveIntegral.time T z.1)*f.val z
  have hFm : Measurable F := by
    apply Measurable.mul _ (BoundedMeasurable.measurable (ℝ × Phase) f.val)
    unfold PositiveIntegral.time
    fun_prop
  refine ⟨⟨F,hFm,?_,⟨Real.exp (scalingRate N*T)*max A 1,?_⟩,?_,?_⟩⟩
  · intro z
    exact mul_nonneg (Real.exp_pos _).le (f.property z).1
  · intro z
    have he : Real.exp (scalingRate N*PositiveIntegral.time T z.1) ≤ Real.exp (scalingRate N*T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (PositiveIntegral.time_bounds hT z.1).2
        (scalingRate_pos hN).le)
    exact mul_le_mul he (f.property z).2 (f.property z).1 (Real.exp_pos _).le
  · intro z hz
    change Real.exp _*f.val z = 0
    rw [hsupport z hz,mul_zero]
  · intro z
    have h := congrArg (fun r => Real.exp (scalingRate N*PositiveIntegral.time T z.1)*r) (hf z)
    change F z = _ at h
    have hs : scaledSource T (scalingRate N) N (fun z => f.val z) =
        (fun w => Real.exp (-scalingRate N*PositiveIntegral.time T w.1)*
          positiveSource N (fun p => F (w.1,p)) w.2) := by
      funext w
      exact scaledSource_eq _ _ _ _ _
    rw [hs] at h
    simpa only [dampingRate,PositiveIntegral.value_rescale hT] using h

theorem BoundedCutoffSolution.finiteEntropy {N T : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N T f₀) (hN : 0 ≤ N) (t : ℝ) :
    FiniteEntropyDatum (fun p => S.density (t,p)) := by
  obtain ⟨B,hB⟩ := S.bounded
  exact bounded_velocity_finiteEntropy hN
    (S.measurable.comp (measurable_const.prodMk measurable_id))
    (fun p => S.nonnegative (t,p)) (fun p => hB (t,p)) (fun p => S.support (t,p))

theorem BoundedCutoffSolution.initial {N T : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N T f₀) (hT : 0 ≤ T) (p : Phase) : S.density (0,p) = f₀ p := by
  rw [S.mild]
  simp only [PositiveIntegral.value,PositiveIntegral.time,min_eq_right hT,max_self,
    mul_zero,Real.exp_zero,neg_zero,TorusFlight.flight_zero,one_mul,
    intervalIntegral.integral_same,add_zero]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual bounded initial approximations for the global construction -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

def initialApproximation (N : ℝ) (f : Density) (p : Phase) : ℝ :=
  if ‖p.2‖ ≤ N then min N (max 0 (f p)) else 0

theorem initialApproximation_measurable (N : ℝ) {f : Density} (hf : Measurable f) :
    Measurable (initialApproximation N f) := by
  unfold initialApproximation
  exact Measurable.ite (measurableSet_le measurable_snd.norm measurable_const)
    (measurable_const.min (measurable_const.max hf)) measurable_const

theorem initialApproximation_bounds {N : ℝ} (hN : 0 ≤ N) (f : Density) (p : Phase) :
    0 ≤ initialApproximation N f p ∧ initialApproximation N f p ≤ N := by
  unfold initialApproximation
  split_ifs
  · exact ⟨le_min hN (le_max_left _ _),min_le_left _ _⟩
  · exact ⟨le_rfl,hN⟩

theorem initialApproximation_support (N : ℝ) (f : Density) (p : Phase) (hp : N < ‖p.2‖) :
    initialApproximation N f p = 0 := by
  simp only [initialApproximation,ite_eq_right_iff]
  intro h
  exact False.elim ((not_le_of_gt hp) h)

theorem initialApproximation_le {N : ℝ} {f : Density}
    (hf : ∀ p, 0 ≤ f p) (p : Phase) : initialApproximation N f p ≤ f p := by
  unfold initialApproximation
  split_ifs
  · rw [max_eq_right (hf p)]
    exact min_le_right _ _
  · exact hf p

theorem initialApproximation_tendsto {f : Density} (hf : ∀ p, 0 ≤ f p) (p : Phase) :
    Tendsto (fun N : ℝ => initialApproximation N f p) atTop (𝓝 (f p)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (max ‖p.2‖ (f p))] with N hN
  have hv : ‖p.2‖ ≤ N := (le_max_left _ _).trans hN
  have hfN : f p ≤ N := (le_max_right _ _).trans hN
  simp [initialApproximation,hv,max_eq_right (hf p),min_eq_right hfN]

theorem exists_initial_approximation_solution {N T : ℝ} (hN : 0 < N) (hT : 0 ≤ T)
    {f : Density} (hf : Measurable f) :
    Nonempty (BoundedCutoffSolution N T (initialApproximation N f)) :=
  exists_supported_cutoff_solution hN hT (initialApproximation_measurable N hf)
    (initialApproximation_bounds hN.le f) (initialApproximation_support N f)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Initial entropy bounds independent of the collision regularization -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem initialApproximation_entropy_le {N : ℝ} (hN : 1 ≤ N) {f : Density}
    (hf : ∀ p, 0 ≤ f p) (p : Phase) :
    entropyMoment (initialApproximation N f) p ≤ entropyMoment f p := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  by_cases hv : ‖p.2‖ ≤ N
  · by_cases hfN : f p ≤ N
    · simp only [entropyMoment,initialApproximation,hv,ite_true,max_eq_right (hf p),min_eq_right hfN]
      exact le_rfl
    · have hNf : N ≤ f p := (lt_of_not_ge hfN).le
      have hfone : 1 ≤ f p := hN.trans hNf
      have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
      have hlogf : 0 ≤ Real.log (f p) := Real.log_nonneg hfone
      have hlogs : Real.log N ≤ Real.log (f p) := Real.log_le_log hN0 hNf
      simp only [entropyMoment,initialApproximation,hv,ite_true,max_eq_right (hf p),min_eq_left hNf,
        abs_of_nonneg hlogN,abs_of_nonneg hlogf]
      exact mul_le_mul hNf (by linarith) (by positivity) (hf p)
  · simp only [entropyMoment,initialApproximation,hv,ite_false,zero_mul]
    exact mul_nonneg (hf p) (by positivity)

theorem initialApproximation_finiteEntropy {N : ℝ} (hN : 0 ≤ N) {f : Density}
    (hf : Measurable f) : FiniteEntropyDatum (initialApproximation N f) :=
  bounded_velocity_finiteEntropy hN (initialApproximation_measurable N hf)
    (fun p => (initialApproximation_bounds hN f p).1)
    (fun p => (initialApproximation_bounds hN f p).2) (initialApproximation_support N f)

theorem initialApproximation_entropy_integral_le {N : ℝ} (hN : 1 ≤ N) {f : Density}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    (∫ p, entropyMoment (initialApproximation N f) p) ≤ ∫ p, entropyMoment f p := by
  exact integral_mono (initialApproximation_finiteEntropy (zero_le_one.trans hN) hfm).2.2 hi
    (initialApproximation_entropy_le hN hf)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong L1 and entropy convergence of the bounded initial approximations -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem initialApproximation_sequence_eventually_eq {f : Density} (hf : ∀ p, 0 ≤ f p) (p : Phase) :
    (fun n : ℕ => initialApproximation ((n:ℝ)+1) f p) =ᶠ[atTop] fun _ => f p := by
  have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n:ℝ) ≤ (n:ℝ)+1) tendsto_natCast_atTop_atTop
  filter_upwards [hn.eventually (eventually_ge_atTop (max ‖p.2‖ (f p)))] with n hn
  have hv : ‖p.2‖ ≤ (n:ℝ)+1 := (le_max_left _ _).trans hn
  have hfn : f p ≤ (n:ℝ)+1 := (le_max_right _ _).trans hn
  simp [initialApproximation,hv,max_eq_right (hf p),min_eq_right hfn]

theorem initialApproximation_L1_tendsto {f : Density} (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable f) :
    Tendsto (fun n : ℕ => ∫ p, |initialApproximation ((n:ℝ)+1) f p-f p|) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (F := fun n p => |initialApproximation ((n:ℝ)+1) f p-f p|)
    (f := fun _ => (0:ℝ)) f
    (fun n => ((initialApproximation_measurable ((n:ℝ)+1) hfm).sub hfm).abs.aestronglyMeasurable) hi
    (fun n => Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_of_nonneg (abs_nonneg _),abs_of_nonpos (sub_nonpos.mpr (initialApproximation_le hf p))]
      have hn := (initialApproximation_bounds (by positivity : 0 ≤ (n:ℝ)+1) f p).1
      linarith))
    (Filter.Eventually.of_forall (fun p => by
      apply tendsto_const_nhds.congr'
      filter_upwards [initialApproximation_sequence_eventually_eq hf p] with n hn
      rw [hn,sub_self,abs_zero]))
  simpa only [integral_zero] using h

theorem initialApproximation_entropy_tendsto {f : Density} (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    Tendsto (fun n : ℕ => ∫ p, entropyMoment (initialApproximation ((n:ℝ)+1) f) p)
      atTop (𝓝 (∫ p, entropyMoment f p)) := by
  have hm (n : ℕ) : Measurable (entropyMoment (initialApproximation ((n:ℝ)+1) f)) := by
    have hf' := initialApproximation_measurable ((n:ℝ)+1) hfm
    exact hf'.mul ((measurable_const.add (measurable_snd.norm.pow_const 2)).add hf'.log.abs)
  apply tendsto_integral_of_dominated_convergence (entropyMoment f) (fun n => (hm n).aestronglyMeasurable) hi
  · intro n
    filter_upwards [] with p
    have hn := (initialApproximation_bounds (by positivity : 0 ≤ (n:ℝ)+1) f p).1
    have he : 0 ≤ entropyMoment (initialApproximation ((n:ℝ)+1) f) p := by
      unfold entropyMoment
      positivity
    rw [Real.norm_of_nonneg he]
    exact initialApproximation_entropy_le (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith : 1 ≤ (n:ℝ)+1) hf p
  · filter_upwards [] with p
    apply tendsto_const_nhds.congr'
    filter_upwards [initialApproximation_sequence_eventually_eq hf p] with n hn
    simp only [entropyMoment,hn]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong initial approximations in the time-extended local phase measure -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem initialApproximation_norm_tendsto {f : Density} (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable f) :
    Tendsto (fun n : ℕ => eLpNorm (initialApproximation ((n:ℝ)+1) f-f) 1 volume) atTop (𝓝 0) := by
  have hAi (n : ℕ) : Integrable (initialApproximation ((n:ℝ)+1) f) :=
    hi.mono' (initialApproximation_measurable ((n:ℝ)+1) hfm).aestronglyMeasurable
      (ae_of_all _ (fun p => by
        rw [Real.norm_of_nonneg (initialApproximation_bounds (N := (n:ℝ)+1) (by positivity) f p).1]
        exact initialApproximation_le hf p))
  have he (n : ℕ) : eLpNorm (initialApproximation ((n:ℝ)+1) f-f) 1 volume =
      ENNReal.ofReal (∫ p, |initialApproximation ((n:ℝ)+1) f p-f p|) := by
    rw [eLpNorm_one_eq_lintegral_enorm ((hAi n).sub hi).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hAi n).sub hi)]
    rfl
  simp_rw [he]
  simpa only [Function.comp_def,ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (initialApproximation_L1_tendsto hfm hf hi)

theorem initialApproximation_time_local_strong {f : Density} (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable f)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (T R : ℝ) :
    Tendsto (fun n => eLpNorm (fun z : ℝ × Phase =>
      initialApproximation ((φ n:ℝ)+1) f z.2-f z.2) 1
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) := by
  let ν : Measure Phase := (volume : Measure Position).prod
    ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))
  have hν : ν ≤ (volume : Measure Phase) := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  have ht := (initialApproximation_norm_tendsto hfm hf hi).comp hφ.tendsto_atTop
  have hl : Tendsto (fun n => eLpNorm (initialApproximation ((φ n:ℝ)+1) f-f) 1 ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
      (fun _ => eLpNorm_mono_measure _ hν)
  have he n : eLpNorm (fun z : ℝ × Phase => initialApproximation ((φ n:ℝ)+1) f z.2-f z.2)
      1 ((volume.restrict (Icc 0 T)).prod ν) =
      eLpNorm (fun _ : ℝ => (1:ℝ)) 1 (volume.restrict (Icc 0 T))*
        eLpNorm (initialApproximation ((φ n:ℝ)+1) f-f) 1 ν := by
    simpa only [one_mul,Pi.sub_apply] using eLpNorm_mul_prod_one
      (μ := volume.restrict (Icc 0 T)) (ν := ν) (f := fun _ : ℝ => (1:ℝ))
      (g := initialApproximation ((φ n:ℝ)+1) f-f) measurable_const
      ((initialApproximation_measurable ((φ n:ℝ)+1) hfm).sub hfm)
  have hh := ENNReal.Tendsto.const_mul
    (a := eLpNorm (fun _ : ℝ => (1:ℝ)) 1 (volume.restrict (Icc 0 T))) hl
    (Or.inr (memLp_one_iff_integrable.mpr (integrable_const (1:ℝ))).eLpNorm_ne_top)
  change Tendsto (fun n => eLpNorm
    (fun z : ℝ × Phase => initialApproximation ((φ n:ℝ)+1) f z.2-f z.2)
    1 ((volume.restrict (Icc 0 T)).prod ν)) atTop (𝓝 0)
  simp_rw [he]
  simpa only [mul_zero] using hh

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform relative entropy of the actual initial truncations -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

def initialEntropyCoefficient : ℝ := 1+|1-(3/2:ℝ)*Real.log (2*Real.pi)|

theorem initialEntropyCoefficient_nonneg : 0 ≤ initialEntropyCoefficient := by
  unfold initialEntropyCoefficient
  positivity

theorem relativeEntropy_density_bound {f : Density} (hf : ∀ p, 0 ≤ f p) (p : Phase) :
    scalarRelativeEntropy (maxwellian p.2) (f p) ≤
      initialEntropyCoefficient*entropyMoment f p+maxwellian p.2 := by
  let c := |1-(3/2:ℝ)*Real.log (2*Real.pi)|
  have hc : 0 ≤ c := abs_nonneg _
  have hn := hf p
  have hE : 0 ≤ ‖p.2‖^2*f p := mul_nonneg (sq_nonneg _) (hf p)
  have hA : 0 ≤ f p*|Real.log (f p)| := mul_nonneg (hf p) (abs_nonneg _)
  have hlog := mul_le_mul_of_nonneg_left (le_abs_self (Real.log (f p))) (hf p)
  have hcoeff : ((3/2:ℝ)*Real.log (2*Real.pi)-1)*f p ≤ c*f p := by
    apply mul_le_mul_of_nonneg_right _ (hf p)
    dsimp [c]
    linarith [neg_abs_le (1-(3/2:ℝ)*Real.log (2*Real.pi))]
  have h1 := mul_nonneg hc hE
  have h2 := mul_nonneg hc hA
  unfold scalarRelativeEntropy initialEntropyCoefficient entropyMoment
  rw [log_maxwellian]
  dsimp only [c] at hcoeff h1 h2
  nlinarith

theorem initialApproximation_relativeEntropy_le {N : ℝ} (hN : 1 ≤ N) {f : Density}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    relativeEntropy (initialApproximation N f) ≤
      initialEntropyCoefficient*(∫ p, entropyMoment f p)+(∫ p : Phase, maxwellian p.2) := by
  have hg := initialApproximation_finiteEntropy (zero_le_one.trans hN) hfm
  have hgn := fun p => (initialApproximation_bounds (zero_le_one.trans hN) f p).1
  have hH := hg.integrable_relativeEntropy
  have hmajor := (hi.const_mul initialEntropyCoefficient).add integrable_maxwellian_phase
  have hineq (p : Phase) : scalarRelativeEntropy (maxwellian p.2) (initialApproximation N f p) ≤
      initialEntropyCoefficient*entropyMoment f p+maxwellian p.2 :=
    (relativeEntropy_density_bound hgn p).trans
      (add_le_add (mul_le_mul_of_nonneg_left (initialApproximation_entropy_le hN hf p)
        initialEntropyCoefficient_nonneg) le_rfl)
  have h := integral_mono hH hmajor (fun p => by
    rw [← scalarRelativeEntropy_eq (maxwellian_pos p.2)]
    exact hineq p)
  rw [integral_add' (hi.const_mul initialEntropyCoefficient) integrable_maxwellian_phase,
    integral_const_mul] at h
  exact h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Measurable spacetime form of the bounded positive collision source -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

def kineticSource (N : ℝ) (F : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ :=
  positiveSource N (fun p : (ℝ × Position) × Velocity => F (p.1.1,(p.1.2,p.2)))
    ((z.1,z.2.1),z.2.2)

theorem kineticSource_eq (N : ℝ) (F : ℝ × Phase → ℝ) (z : ℝ × Phase) :
    kineticSource N F z = positiveSource N (fun p => F (z.1,p)) z.2 := rfl

theorem kineticSource_measurable (N : ℝ) {F : ℝ × Phase → ℝ} (hF : Measurable F) :
    Measurable (kineticSource N F) := by
  have hm : Measurable (fun p : (ℝ × Position) × Velocity => F (p.1.1,(p.1.2,p.2))) :=
    hF.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact (positiveSource_measurable N hm).comp
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Bounded phase tests of the actual initial truncations -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem initialApproximation_test_tendsto {f ψ : Density}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable f)
    (hψ : Measurable ψ) (C : ℝ) (hC : ∀ p, |ψ p| ≤ C) :
    Tendsto (fun n : ℕ => ∫ p, ψ p*initialApproximation ((n:ℝ)+1) f p)
      atTop (𝓝 (∫ p, ψ p*f p)) := by
  apply tendsto_integral_of_dominated_convergence (fun p => C*f p)
    (fun n => (hψ.mul (initialApproximation_measurable ((n:ℝ)+1) hfm)).aestronglyMeasurable)
    (hi.const_mul C)
  · intro n
    filter_upwards [] with p
    change ‖ψ p*initialApproximation ((n:ℝ)+1) f p‖ ≤ C*f p
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg
      ((initialApproximation_bounds (by positivity : 0 ≤ (n:ℝ)+1) f p).1)]
    exact (mul_le_mul_of_nonneg_left (initialApproximation_le hf p) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (hC p) (hf p))
  · filter_upwards [] with p
    apply tendsto_const_nhds.congr'
    filter_upwards [initialApproximation_sequence_eventually_eq hf p] with n hn
    change ψ p*f p = ψ p*initialApproximation ((n:ℝ)+1) f p
    rw [hn]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Measurability and pointwise stability of the common collision multiplier -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem rateMultiplier_measurable (N : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (rateMultiplier N f) := by
  unfold rateMultiplier attenuation rateSum scatterLeft scatterRight normalComponent
  fun_prop

omit [MeasurableSpace X] in
theorem rateMultiplier_pos {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    0 < rateMultiplier N f z := by
  unfold rateMultiplier attenuation
  apply div_pos (sq_pos_of_pos hN)
  exact sq_pos_of_pos (add_pos_of_pos_of_nonneg hN (rateSum_nonneg (hf _) (hf _) (hf _) (hf _)))

omit [MeasurableSpace X] in
theorem rateMultiplier_tendsto {ι : Type*} {l : Filter ι} {N : ℝ} (hN : 0 < N)
    {F : ι → X × Velocity → ℝ} {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (hF : ∀ p, Tendsto (fun i => F i p) l (𝓝 (f p)))
    (z : (X × (Velocity × Velocity)) × Sphere) :
    Tendsto (fun i => rateMultiplier N (F i) z) l (𝓝 (rateMultiplier N f z)) := by
  have hs := (((hF (z.1.1,z.1.2.1)).add (hF (z.1.1,z.1.2.2))).add
    (hF (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))).add
    (hF (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
  have hn : N+rateSum (f (z.1.1,z.1.2.1)) (f (z.1.1,z.1.2.2))
      (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
      (f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)) ≠ 0 :=
    (add_pos_of_pos_of_nonneg hN (rateSum_nonneg (hf _) (hf _) (hf _) (hf _))).ne'
  exact tendsto_const_nhds.div ((tendsto_const_nhds.add hs).pow 2) (pow_ne_zero 2 hn)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The exact characteristic equation of the supported periodic approximants -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

def BoundedCutoffSolution.source (S : BoundedCutoffSolution N T f₀) (z : ℝ × Phase) : ℝ :=
  positiveSource N (fun p => S.density (z.1,p)) z.2

theorem BoundedCutoffSolution.source_measurable (S : BoundedCutoffSolution N T f₀) :
    Measurable S.source := by
  have he : S.source = kineticSource N S.density := by
    funext z
    exact (kineticSource_eq N S.density z).symm
  rw [he]
  exact kineticSource_measurable N S.measurable

theorem BoundedCutoffSolution.source_bounded (S : BoundedCutoffSolution N T f₀) (hN : 0 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |S.source z| ≤ C := by
  obtain ⟨B,hB⟩ := S.bounded
  have hB0 : 0 ≤ B := (S.nonnegative (0,0)).trans (hB (0,0))
  have hC : 0 ≤ gainBound N := by unfold gainBound; positivity
  have hL : 0 ≤ lossBound N := by unfold lossBound; positivity
  refine ⟨gainBound N+lossBound N*B,by positivity,?_⟩
  intro z
  have h := positiveSource_bounds hN
    (S.measurable.comp (measurable_const.prodMk measurable_id))
    (fun p => S.nonnegative (z.1,p)) (fun p => hB (z.1,p)) z.2
  exact (abs_of_nonneg h.1).trans_le h.2

theorem BoundedCutoffSolution.source_path_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (p : Phase) (t : ℝ) :
    IntervalIntegrable (fun r => S.source (r,TorusFlight.flight r p)) volume 0 t := by
  obtain ⟨C,_,hC⟩ := S.source_bounded hN
  apply (intervalIntegrable_const (c := C)).mono_fun'
  · exact (S.source_measurable.comp (measurable_id.prodMk
      (TorusFlight.measurable_flight.comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun r => by simpa only [Real.norm_eq_abs] using hC (r,TorusFlight.flight r p))

theorem BoundedCutoffSolution.along_eq_damped (S : BoundedCutoffSolution N T f₀)
    {t : ℝ} (ht : t ∈ Icc 0 T) (p : Phase) :
    S.density (t,TorusFlight.flight t p) = TransportPrimitive.damped (lossBound N) (f₀ p)
      (fun r => S.source (r,TorusFlight.flight r p)) t := by
  rw [S.mild,TransportPrimitive.damped_eq]
  change PositiveIntegral.value T (lossBound N) TorusFlight.flight f₀ S.source
    (t,TorusFlight.flight t p) = _
  unfold PositiveIntegral.value
  have htt : PositiveIntegral.time T t = t := by
    unfold PositiveIntegral.time
    rw [min_eq_right ht.2,max_eq_right ht.1]
  rw [htt,TorusFlight.flight_neg]
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [TorusFlight.flight_add,sub_add_cancel]

theorem BoundedCutoffSolution.tested_path (S : BoundedCutoffSolution N T f₀) (hN : 0 < N)
    {t : ℝ} (ht : t ∈ Icc 0 T) (p : Phase) (χ χ' : ℝ → ℝ)
    (hc : ContinuousOn χ (Icc 0 t)) (hc' : ContinuousOn χ' (Icc 0 t))
    (hd : ∀ r ∈ Icc 0 t, HasDerivAt χ (χ' r) r) :
    (∫ r in 0..t, χ' r*S.density (r,TorusFlight.flight r p)+
      χ r*(S.source (r,TorusFlight.flight r p)-lossBound N*S.density (r,TorusFlight.flight r p))) =
      χ t*S.density (t,TorusFlight.flight t p)-χ 0*f₀ p := by
  have h := TransportPrimitive.damped_integration_by_parts (L := lossBound N) (c := f₀ p) ht.1
    (S.source_path_integrable hN p t) hc hc' hd
  rw [← S.along_eq_damped ht p] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro r hr
  have hrT : r ∈ Icc 0 T := by
    rw [uIcc_of_le ht.1] at hr
    exact ⟨hr.1,hr.2.trans ht.2⟩
  dsimp only
  rw [S.along_eq_damped hrT p]

theorem BoundedCutoffSolution.characteristic_integral (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 T) (p : Phase) :
    S.density (t,TorusFlight.flight t p) = f₀ p+
      ∫ r in 0..t, S.source (r,TorusFlight.flight r p)-lossBound N*S.density (r,TorusFlight.flight r p) := by
  have h := S.tested_path hN ht p (fun _ => 1) (fun _ => 0) continuousOn_const continuousOn_const
    (fun r _ => hasDerivAt_const r (1:ℝ))
  simp only [zero_mul,zero_add,one_mul] at h
  linarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # An entropy-production bound for nonnegative approximate densities -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem collisionOperator_test_integrable {μ : Measure X} [IsFiniteMeasure μ]
    {N C : ℝ} (hN : 0 < N) {f ψ : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hψm : Measurable ψ)
    (hψ : ∀ p, ‖p.2‖ ≤ N → |ψ p| ≤ C) :
    Integrable (fun p => ψ p*collisionOperator N f p) (μ.prod volume) := by
  obtain ⟨hg,hl,_,_⟩ := regularized_test_marginals (μ := μ) hN hfm hf hψm hψ
  convert hg.sub hl using 1
  funext p
  simp only [collisionOperator,mul_sub,Pi.sub_apply]

theorem nonnegative_entropy_production_bound {μ : Measure X} [IsFiniteMeasure μ]
    {N B δ : ℝ} (hN : 0 < N) (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ B) :
    (∫ p, Real.log (gaussianShift δ f p/maxwellian p.2)*collisionOperator N f p ∂μ.prod volume) ≤
      entropyErrorCoefficient μ N*δ*(|Real.log δ|+logRegularizationConstant N B) := by
  let g := gaussianShift δ f
  let ψ := fun p : X × Velocity => Real.log (g p/maxwellian p.2)
  have hgm : Measurable g := gaussianShift_measurable δ hfm
  have hgp : ∀ p, 0 < g p := gaussianShift_pos hδ hf
  have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hψm : Measurable ψ := (hgm.div hm).log
  have hψ : ∀ p, ‖p.2‖ ≤ N → |ψ p| ≤ |Real.log δ|+logRegularizationConstant N B :=
    fun p hp => log_regularization_bound hN.le hB hδ hδ1 (hf p) (hfb p) p.2 hp
  have hif := collisionOperator_test_integrable (μ := μ) hN hfm hf hψm hψ
  have hig := collisionOperator_test_integrable (μ := μ) hN hgm (fun p => (hgp p).le) hψm hψ
  obtain ⟨hg,hl,_,_⟩ := regularized_test_marginals (μ := μ) hN hgm (fun p => (hgp p).le) hψm hψ
  have hn := regularized_relative_entropy_nonpositive (μ := μ) hN hgm hgp hψ
  rw [← integral_sub hg hl] at hn
  simp only [← mul_sub] at hn
  have he := entropy_error_integral (μ := μ) hN hB hδ hδ1 hfm hf hfb
  have heq : (fun p => ψ p*(collisionOperator N f p-collisionOperator N g p)) =
      (fun p => ψ p*collisionOperator N f p)-(fun p => ψ p*collisionOperator N g p) := by
    funext p
    simp only [Pi.sub_apply,mul_sub]
  change |∫ p, ψ p*(collisionOperator N f p-collisionOperator N g p) ∂μ.prod volume| ≤ _ at he
  rw [heq,integral_sub' hif hig] at he
  change (∫ p, ψ p*collisionOperator N g p ∂μ.prod volume) ≤ 0 at hn
  have ha := (le_abs_self ((∫ p, ψ p*collisionOperator N f p ∂μ.prod volume)-
    (∫ p, ψ p*collisionOperator N g p ∂μ.prod volume))).trans he
  change (∫ p, ψ p*collisionOperator N f p ∂μ.prod volume) ≤ _
  linarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The entropy chain rule for the actual supported cutoff solution -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.collision_path_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (p : Phase) (t : ℝ) :
    IntervalIntegrable (fun r => S.source (r,TorusFlight.flight r p)-
      lossBound N*S.density (r,TorusFlight.flight r p)) volume 0 t := by
  obtain ⟨B,hB⟩ := S.bounded
  have hi : IntervalIntegrable (fun r => S.density (r,TorusFlight.flight r p)) volume 0 t := by
    apply (intervalIntegrable_const (c := B)).mono_fun'
    · exact (S.measurable.comp (measurable_id.prodMk
        (TorusFlight.measurable_flight.comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
    · filter_upwards [] with r
      rw [Real.norm_of_nonneg (S.nonnegative _)]
      exact hB _
  exact (S.source_path_integrable hN p t).sub (hi.const_mul (lossBound N))

theorem BoundedCutoffSolution.entropy_path_balance (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {t δ : ℝ} (ht : t ∈ Icc 0 T) (hδ : 0 < δ) (p : Phase) :
    (∫ r in 0..t, Real.log ((S.density (r,TorusFlight.flight r p)+δ*maxwellian p.2)/maxwellian p.2)*
      (S.source (r,TorusFlight.flight r p)-lossBound N*S.density (r,TorusFlight.flight r p))) =
      regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,TorusFlight.flight t p))-
      regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p) := by
  obtain ⟨B,hB⟩ := S.bounded
  have hB0 : 0 ≤ B := (S.nonnegative (0,0)).trans (hB (0,0))
  have he (r : ℝ) (hr : r ∈ uIcc 0 t) :
      f₀ p+(∫ s in 0..r, S.source (s,TorusFlight.flight s p)-
        lossBound N*S.density (s,TorusFlight.flight s p)) = S.density (r,TorusFlight.flight r p) := by
    rw [uIcc_of_le ht.1] at hr
    exact (S.characteristic_integral hN ⟨hr.1,hr.2.trans ht.2⟩ p).symm
  have h := regularizedEntropy_integral_path (maxwellian_pos p.2) (maxwellian_pos p.2) hδ hB0
    (S.collision_path_integrable hN p t)
    (fun r hr => (he r hr).symm ▸ S.nonnegative (r,TorusFlight.flight r p))
    (fun r hr => (he r hr).symm ▸ hB (r,TorusFlight.flight r p))
  rw [he t right_mem_uIcc] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [he r hr]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Retaining the nonnegative dissipation in the approximate entropy identity -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def positiveProduction (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  (1/4:ℝ)*collisionJump (fun p => Real.log (f p/maxwellian p.2)) z*
    (regularizedPostRate N f z-regularizedPreRate N f z)

omit [MeasurableSpace X] in
theorem positiveProduction_nonneg (N : ℝ) (f : X × Velocity → ℝ)
    (hf : ∀ p, 0 < f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ positiveProduction N f z := by
  simpa only [positiveProduction,mul_assoc] using
    mul_nonneg (by norm_num : (0:ℝ) ≤ 1/4) (regularized_relative_production_nonneg N f hf z)

theorem positiveProduction_identity {μ : Measure X} [IsFiniteMeasure μ]
    {N C : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hf : ∀ p, 0 < f p)
    (hlog : ∀ p, ‖p.2‖ ≤ N → |Real.log (f p/maxwellian p.2)| ≤ C) :
    Integrable (positiveProduction N f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ∧
    (∫ p, Real.log (f p/maxwellian p.2)*collisionOperator N f p ∂μ.prod volume) =
      -(∫ z, positiveProduction N f z ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hψ := (hfm.div hm).log
  have hpre := regularizedPreRate_test_integrable (μ := μ) hN hfm (fun p => (hf p).le) hψ hlog
  have hpost := regularizedPostRate_test_integrable (μ := μ) hN hfm (fun p => (hf p).le) hψ hlog
  obtain ⟨hjpre,hjpost⟩ := collisionJump_integrable N f (fun p => Real.log (f p/maxwellian p.2)) hpre hpost
  obtain ⟨hg,hl,hgEq,hlEq⟩ := regularized_test_marginals (μ := μ) hN hfm (fun p => (hf p).le) hψ hlog
  simp only [Pi.div_apply] at hg hl hgEq hlEq
  constructor
  · convert (hjpost.sub hjpre).const_mul (1/4:ℝ) using 1
    funext z
    simp only [positiveProduction,Pi.sub_apply]
    ring
  · simp_rw [collisionOperator,mul_sub]
    rw [integral_sub hg hl,hgEq,hlEq,
      regularized_production_identity N f (fun p => Real.log (f p/maxwellian p.2)) hpre hpost]
    simp only [positiveProduction,mul_assoc,integral_const_mul]
    ring

theorem gaussian_entropy_dissipation_bound {μ : Measure X} [IsFiniteMeasure μ]
    {N B δ : ℝ} (hN : 0 < N) (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ B) :
    (∫ p, Real.log (gaussianShift δ f p/maxwellian p.2)*collisionOperator N f p ∂μ.prod volume)+
      (∫ z, positiveProduction N (gaussianShift δ f) z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤
      entropyErrorCoefficient μ N*δ*(|Real.log δ|+logRegularizationConstant N B) := by
  let g := gaussianShift δ f
  let ψ := fun p : X × Velocity => Real.log (g p/maxwellian p.2)
  have hgm : Measurable g := gaussianShift_measurable δ hfm
  have hgp : ∀ p, 0 < g p := gaussianShift_pos hδ hf
  have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hψm : Measurable ψ := (hgm.div hm).log
  have hψ : ∀ p, ‖p.2‖ ≤ N → |ψ p| ≤ |Real.log δ|+logRegularizationConstant N B :=
    fun p hp => log_regularization_bound hN.le hB hδ hδ1 (hf p) (hfb p) p.2 hp
  have hif := collisionOperator_test_integrable (μ := μ) hN hfm hf hψm hψ
  have hig := collisionOperator_test_integrable (μ := μ) hN hgm (fun p => (hgp p).le) hψm hψ
  have hid := (positiveProduction_identity (μ := μ) hN hgm hgp hψ).2
  have he := entropy_error_integral (μ := μ) hN hB hδ hδ1 hfm hf hfb
  have heq : (fun p => ψ p*(collisionOperator N f p-collisionOperator N g p)) =
      (fun p => ψ p*collisionOperator N f p)-(fun p => ψ p*collisionOperator N g p) := by
    funext p
    simp only [Pi.sub_apply,mul_sub]
  change |∫ p, ψ p*(collisionOperator N f p-collisionOperator N g p) ∂μ.prod volume| ≤ _ at he
  rw [heq,integral_sub' hif hig,hid] at he
  simp only [sub_neg_eq_add] at he
  exact (le_abs_self _).trans he

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Renormalized characteristics of the actual periodic approximants -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.renormalized_path_balance (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 T) (β : Renormalization) (p : Phase) :
    (∫ r in 0..t, derivWithin β.toFun (Ici 0)
      (S.density (r,TorusFlight.flight r p)/maxwellian p.2)*
      (S.source (r,TorusFlight.flight r p)-lossBound N*S.density (r,TorusFlight.flight r p))) =
      maxwellian p.2*β.toFun (S.density (t,TorusFlight.flight t p)/maxwellian p.2)-
      maxwellian p.2*β.toFun (f₀ p/maxwellian p.2) := by
  have he (r : ℝ) (hr : r ∈ Icc 0 t) :
      f₀ p+(∫ s in 0..r, S.source (s,TorusFlight.flight s p)-
        lossBound N*S.density (s,TorusFlight.flight s p)) = S.density (r,TorusFlight.flight r p) :=
    (S.characteristic_integral hN ⟨hr.1,hr.2.trans ht.2⟩ p).symm
  have h := β.weighted_integral_path ht.1 (maxwellian_pos p.2)
    (S.collision_path_integrable hN p t)
    (fun r hr => (he r hr).symm ▸ S.nonnegative (r,TorusFlight.flight r p))
  rw [he t ⟨ht.1,le_rfl⟩] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [he r (by simpa only [uIcc_of_le ht.1] using hr)]

theorem BoundedCutoffSolution.renormalized_tested_path (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 T) (β : Renormalization) (φ : KineticTest) (p : Phase) :
    (∫ r in 0..t,
      derivWithin β.toFun (Ici 0) (S.density (r,TorusFlight.flight r p)/maxwellian p.2)*
        (S.source (r,TorusFlight.flight r p)-lossBound N*S.density (r,TorusFlight.flight r p))*
        φ.toFun r (TorusFlight.flight r p).1 p.2+
      maxwellian p.2*β.toFun (S.density (r,TorusFlight.flight r p)/maxwellian p.2)*
        φ.transportDerivative r (TorusFlight.flight r p)) =
      maxwellian p.2*β.toFun (S.density (t,TorusFlight.flight t p)/maxwellian p.2)*
        φ.toFun t (TorusFlight.flight t p).1 p.2-
      maxwellian p.2*β.toFun (f₀ p/maxwellian p.2)*φ.toFun 0 p.1 p.2 := by
  have he (r : ℝ) (hr : r ∈ Icc 0 t) :
      f₀ p+(∫ s in 0..r, S.source (s,TorusFlight.flight s p)-
        lossBound N*S.density (s,TorusFlight.flight s p)) = S.density (r,TorusFlight.flight r p) :=
    (S.characteristic_integral hN ⟨hr.1,hr.2.trans ht.2⟩ p).symm
  have hφ : AbsolutelyContinuousOnInterval
      (fun r => φ.toFun r (TorusFlight.flight r p).1 p.2) 0 t :=
    ((φ.contDiff_along p).of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hφ' : ∀ᵐ r, r ∈ Icc 0 t → HasDerivAt
      (fun r => φ.toFun r (TorusFlight.flight r p).1 p.2)
      (φ.transportDerivative r (TorusFlight.flight r p)) r :=
    ae_of_all _ (fun r _ => φ.hasDerivAt_along p r)
  have h := β.weighted_tested_integral_path ht.1 (maxwellian_pos p.2)
    (S.collision_path_integrable hN p t)
    (fun r hr => (he r hr).symm ▸ S.nonnegative (r,TorusFlight.flight r p)) hφ hφ'
  rw [he t ⟨ht.1,le_rfl⟩,TorusFlight.flight_zero] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [he r (by simpa only [uIcc_of_le ht.1] using hr)]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The extended dissipation of the actual symmetric regularization -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def extendedProduction (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ≥0∞ :=
  ENNReal.ofReal (windowKernel N z*rateMultiplier N f z)*extendedEntropyProduction
    (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
    (f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2))

def extendedDissipation (μ : Measure X) (N : ℝ) (f : X × Velocity → ℝ) : ℝ≥0∞ :=
  (4:ℝ≥0∞)⁻¹*∫⁻ z, extendedProduction N f z
    ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea

omit [MeasurableSpace X] in
theorem positiveProduction_formula (N : ℝ) (f : X × Velocity → ℝ) (hf : ∀ p, 0 < f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    positiveProduction N f z = (1/4:ℝ)*(windowKernel N z*rateMultiplier N f z)*
      ((f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)-
        f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2))*
        Real.log ((f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))/
          (f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)))) := by
  unfold positiveProduction
  rw [collisionJump_log_relative f hf,collisionJump_log_density f hf,
    regularizedPostRate_factor,regularizedPreRate_factor]
  ring

omit [MeasurableSpace X] in
theorem ofReal_positiveProduction {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (hf : ∀ p, 0 < f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    ENNReal.ofReal (positiveProduction N f z) = (4:ℝ≥0∞)⁻¹*extendedProduction N f z := by
  have hA := mul_pos (hf (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (hf (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
  have hB := mul_pos (hf (z.1.1,z.1.2.1)) (hf (z.1.1,z.1.2.2))
  have hw : 0 ≤ windowKernel N z*rateMultiplier N f z :=
    mul_nonneg (windowKernel_bounds hN z).1 (attenuation_nonneg _ _)
  rw [positiveProduction_formula N f hf]
  unfold extendedProduction
  simp only [extendedEntropyProduction,hA,hB,hA.ne',hB.ne',and_self,ite_true,ite_false]
  rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hw),ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/4)]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4)]
  norm_num [mul_assoc]

theorem ofReal_integral_positiveProduction {μ : Measure X} {N : ℝ} (hN : 0 ≤ N)
    (f : X × Velocity → ℝ) (hf : ∀ p, 0 < f p)
    (hi : Integrable (positiveProduction N f)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    ENNReal.ofReal (∫ z, positiveProduction N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) = extendedDissipation μ N f := by
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (positiveProduction_nonneg N f hf))]
  simp_rw [ofReal_positiveProduction hN f hf]
  exact lintegral_const_mul' _ _ (by norm_num)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual regularized collision rates have a vanishing entropy tail -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

def normalizedRateExcess (N R : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  regularizedPostRate N f z/(1+f (z.1.1,z.1.2.1)/maxwellian z.1.2.1)-
    R*(regularizedPreRate N f z/(1+f (z.1.1,z.1.2.1)/maxwellian z.1.2.1))

theorem normalizedRateExcess_measurable (N R : ℝ) {f : X × Velocity → ℝ} (hfm : Measurable f) :
    Measurable (normalizedRateExcess N R f) := by
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere => maxwellian z.1.2.1) := by
    unfold maxwellian
    fun_prop
  have hd : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      1+f (z.1.1,z.1.2.1)/maxwellian z.1.2.1) :=
    measurable_const.add ((hfm.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst)).div hm)
  exact ((regularizedPostRate_measurable N hfm).div hd).sub
    (((regularizedPreRate_measurable N hfm).div hd).const_mul R)

omit [MeasurableSpace X] in
theorem normalizedRateExcess_bound {N R : ℝ} (hN : 0 < N) (hR : 2 ≤ R)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    ENNReal.ofReal (normalizedRateExcess N R f z) ≤
      ENNReal.ofReal (2/Real.log R)*extendedProduction N f z := by
  let d := 1+f (z.1.1,z.1.2.1)/maxwellian z.1.2.1
  have hd : 1 ≤ d := le_add_of_nonneg_right (div_nonneg (hf _) (maxwellian_pos _).le)
  have hdp : 0 < d := zero_lt_one.trans_le hd
  have hθ : 0 ≤ d⁻¹ := inv_nonneg.mpr hdp.le
  have hθ1 : d⁻¹ ≤ 1 := (inv_le_one₀ hdp).mpr hd
  have h := gain_excess_le_extendedProduction
    (mul_nonneg (hf (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
      (hf (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)))
    (mul_nonneg (hf (z.1.1,z.1.2.1)) (hf (z.1.1,z.1.2.2)))
    (mul_nonneg (windowKernel_bounds hN.le z).1 (rateMultiplier_bounds hN hf z).1) hθ hθ1 hR
  change ENNReal.ofReal ((windowKernel N z*rateMultiplier N f z)*d⁻¹*
    (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))-
    R*((windowKernel N z*rateMultiplier N f z)*d⁻¹*(f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)))) ≤ _ at h
  convert h using 1
  · congr 1
    rw [normalizedRateExcess,regularizedPostRate_factor,regularizedPreRate_factor]
    dsimp only [d]
    ring
  · simp only [extendedProduction,mul_assoc]

theorem normalizedRateExcess_integral_bound {μ : Measure X} {N R : ℝ}
    (hN : 0 < N) (hR : 2 ≤ R) {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) :
    (∫⁻ z, ENNReal.ofReal (normalizedRateExcess N R f z)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤
        ENNReal.ofReal (2/Real.log R)*(4*extendedDissipation μ N f) := by
  have hD : 4*extendedDissipation μ N f =
      ∫⁻ z, extendedProduction N f z ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
    rw [extendedDissipation,← mul_assoc,ENNReal.mul_inv_cancel (by norm_num) (by norm_num),one_mul]
  rw [hD]
  exact (lintegral_mono (normalizedRateExcess_bound hN hR hf)).trans_eq
    (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Gaussian removal for the extended regularized collision dissipation -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem gaussianShift_tendsto (f : X × Velocity → ℝ) (p : X × Velocity) :
    Tendsto (fun δ : ℝ => gaussianShift δ f p) (𝓝[>] 0) (𝓝 (f p)) := by
  have hc : Continuous (fun δ : ℝ => f p+δ*maxwellian p.2) :=
    continuous_const.add (continuous_id.mul_const _)
  simpa only [gaussianShift,zero_mul,add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem extendedDissipation_gaussian_le_liminf (μ : Measure X) {N : ℝ} (hN : 0 < N)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    extendedDissipation μ N f ≤
      liminf (fun δ : ℝ => extendedDissipation μ N (gaussianShift δ f)) (𝓝[>] 0) := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  let A := fun z : (X × (Velocity × Velocity)) × Sphere =>
    f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)
  let B := fun z : (X × (Velocity × Velocity)) × Sphere => f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)
  let a := fun (δ : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) =>
    gaussianShift δ f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*
      gaussianShift δ f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)
  let b := fun (δ : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) =>
    gaussianShift δ f (z.1.1,z.1.2.1)*gaussianShift δ f (z.1.1,z.1.2.2)
  let W := fun z : (X × (Velocity × Velocity)) × Sphere =>
    ENNReal.ofReal (windowKernel N z*rateMultiplier N f z)
  let w := fun (δ : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) =>
    ENNReal.ofReal (windowKernel N z*rateMultiplier N (gaussianShift δ f) z)
  have hbm (δ : ℝ) : Measurable (b δ) :=
    ((gaussianShift_measurable δ hfm).comp (measurable_fst.fst.prodMk measurable_fst.snd.fst)).mul
      ((gaussianShift_measurable δ hfm).comp (measurable_fst.fst.prodMk measurable_fst.snd.snd))
  have ham (δ : ℝ) : Measurable (a δ) := (hbm δ).comp scatterTriple_measurable
  have hwm (δ : ℝ) : Measurable (w δ) :=
    ((windowKernel_measurable N).mul (rateMultiplier_measurable N (gaussianShift_measurable δ hfm))).ennreal_ofReal
  have hprod := lintegral_varying_production_le_liminf (μ := ν) (l := 𝓝[>] (0:ℝ))
    ham hbm hwm (A := A) (B := B) (W := W)
    (Filter.Eventually.of_forall (fun _ => mul_nonneg (hf _) (hf _)))
    (Filter.Eventually.of_forall (fun _ => mul_nonneg (hf _) (hf _)))
    (Filter.Eventually.of_forall (fun _ => ⟨(gaussianShift_tendsto f _).mul (gaussianShift_tendsto f _),
      (gaussianShift_tendsto f _).mul (gaussianShift_tendsto f _)⟩))
    (Filter.Eventually.of_forall (fun z => ENNReal.tendsto_ofReal
      ((rateMultiplier_tendsto hN hf (gaussianShift_tendsto f) z).const_mul (windowKernel N z)))) (by
      filter_upwards [] with z
      have hp (p : X × Velocity) : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < gaussianShift δ f p := by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact gaussianShift_pos hδ hf p
      exact ⟨((hp _).and (hp _)).mono (fun _ h => mul_pos h.1 h.2),
        ((hp _).and (hp _)).mono (fun _ h => mul_pos h.1 h.2)⟩)
  have hi : (∫⁻ z, extendedProduction N f z ∂ν) ≤
      liminf (fun δ : ℝ => ∫⁻ z, extendedProduction N (gaussianShift δ f) z ∂ν) (𝓝[>] 0) := hprod
  have hm := ENNReal.le_liminf_mul (u := fun _ : ℝ => (4:ℝ≥0∞)⁻¹)
    (v := fun δ => ∫⁻ z, extendedProduction N (gaussianShift δ f) z ∂ν) (f := 𝓝[>] (0:ℝ))
  change (4:ℝ≥0∞)⁻¹*(∫⁻ z, extendedProduction N f z ∂ν) ≤
    liminf (fun δ : ℝ => (4:ℝ≥0∞)⁻¹*∫⁻ z, extendedProduction N (gaussianShift δ f) z ∂ν) (𝓝[>] 0)
  exact (mul_le_mul_right hi (4:ℝ≥0∞)⁻¹).trans (by
    simpa only [liminf_const,Pi.mul_def] using hm)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integrability of both normalized regularized rates before angular averaging -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def normalizer (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ := 1+f p/maxwellian p.2

theorem normalizer_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (normalizer f) := by
  have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  exact measurable_const.add (hf.div hm)

omit [MeasurableSpace X] in
theorem normalizer_ge_one {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    1 ≤ normalizer f p := le_add_of_nonneg_right (div_nonneg (hf p) (maxwellian_pos p.2).le)

omit [MeasurableSpace X] in
theorem normalizer_pos {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 < normalizer f p := zero_lt_one.trans_le (normalizer_ge_one hf p)

theorem normalizedRates_integrable {μ : Measure X} [IsFiniteMeasure μ] {N : ℝ} (hN : 0 < N)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    Integrable (fun z => regularizedPostRate N f z/normalizer f (z.1.1,z.1.2.1))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ∧
    Integrable (fun z => regularizedPreRate N f z/normalizer f (z.1.1,z.1.2.1))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  let ψ : X × Velocity → ℝ := fun p => (normalizer f p)⁻¹
  have hm : Measurable ψ := (normalizer_measurable hfm).inv
  have hb (p : X × Velocity) (_hp : ‖p.2‖ ≤ N) : |ψ p| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (normalizer_pos hf p).le)]
    exact (inv_le_one₀ (normalizer_pos hf p)).mpr (normalizer_ge_one hf p)
  have hpost := regularizedPostRate_test_integrable (μ := μ) hN hfm hf hm hb
  have hpre := regularizedPreRate_test_integrable (μ := μ) hN hfm hf hm hb
  constructor
  · convert hpost using 1
    funext z
    dsimp only [ψ]
    ring
  · convert hpre using 1
    funext z
    dsimp only [ψ]
    ring

theorem normalizedRateExcess_integrable {μ : Measure X} [IsFiniteMeasure μ] {N R : ℝ}
    (hN : 0 < N) {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    Integrable (normalizedRateExcess N R f)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) :=
  (normalizedRates_integrable hN hfm hf).1.sub ((normalizedRates_integrable hN hfm hf).2.const_mul R)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Entropy control of the actual angularly averaged normalized gain tail -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
variable {X : Type*} [MeasurableSpace X]

def normalizedGainExcess (N R : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  gain N f p/normalizer f p-R*(loss N f p/normalizer f p)

theorem normalizedRateExcess_marginal_ae {μ : Measure X} [IsFiniteMeasure μ] {N R : ℝ}
    (hN : 0 < N) {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    (fun p => ∫ q : Velocity × Sphere, normalizedRateExcess N R f (collisionGrouping.symm (p,q))
      ∂((volume : Measure Velocity).prod sphereArea)) =ᵐ[μ.prod volume] normalizedGainExcess N R f := by
  have hI := normalizedRates_integrable (μ := μ) hN hfm hf
  have hP := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable hI.1
  have hL := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable hI.2
  filter_upwards [hP.prod_right_ae,hL.prod_right_ae] with p hp hl
  change Integrable (fun q : Velocity × Sphere =>
    regularizedPostRate N f (collisionGrouping.symm (p,q))/normalizer f p) _ at hp
  change Integrable (fun q : Velocity × Sphere =>
    regularizedPreRate N f (collisionGrouping.symm (p,q))/normalizer f p) _ at hl
  change (∫ q : Velocity × Sphere,
    regularizedPostRate N f (collisionGrouping.symm (p,q))/normalizer f p-
      R*(regularizedPreRate N f (collisionGrouping.symm (p,q))/normalizer f p)
      ∂((volume : Measure Velocity).prod sphereArea)) = _
  rw [integral_sub hp (hl.const_mul R),integral_const_mul,integral_div,integral_div,
    ← gain_eq_full_integral hN.le f p,← loss_eq_full_integral hN.le f p]
  rfl

theorem normalizedGainExcess_integral_bound {μ : Measure X} [IsFiniteMeasure μ] {N R : ℝ}
    (hN : 0 < N) (hR : 2 ≤ R) {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    (∫⁻ p, ENNReal.ofReal (normalizedGainExcess N R f p) ∂μ.prod volume) ≤
      ENNReal.ofReal (2/Real.log R)*(4*extendedDissipation μ N f) := by
  have hm := (normalizedRateExcess_measurable N R hfm).comp collisionGrouping.symm.measurable
  have hi := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    (normalizedRateExcess_integrable (R := R) hN hfm hf)
  have hae := normalizedRateExcess_marginal_ae (μ := μ) (R := R) hN hfm hf
  calc
    _ = ∫⁻ p, ENNReal.ofReal (∫ q : Velocity × Sphere,
        normalizedRateExcess N R f (collisionGrouping.symm (p,q))
        ∂((volume : Measure Velocity).prod sphereArea)) ∂μ.prod volume :=
      lintegral_congr_ae (hae.symm.mono (fun _ h => congrArg ENNReal.ofReal h))
    _ ≤ ∫⁻ z, ENNReal.ofReal (normalizedRateExcess N R f (collisionGrouping.symm z))
        ∂(μ.prod volume).prod ((volume : Measure Velocity).prod sphereArea) :=
      positive_marginal_bound hm hi
    _ = ∫⁻ z, ENNReal.ofReal (normalizedRateExcess N R f z)
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea :=
      (collisionGrouping_measurePreserving μ).symm.lintegral_comp
        (normalizedRateExcess_measurable N R hfm).ennreal_ofReal
    _ ≤ _ := normalizedRateExcess_integral_bound hN hR hf

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Initial mass and momentum pass through the actual truncations -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem initialApproximation_linear_moment_tendsto {f : Density}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) (D : ℝ≥0)
    (hD : ∀ v, |ψ v| ≤ D*(1+‖v‖)) :
    Tendsto (fun n : ℕ => ∫ p : Phase, ψ p.2*initialApproximation ((n:ℝ)+1) f p)
      atTop (𝓝 (∫ p : Phase, ψ p.2*f p)) := by
  have hli : Integrable (linearMoment f) := linearMoment_integrable hfm hf hi
  apply tendsto_integral_of_dominated_convergence
    (fun p => (D:ℝ)*linearMoment f p)
    (fun n => ((hψ.comp measurable_snd).mul
      (initialApproximation_measurable ((n:ℝ)+1) hfm)).aestronglyMeasurable)
    (hli.const_mul (D:ℝ))
  · intro n
    filter_upwards [] with p
    change ‖ψ p.2*initialApproximation ((n:ℝ)+1) f p‖ ≤ (D:ℝ)*linearMoment f p
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg
      ((initialApproximation_bounds (by positivity : 0 ≤ (n:ℝ)+1) f p).1)]
    calc
      _ ≤ |ψ p.2| *f p := mul_le_mul_of_nonneg_left (initialApproximation_le hf p) (abs_nonneg _)
      _ ≤ (D:ℝ)*(1+‖p.2‖)*f p := mul_le_mul_of_nonneg_right (hD p.2) (hf p)
      _ = _ := by simp only [linearMoment, mul_assoc]
  · filter_upwards [] with p
    apply tendsto_const_nhds.congr'
    filter_upwards [initialApproximation_sequence_eventually_eq hf p] with n hn
    change ψ p.2*f p = ψ p.2*initialApproximation ((n:ℝ)+1) f p
    rw [hn]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Relative entropy of the actual initial truncations converges to the datum -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem initialApproximation_relativeEntropy_tendsto {f : Density}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    Tendsto (fun n : ℕ => relativeEntropy (initialApproximation ((n:ℝ)+1) f))
      atTop (𝓝 (relativeEntropy f)) := by
  have hm : Measurable (fun p : Phase => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hmajor := (hi.const_mul initialEntropyCoefficient).add integrable_maxwellian_phase
  have h := tendsto_integral_of_dominated_convergence
    (F := fun n p => scalarRelativeEntropy (maxwellian p.2) (initialApproximation ((n:ℝ)+1) f p))
    (f := fun p => scalarRelativeEntropy (maxwellian p.2) (f p))
    (fun p => initialEntropyCoefficient*entropyMoment f p+maxwellian p.2)
    (fun n => (scalarRelativeEntropy_measurable hm (initialApproximation_measurable ((n:ℝ)+1) hfm)).aestronglyMeasurable)
    hmajor (fun n => by
      filter_upwards [] with p
      have hn : 1 ≤ (n:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
      have hfn := fun p => (initialApproximation_bounds (zero_le_one.trans hn) f p).1
      rw [Real.norm_of_nonneg (scalarRelativeEntropy_nonneg (maxwellian_pos p.2) (hfn p))]
      exact (relativeEntropy_density_bound hfn p).trans
        (add_le_add (mul_le_mul_of_nonneg_left (initialApproximation_entropy_le hn hf p)
          initialEntropyCoefficient_nonneg) le_rfl)) (by
      filter_upwards [] with p
      apply tendsto_const_nhds.congr'
      filter_upwards [initialApproximation_sequence_eventually_eq hf p] with n hn
      rw [hn])
  simpa only [relativeEntropy,scalarRelativeEntropy_eq (maxwellian_pos _)] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
