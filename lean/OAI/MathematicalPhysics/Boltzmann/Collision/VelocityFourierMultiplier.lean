import OAI.MathematicalPhysics.Boltzmann.Branching.PublishedInputs
import OAI.MathematicalPhysics.Boltzmann.Collision.SphereIsometryMeasure
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.Topology.UniformSpace.Dini

namespace OAI

section

/-! # Nonconcentration of Lebesgue velocities on affine transport hyperplanes -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem inner_velocity_surjective {ξ : Velocity} (hξ : ξ ≠ 0) :
    Function.Surjective (innerSL ℝ ξ : Velocity →ₗ[ℝ] ℝ) := by
  intro y
  refine ⟨(y / inner ℝ ξ ξ) • ξ, ?_⟩
  have hn : inner ℝ ξ ξ ≠ 0 := (real_inner_self_pos.mpr hξ).ne'
  change inner ℝ ξ ((y / inner ℝ ξ ξ) • ξ) = y
  rw [real_inner_smul_right]
  exact div_mul_cancel₀ y hn

theorem affine_velocity_hyperplane_null (τ : ℝ) {ξ : Velocity} (hξ : ξ ≠ 0) :
    (volume : Measure Velocity) {v | τ + inner ℝ ξ v = 0} = 0 := by
  have ha : ∀ᵐ y : ℝ ∂volume, y ∈ ({-τ} : Set ℝ)ᶜ := by
    simpa only [mem_compl_iff,mem_singleton_iff] using volume.ae_ne (-τ)
  have h := (ae_comp_linearMap_mem_iff (innerSL ℝ ξ : Velocity →ₗ[ℝ] ℝ)
    (volume : Measure Velocity) (volume : Measure ℝ) (inner_velocity_surjective hξ)
    (measurableSet_singleton (-τ)).compl).mpr ha
  have hz : ∀ᵐ v : Velocity ∂volume, ¬(τ + inner ℝ ξ v = 0) := by
    filter_upwards [h] with v hv he
    apply hv
    change inner ℝ ξ v = -τ
    linarith
  simpa only [not_not] using ae_iff.mp hz

theorem evolution_velocity_hyperplane_null {τ : ℝ} {ξ : Velocity}
    (h : (τ,ξ) ≠ 0) : (volume : Measure Velocity) {v | τ + inner ℝ ξ v = 0} = 0 := by
  by_cases hξ : ξ = 0
  · have hτ : τ ≠ 0 := by
      intro he
      apply h
      simp [he,hξ]
    simp [hξ,hτ]
  · exact affine_velocity_hyperplane_null τ hξ

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Nonnegative polar integrals for the physical three-dimensional velocity space -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness

theorem lintegral_velocity_polar {F : Velocity → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, F x) = ∫⁻ n : Sphere, ∫⁻ r : Ioi (0:ℝ), F ((r:ℝ) • n.1)
      ∂Measure.volumeIoiPow 2 ∂sphereArea := by
  let H := homeomorphUnitSphereProd Velocity
  have hp := (volume : Measure Velocity).measurePreserving_homeomorphUnitSphereProd
  have hFm : Measurable (fun p : Sphere × Ioi (0:ℝ) => F ((p.2:ℝ) • p.1.1)) := by
    apply hF.comp
    fun_prop
  calc
    (∫⁻ x, F x) = ∫⁻ x : ({0}ᶜ : Set Velocity), F x ∂((volume : Measure Velocity).comap (↑)) := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl,restrict_compl_singleton]
    _ = ∫⁻ p : Sphere × Ioi (0:ℝ), F ((p.2:ℝ) • p.1.1)
        ∂sphereArea.prod (Measure.volumeIoiPow 2) := by
      have hh := hp.lintegral_comp_emb H.measurableEmbedding
        (fun p => F (H.symm p))
      simpa only [H,sphereArea,Homeomorph.symm_apply_apply,
        homeomorphUnitSphereProd_symm_apply_coe,finrank_euclideanSpace,
        Fintype.card_fin,Nat.reduceSub] using hh
    _ = _ := lintegral_prod _ hFm.aemeasurable

theorem radial_cubic_unit_integral :
    (∫⁻ r : Ioi (0:ℝ), if (r:ℝ) < 1 then ENNReal.ofReal ((r:ℝ)^3) else 0
      ∂Measure.volumeIoiPow 2) = (6:ℝ≥0∞)⁻¹ := by
  have hm : Measurable (fun r : Ioi (0:ℝ) => ENNReal.ofReal ((r:ℝ)^3)) := by fun_prop
  have hd : (Measure.volumeIoiPow 2).withDensity (fun r : Ioi (0:ℝ) => ENNReal.ofReal ((r:ℝ)^3)) =
      Measure.volumeIoiPow 5 := by
    unfold Measure.volumeIoiPow
    rw [← withDensity_mul _ (by fun_prop) hm]
    congr 1
    funext r
    change ENNReal.ofReal ((r:ℝ)^2)*ENNReal.ofReal ((r:ℝ)^3) = _
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hs : MeasurableSet {r : Ioi (0:ℝ) | (r:ℝ) < 1} := measurableSet_lt (by fun_prop) measurable_const
  change (∫⁻ r, ({r : Ioi (0:ℝ) | (r:ℝ) < 1}.indicator
    (fun r => ENNReal.ofReal ((r:ℝ)^3))) r ∂Measure.volumeIoiPow 2) = _
  rw [lintegral_indicator hs,← withDensity_apply _ hs,hd]
  change Measure.volumeIoiPow 5 (Iio (⟨1,by norm_num⟩ : Ioi (0:ℝ))) = _
  rw [Measure.volumeIoiPow_apply_Iio]
  norm_num only [Nat.reduceAdd,one_pow]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 6)]
  norm_num

end BoltzmannNonuniqueness

end

end

section

/-! # Decay and continuity of the localized transport multiplier -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

def velocityMultiplier (n : ℕ) (k : SpaceTime) (v : Velocity) : ℝ :=
  (1+((n : ℝ)*(k.1+inner ℝ k.2 v))^2)⁻¹

theorem velocityMultiplier_nonneg (n : ℕ) (k : SpaceTime) (v : Velocity) :
    0 ≤ velocityMultiplier n k v := by unfold velocityMultiplier; positivity

theorem velocityMultiplier_le_one (n : ℕ) (k : SpaceTime) (v : Velocity) :
    velocityMultiplier n k v ≤ 1 := by
  unfold velocityMultiplier
  exact (inv_le_one₀ (by positivity)).mpr (by nlinarith [sq_nonneg ((n:ℝ)*(k.1+inner ℝ k.2 v))])

theorem velocityMultiplier_continuous (n : ℕ) :
    Continuous (fun p : SpaceTime × Velocity => velocityMultiplier n p.1 p.2) := by
  unfold velocityMultiplier
  apply Continuous.inv₀
  · fun_prop
  · intro p
    positivity

theorem velocityMultiplier_antitone (k : SpaceTime) (v : Velocity) :
    Antitone (fun n => velocityMultiplier n k v) := by
  intro n m hnm
  unfold velocityMultiplier
  apply inv_anti₀ (by positivity)
  have hcast : (n : ℝ) ≤ m := by exact_mod_cast hnm
  rw [mul_pow,mul_pow]
  exact add_le_add_right (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Nat.cast_nonneg n) hcast 2) (sq_nonneg _)) _

theorem velocityMultiplier_tendsto {k : SpaceTime} {v : Velocity}
    (h : k.1+inner ℝ k.2 v ≠ 0) :
    Tendsto (fun n => velocityMultiplier n k v) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun n : ℕ => (n : ℝ)^2*(k.1+inner ℝ k.2 v)^2) atTop atTop :=
    hn.atTop_mul_const (sq_pos_of_ne_zero h)
  have hh : Tendsto (fun n : ℕ => 1+(n : ℝ)^2*(k.1+inner ℝ k.2 v)^2) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 hs
  simpa only [velocityMultiplier,mul_pow,Function.comp_def] using tendsto_inv_atTop_zero.comp hh

def velocityMultiplierMass (R : ℝ) (n : ℕ) (k : SpaceTime) : ℝ :=
  ∫ v in Metric.closedBall (0 : Velocity) R, velocityMultiplier n k v

theorem velocityMultiplier_integrable (R : ℝ) (n : ℕ) (k : SpaceTime) :
    IntegrableOn (velocityMultiplier n k) (Metric.closedBall (0 : Velocity) R) := by
  exact ((velocityMultiplier_continuous n).comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
    (isCompact_closedBall _ _)

theorem velocityMultiplierMass_nonneg (R : ℝ) (n : ℕ) (k : SpaceTime) :
    0 ≤ velocityMultiplierMass R n k :=
  integral_nonneg (velocityMultiplier_nonneg n k)

theorem velocityMultiplierMass_antitone (R : ℝ) (k : SpaceTime) :
    Antitone (fun n => velocityMultiplierMass R n k) := by
  intro n m hnm
  exact integral_mono (velocityMultiplier_integrable R m k)
    (velocityMultiplier_integrable R n k) (fun v => velocityMultiplier_antitone k v hnm)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Uniform decay of the transport multiplier on the unit frequency sphere -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem velocityMultiplierMass_continuous (R : ℝ) (n : ℕ) :
    Continuous (velocityMultiplierMass R n) := by
  have : IsFiniteMeasure ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Velocity) R).measure_lt_top.ne
  apply continuous_of_dominated (bound := fun _ : Velocity => (1 : ℝ))
  · intro k
    exact ((velocityMultiplier_continuous n).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro k
    exact ae_of_all _ (fun v => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (velocityMultiplier_nonneg n k v)] using
        velocityMultiplier_le_one n k v)
  · exact integrable_const 1
  · exact ae_of_all _ (fun v => (velocityMultiplier_continuous n).comp
      (continuous_id.prodMk continuous_const))

theorem velocityMultiplierMass_tendsto (R : ℝ) {k : SpaceTime} (hk : k ≠ 0) :
    Tendsto (fun n => velocityMultiplierMass R n k) atTop (𝓝 0) := by
  have : IsFiniteMeasure ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Velocity) R).measure_lt_top.ne
  have hz : ∀ᵐ v : Velocity ∂volume, k.1+inner ℝ k.2 v ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using evolution_velocity_hyperplane_null hk
  have hlim : ∀ᵐ v ∂volume.restrict (Metric.closedBall (0 : Velocity) R),
      Tendsto (fun n => velocityMultiplier n k v) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_of_ae hz] with v hv
    exact velocityMultiplier_tendsto hv
  have h := tendsto_integral_of_dominated_convergence (fun _ : Velocity => (1 : ℝ))
    (fun n => (velocityMultiplier_integrable R n k).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => ae_of_all _ (fun v => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (velocityMultiplier_nonneg n k v)] using
        velocityMultiplier_le_one n k v)) hlim
  simpa only [integral_zero,velocityMultiplierMass] using h

theorem velocityMultiplierMass_uniform_decay (R : ℝ) :
    TendstoUniformlyOn (velocityMultiplierMass R) (fun _ => 0) atTop
      (Metric.sphere (0 : SpaceTime) 1) := by
  apply Antitone.tendstoUniformlyOn_of_forall_tendsto (isCompact_sphere _ _)
  · intro n
    exact (velocityMultiplierMass_continuous R n).continuousOn
  · intro k _
    exact velocityMultiplierMass_antitone R k
  · exact continuousOn_const
  · intro k hk
    apply velocityMultiplierMass_tendsto R
    intro he
    have hn : ‖k‖ = 1 := mem_sphere_zero_iff_norm.mp hk
    rw [he,norm_zero] at hn
    norm_num at hn

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The localized multiplier mass is uniformly small outside a frequency ball -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

theorem velocityMultiplier_smul (a : ℝ) (n : ℕ) (k : SpaceTime) (v : Velocity) :
    velocityMultiplier n (a • k) v = (1+((n:ℝ)*a*(k.1+inner ℝ k.2 v))^2)⁻¹ := by
  simp only [velocityMultiplier,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,real_inner_smul_left]
  congr 2
  ring

theorem velocityMultiplier_large_scale {a : ℝ} {n : ℕ} (ha : (n:ℝ) ≤ a)
    (k : SpaceTime) (v : Velocity) :
    velocityMultiplier 1 (a • k) v ≤ velocityMultiplier n k v := by
  rw [velocityMultiplier_smul,velocityMultiplier]
  simp only [Nat.cast_one,one_mul]
  apply inv_anti₀ (by positivity)
  rw [mul_pow,mul_pow]
  exact add_le_add_right (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Nat.cast_nonneg n) ha 2) (sq_nonneg _)) _

theorem velocityMultiplierMass_large_scale (R : ℝ) {a : ℝ} {n : ℕ} (ha : (n:ℝ) ≤ a)
    (k : SpaceTime) : velocityMultiplierMass R 1 (a • k) ≤ velocityMultiplierMass R n k :=
  integral_mono (velocityMultiplier_integrable R 1 (a • k))
    (velocityMultiplier_integrable R n k) (velocityMultiplier_large_scale ha k)

theorem velocityMultiplierMass_high_frequency (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ k : SpaceTime, (N:ℝ) ≤ ‖k‖ → velocityMultiplierMass R 1 k < ε := by
  have hu := (Metric.tendstoUniformlyOn_iff.mp (velocityMultiplierMass_uniform_decay R)) ε hε
  rcases Filter.eventually_atTop.mp hu with ⟨n,hn⟩
  refine ⟨max n 1,by omega,?_⟩
  intro k hk
  have hkpos : 0 < ‖k‖ := lt_of_lt_of_le (by exact_mod_cast (show 0 < max n 1 by omega)) hk
  let e : SpaceTime := ‖k‖⁻¹ • k
  have he : e ∈ Metric.sphere (0 : SpaceTime) 1 := by
    rw [mem_sphere_zero_iff_norm]
    dsimp [e]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hkpos.ne']
  have heq : ‖k‖ • e = k := by
    dsimp [e]
    rw [smul_smul,mul_inv_cancel₀ hkpos.ne',one_smul]
  have hb := velocityMultiplierMass_large_scale R hk e
  rw [heq] at hb
  have hs := hn (max n 1) (le_max_left _ _) e he
  have hs' : velocityMultiplierMass R (max n 1) e < ε := by
    simpa only [Real.dist_eq,zero_sub,abs_neg,
      abs_of_nonneg (velocityMultiplierMass_nonneg R (max n 1) e)] using hs
  exact hb.trans_lt hs'

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The complex resolvent multiplier and its exact squared norm -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

def complexVelocityMultiplier (n : ℕ) (k : SpaceTime) (v : Velocity) : ℂ :=
  (1+Complex.I*(n : ℂ)*(k.1+inner ℝ k.2 v))⁻¹

theorem complexVelocityMultiplier_norm_sq (n : ℕ) (k : SpaceTime) (v : Velocity) :
    ‖complexVelocityMultiplier n k v‖^2 = velocityMultiplier n k v := by
  rw [complexVelocityMultiplier,norm_inv,inv_pow,Complex.sq_norm]
  simp [Complex.normSq_apply,velocityMultiplier]
  ring

theorem complexVelocityMultiplier_norm_le_one (n : ℕ) (k : SpaceTime) (v : Velocity) :
    ‖complexVelocityMultiplier n k v‖ ≤ 1 := by
  have h := velocityMultiplier_le_one n k v
  rw [← complexVelocityMultiplier_norm_sq] at h
  nlinarith [norm_nonneg (complexVelocityMultiplier n k v)]

theorem complexVelocityMultiplier_continuous (n : ℕ) :
    Continuous (fun p : SpaceTime × Velocity => complexVelocityMultiplier n p.1 p.2) := by
  unfold complexVelocityMultiplier
  apply Continuous.inv₀
  · fun_prop
  · intro p h
    have hr := congrArg Complex.re h
    norm_num at hr

end BoltzmannNonuniqueness.Published

end

end

end OAI
