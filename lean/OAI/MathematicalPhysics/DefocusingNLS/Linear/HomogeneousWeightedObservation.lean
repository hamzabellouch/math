import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousWeakObservation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Physical L² observation with an actual square-integrable coefficient

Multiplication by a fixed L² coefficient sends bounded weakly null data in
the faithful homogeneous space to zero in physical L². In particular this
applies to every smooth compactly supported part of a potential coefficient.
-/

open MeasureTheory Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousPhysical_point_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (f : HomogeneousY a k) (x : E) :
    ‖homogeneousPhysicalCLM a k ha ha1 hk f x‖ ≤
      ‖homogeneousPointEvaluation a k ha ha1 hk 0‖ * ‖f‖ := by
  calc
    _ ≤ ‖homogeneousPointEvaluation a k ha ha1 hk x‖ * ‖f‖ :=
      (homogeneousPointEvaluation a k ha ha1 hk x).le_opNorm f
    _ = _ := by rw [homogeneousPointEvaluation_norm_const]

theorem homogeneousPhysical_weighted_memLp (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (V : E → ℂ) (hV : MemLp V 2 volume) (f : HomogeneousY a k) :
    MemLp (fun x => V x * homogeneousPhysicalCLM a k ha ha1 hk f x) 2 volume := by
  let C := ‖homogeneousPointEvaluation a k ha ha1 hk 0‖ * ‖f‖
  apply (hV.norm.const_mul C).mono'
    (hV.aestronglyMeasurable.mul (homogeneousPhysicalCLM a k ha ha1 hk f).continuous.aestronglyMeasurable)
  filter_upwards [] with x
  rw [Pi.mul_apply, norm_mul]
  exact (mul_le_mul_of_nonneg_left (homogeneousPhysical_point_bound a k ha ha1 hk f x)
    (norm_nonneg _)).trans_eq (mul_comm _ _)

noncomputable def homogeneousWeightedObservationValue (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (V : E → ℂ) (hV : MemLp V 2 volume) (f : HomogeneousY a k) : Lp ℂ 2 (volume : Measure E) :=
  (homogeneousPhysical_weighted_memLp a k ha ha1 hk V hV f).toLp
    (fun x => V x * homogeneousPhysicalCLM a k ha ha1 hk f x)

theorem homogeneousWeightedObservationValue_ae (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (V : E → ℂ) (hV : MemLp V 2 volume) (f : HomogeneousY a k) :
    homogeneousWeightedObservationValue a k ha ha1 hk V hV f =ᵐ[volume]
      (fun x => V x * homogeneousPhysicalCLM a k ha ha1 hk f x) := MemLp.coeFn_toLp _

theorem homogeneousWeightedObservationValue_norm_le (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (V : E → ℂ) (hV : MemLp V 2 volume) (f : HomogeneousY a k) :
    ‖homogeneousWeightedObservationValue a k ha ha1 hk V hV f‖ ≤
      (‖hV.toLp V‖ * ‖homogeneousPointEvaluation a k ha ha1 hk 0‖) * ‖f‖ := by
  have h : ‖homogeneousWeightedObservationValue a k ha ha1 hk V hV f‖ ≤
      (‖homogeneousPointEvaluation a k ha ha1 hk 0‖ * ‖f‖) * ‖hV.toLp V‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [homogeneousWeightedObservationValue_ae a k ha ha1 hk V hV f,
      hV.coeFn_toLp] with x hx hv
    rw [hx, norm_mul, hv]
    exact (mul_le_mul_of_nonneg_left (homogeneousPhysical_point_bound a k ha ha1 hk f x)
      (norm_nonneg _)).trans_eq (mul_comm _ _)
  exact h.trans_eq (by ring)

noncomputable def homogeneousWeightedObservation (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (V : E → ℂ) (hV : MemLp V 2 volume) : HomogeneousY a k →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  let A : HomogeneousY a k →ₗ[ℂ] Lp ℂ 2 (volume : Measure E) :=
    { toFun := homogeneousWeightedObservationValue a k ha ha1 hk V hV
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [homogeneousWeightedObservationValue_ae a k ha ha1 hk V hV (f + g),
          homogeneousWeightedObservationValue_ae a k ha ha1 hk V hV f,
          homogeneousWeightedObservationValue_ae a k ha ha1 hk V hV g,
          Lp.coeFn_add (homogeneousWeightedObservationValue a k ha ha1 hk V hV f)
            (homogeneousWeightedObservationValue a k ha ha1 hk V hV g)] with x hfg hf hg hadd
        rw [hfg, hadd, Pi.add_apply, hf, hg, map_add, ZeroAtInftyContinuousMap.add_apply, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [homogeneousWeightedObservationValue_ae a k ha ha1 hk V hV (c • f),
          homogeneousWeightedObservationValue_ae a k ha ha1 hk V hV f,
          Lp.coeFn_smul c (homogeneousWeightedObservationValue a k ha ha1 hk V hV f)] with x hcf hf hsmul
        simp only [RingHom.id_apply]
        rw [hcf, hsmul, Pi.smul_apply, hf, map_smul, ZeroAtInftyContinuousMap.smul_apply]
        simp only [smul_eq_mul]
        ring }
  A.mkContinuous (‖hV.toLp V‖ * ‖homogeneousPointEvaluation a k ha ha1 hk 0‖)
    (homogeneousWeightedObservationValue_norm_le a k ha ha1 hk V hV)

theorem homogeneousWeightedObservation_norm_sq (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (V : E → ℂ) (hV : MemLp V 2 volume) (f : HomogeneousY a k) :
    ‖homogeneousWeightedObservation a k ha ha1 hk V hV f‖ ^ 2 =
      ∫ x : E, ‖V x * homogeneousPhysicalCLM a k ha ha1 hk f x‖ ^ 2 := by
  have h := real_inner_self_eq_norm_sq (homogeneousWeightedObservation a k ha ha1 hk V hV f)
  rw [L2.inner_def] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [homogeneousWeightedObservationValue_ae a k ha ha1 hk V hV f] with x hx
  change inner ℝ (homogeneousWeightedObservationValue a k ha ha1 hk V hV f x)
    (homogeneousWeightedObservationValue a k ha ha1 hk V hV f x) = _
  rw [hx, real_inner_self_eq_norm_sq]

theorem tendsto_homogeneousPhysical_weighted_L2_of_weakNull (a k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (V : E → ℂ) (hV : MemLp V 2 volume)
    (u : ℕ → HomogeneousY a k) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x : E,
      ‖V x * homogeneousPhysicalCLM a k ha ha1 hk (u n) x‖ ^ 2)
      atTop (𝓝 0) := by
  let C := ‖homogeneousPointEvaluation a k ha ha1 hk 0‖ * M
  have hv (n : ℕ) (x : E) :
      ‖homogeneousPhysicalCLM a k ha ha1 hk (u n) x‖ ≤ C :=
    (homogeneousPhysical_point_bound a k ha ha1 hk (u n) x).trans
      (mul_le_mul_of_nonneg_left (hu n) (norm_nonneg _))
  have hbound (n : ℕ) (x : E) :
      ‖‖V x * homogeneousPhysicalCLM a k ha ha1 hk (u n) x‖ ^ 2‖ ≤ ‖V x‖ ^ 2 * C ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hv n x) 2) (sq_nonneg _)
  have hpoint (x : E) : Tendsto
      (fun n => ‖V x * homogeneousPhysicalCLM a k ha ha1 hk (u n) x‖ ^ 2) atTop (𝓝 0) := by
    have hx := hweak ((homogeneousPointEvaluation a k ha ha1 hk x).restrictScalars ℝ)
    change Tendsto (fun n => homogeneousPhysicalCLM a k ha ha1 hk (u n) x) atTop (𝓝 0) at hx
    simpa only [norm_mul, mul_pow, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      (hx.norm.pow 2).const_mul (‖V x‖ ^ 2)
  have hi : Integrable (fun x => ‖V x‖ ^ 2 * C ^ 2) :=
    (hV.integrable_norm_pow (p := 2) (by norm_num)).mul_const _
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun x => ‖V x * homogeneousPhysicalCLM a k ha ha1 hk (u n) x‖ ^ 2) volume :=
    (hV.aestronglyMeasurable.mul
      (homogeneousPhysicalCLM a k ha ha1 hk (u n)).continuous.aestronglyMeasurable).norm.pow 2
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun x => ‖V x‖ ^ 2 * C ^ 2) hmeas hi
      (fun n => ae_of_all _ (hbound n)) (ae_of_all _ hpoint)

end DefocusingNLS

end OAI
