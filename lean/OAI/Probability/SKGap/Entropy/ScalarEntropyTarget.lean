import Mathlib
import OAI.Probability.SKGap.Entropy.EntropyTransport
import OAI.Probability.SKGap.Entropy.EntropyEll

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
namespace SKGap
theorem gaussian_tanh_integration_by_parts {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0) :
    (∫ y, (y - d) * tanh y ∂gaussianReal d s) =
      (s : ℝ) * (1 - ∫ y, tanh y ^ 2 ∂gaussianReal d s) := by
  have ht : Integrable tanh (gaussianReal d s) := Integrable.of_bound
    continuous_tanh.aestronglyMeasurable 1 (ae_of_all _ (fun y => (abs_tanh_lt_one y).le))
  have h := gaussian_integration_by_parts hs hasDerivAt_tanh ht
    ((integrable_const 1).sub integrable_tanh_sq)
    (integrable_sub_mul_tanh IsGaussian.integrable_id d)
  rw [integral_sub (integrable_const 1) integrable_tanh_sq] at h
  simpa using h

theorem scalar_entropy_finite {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable (fun y : ℝ => y ^ 2) P)
    {j d : ℝ} {s : ℝ≥0} (hj0 : 0 < j) (hj1 : j < 1) (hs : s ≠ 0)
    (hcons : j * (∫ y, tanh y ^ 2 ∂P) ≤ (s : ℝ))
    (hD : klDiv P (gaussianReal d s) ≠ ⊤) :
    let q := ∫ y, tanh y ^ 2 ∂P
    let a := ∫ y, (y - d) * tanh y ∂P
    let T := j * (a - (s : ℝ) * (1 - q)) ^ 2 / (2 * (s : ℝ) * ((s : ℝ) + j * q))
    T ≤ (klDiv P (gaussianReal d s)).toReal ∧
      (a ≠ (s : ℝ) * (1 - q) → T < (klDiv P (gaussianReal d s)).toReal) := by
  dsimp only
  let q := ∫ y, tanh y ^ 2 ∂P
  let a := ∫ y, (y - d) * tanh y ∂P
  let k := j * q / (s : ℝ)
  let B := j * (1 - q)
  let C := j * a / (s : ℝ)
  let D := (klDiv P (gaussianReal d s)).toReal
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  have hq0 : 0 < q := entropy_q_pos hs hD
  have hq1 : q < 1 := entropy_q_lt_one
  have hk0 : 0 < k := div_pos (mul_pos hj0 hq0) hsp
  have hk1 : k ≤ 1 := (div_le_one hsp).mpr hcons
  have hB0 : 0 < B := mul_pos hj0 (sub_pos.mpr hq1)
  have hB1 : B < 1 := by dsimp [B]; nlinarith
  have htransport (u : ℝ) (hu : u < 1) :
      u * (C - B) - k * u ^ 2 / 2 - B * entropyEll u ≤ j * D := by
    have h := mul_le_mul_of_nonneg_left (entropy_transport_lower (secondMoment_integrable hP) hu hs hD) hj0.le
    change j * (u / (s : ℝ) * a - u ^ 2 / (2 * (s : ℝ)) * q + (1 - q) * log (1 - u)) ≤ j * D at h
    convert h using 1
    dsimp [k, B, C, entropyEll]
    field_simp
    ring
  have hvariance (hC : 1 < C) : C ^ 2 / k - 1 - log (C ^ 2 / k) ≤ 2 * (j * D) := by
    let v := (∫ y, (y - d) ^ 2 ∂P) / (s : ℝ)
    have hcauchy := entropy_moment_cauchy hP d hq0
    have hcv : C ^ 2 / (j * k) ≤ v := by
      have heq : C ^ 2 / (j * k) * (s : ℝ) = a ^ 2 / q := by
        dsimp [C, k]
        field_simp
      dsimp [v]
      rw [le_div_iff₀ hsp, heq, div_le_iff₀ hq0]
      simpa only [q, a, mul_comm] using hcauchy
    have hv : 0 < v := (div_pos (pow_pos (by linarith : 0 < C) 2) (mul_pos hj0 hk0)).trans_le hcv
    have hvar : (∫ y, (y - d) ^ 2 ∂P) = (s : ℝ) * v := by dsimp [v]; field_simp
    have hbound := entropy_variance_lower hs (centered_secondMoment_integrable hP d) hD hv hvar
    exact entropy_variance_scaled_lower hj0 hj1.le hk0 hk1 hC hcv hbound
  have hopt := entropy_scalar_optimization hk0 hk1 hB0 hB1
    (mul_nonneg hj0.le ENNReal.toReal_nonneg) htransport hvariance
  have heq : (C - B) ^ 2 / (2 * (1 + k)) =
      j * (j * (a - (s : ℝ) * (1 - q)) ^ 2 / (2 * (s : ℝ) * ((s : ℝ) + j * q))) := by
    dsimp [C, B, k]
    field_simp
  rw [heq] at hopt
  refine ⟨le_of_mul_le_mul_left hopt.1 hj0, ?_⟩
  intro ha
  have hCB : C ≠ B := by
    intro h
    apply ha
    dsimp [C, B] at h
    have he := (div_eq_iff hsp.ne').mp h
    nlinarith
  exact lt_of_mul_lt_mul_left (hopt.2 hCB) hj0.le

def scalarEntropyTarget (P : Measure ℝ) (j d : ℝ) (s : ℝ≥0) : ℝ :=
  j * ((∫ y, (y - d) * tanh y ∂P) - (s : ℝ) * (1 - ∫ y, tanh y ^ 2 ∂P)) ^ 2 /
    (2 * (s : ℝ) * ((s : ℝ) + j * (∫ y, tanh y ^ 2 ∂P)))

theorem scalarEntropyTarget_nonneg {P : Measure ℝ} {j d : ℝ} {s : ℝ≥0} (hj : 0 ≤ j) :
    0 ≤ scalarEntropyTarget P j d s := by
  unfold scalarEntropyTarget
  apply div_nonneg (mul_nonneg hj (sq_nonneg _))
  positivity

theorem scalar_entropy_inequality {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable (fun y : ℝ => y ^ 2) P)
    {j d : ℝ} {s : ℝ≥0} (hj0 : 0 < j) (hj1 : j < 1) (hs : s ≠ 0)
    (hcons : j * (∫ y, tanh y ^ 2 ∂P) ≤ (s : ℝ)) :
    ENNReal.ofReal (scalarEntropyTarget P j d s) ≤ klDiv P (gaussianReal d s) := by
  by_cases hD : klDiv P (gaussianReal d s) = ⊤
  · simp [hD]
  · rw [ENNReal.ofReal_le_iff_le_toReal hD]
    exact (scalar_entropy_finite hP hj0 hj1 hs hcons hD).1

theorem scalar_entropy_equality_iff {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable (fun y : ℝ => y ^ 2) P)
    {j d : ℝ} {s : ℝ≥0} (hj0 : 0 < j) (hj1 : j < 1) (hs : s ≠ 0)
    (hcons : j * (∫ y, tanh y ^ 2 ∂P) ≤ (s : ℝ)) :
    klDiv P (gaussianReal d s) = ENNReal.ofReal (scalarEntropyTarget P j d s) ↔
      P = gaussianReal d s := by
  constructor
  · intro he
    have hD : klDiv P (gaussianReal d s) ≠ ⊤ := by rw [he]; exact ENNReal.ofReal_ne_top
    have hreal : (klDiv P (gaussianReal d s)).toReal = scalarEntropyTarget P j d s := by
      rw [he, ENNReal.toReal_ofReal (scalarEntropyTarget_nonneg hj0.le)]
    have hm : (∫ y, (y - d) * tanh y ∂P) = (s : ℝ) * (1 - ∫ y, tanh y ^ 2 ∂P) := by
      by_contra h
      have hstrict := (scalar_entropy_finite hP hj0 hj1 hs hcons hD).2 h
      change scalarEntropyTarget P j d s < _ at hstrict
      rw [hreal] at hstrict
      exact lt_irrefl _ hstrict
    have hzero : klDiv P (gaussianReal d s) = 0 := by simpa [scalarEntropyTarget, hm] using he
    exact klDiv_eq_zero_iff.mp hzero
  · rintro rfl
    simp [scalarEntropyTarget, gaussian_tanh_integration_by_parts hs, klDiv_self]

end SKGap

noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace SKGap

def EntropyTestBound (P Q : Measure ℝ) (D : ℝ) : Prop :=
  ∀ f : ℝ →ᵇ ℝ, (∫ x, f x ∂P) - log (∫ x, exp (f x) ∂Q) ≤ D

def realClip (n : ℕ) (x : ℝ) : ℝ := max (-(n:ℝ)) (min (n:ℝ) x)

lemma realClip_bounds (n : ℕ) (x : ℝ) : -(n:ℝ) ≤ realClip n x ∧ realClip n x ≤ n := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_left _ _)

lemma realClip_abs (n : ℕ) (x : ℝ) : |realClip n x| ≤ |x| := by
  rw [abs_le]
  constructor
  · exact le_sup_of_le_right (le_min (by linarith [abs_nonneg x]) (neg_abs_le x))
  · exact sup_le (by linarith [abs_nonneg x]) ((min_le_right _ _).trans (le_abs_self x))

lemma realClip_le (n : ℕ) (x : ℝ) : realClip n x ≤ max 0 x :=
  max_le (by linarith [le_max_left (0:ℝ) x]) ((min_le_right _ _).trans (le_max_right _ _))

lemma tendsto_realClip (x : ℝ) : Tendsto (fun n : ℕ => realClip n x) atTop (𝓝 x) := by
  have he : ∀ᶠ n : ℕ in atTop, realClip n x = x := by
    obtain ⟨N, hN⟩ := exists_nat_ge |x|
    filter_upwards [eventually_ge_atTop N] with n hn
    have hb : |x| ≤ (n:ℝ) := hN.trans (by exact_mod_cast hn)
    have hx := abs_le.mp hb
    simp only [realClip, min_eq_right hx.2, max_eq_right hx.1]
  exact (tendsto_congr' he).2 tendsto_const_nhds

def clippedBC {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => realClip n (f x))
    (by unfold realClip; fun_prop) n (fun x => by
      rw [Real.norm_eq_abs, abs_le]; exact realClip_bounds n (f x))

lemma entropyTestBound_continuous {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {D : ℝ} (hD : EntropyTestBound P Q D)
    {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable f P)
    (he : Integrable (fun x => exp (f x)) Q) :
    (∫ x, f x ∂P) - log (∫ x, exp (f x) ∂Q) ≤ D := by
  have hP : Tendsto (fun n => ∫ x, clippedBC hf n x ∂P) atTop (𝓝 (∫ x, f x ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |f x|)
    · intro n; exact (clippedBC hf n).continuous.aestronglyMeasurable
    · exact hi.abs
    · intro n; exact ae_of_all _ (fun x => by
        change ‖realClip n (f x)‖ ≤ |f x|
        rw [Real.norm_eq_abs]; exact realClip_abs n (f x))
    · exact ae_of_all _ (fun x => tendsto_realClip (f x))
  have hQ : Tendsto (fun n => ∫ x, exp (clippedBC hf n x) ∂Q) atTop (𝓝 (∫ x, exp (f x) ∂Q)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => 1+exp (f x))
    · intro n; exact (by fun_prop : Continuous (fun x => exp (clippedBC hf n x))).aestronglyMeasurable
    · exact (integrable_const 1).add he
    · intro n; exact ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        calc
          _ ≤ exp (max 0 (f x)) := exp_le_exp.mpr (realClip_le n (f x))
          _ ≤ 1+exp (f x) := by
            by_cases hx : 0 ≤ f x
            · rw [max_eq_right hx]; linarith
            · rw [max_eq_left (le_of_not_ge hx), exp_zero]; linarith [exp_pos (f x)])
    · exact ae_of_all _ (fun x => continuous_exp.continuousAt.tendsto.comp (tendsto_realClip (f x)))
  have hpos : 0 < ∫ x, exp (f x) ∂Q := integral_pos_iff_support_of_nonneg
    (fun x => (exp_pos (f x)).le) he |>.mpr (by simp [Function.support, (exp_pos _).ne'])
  exact le_of_tendsto (hP.sub ((continuousAt_log hpos.ne').tendsto.comp hQ))
    (Eventually.of_forall (fun n => hD (clippedBC hf n)))

lemma entropyTestBound_normalized {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {D : ℝ} (hD : EntropyTestBound P Q D)
    {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable f P)
    (he : Integrable (fun x => exp (f x)) Q) (hZ : ∫ x, exp (f x) ∂Q = 1) :
    (∫ x, f x ∂P) ≤ D := by
  simpa only [hZ, log_one, sub_zero] using entropyTestBound_continuous hD hf hi he

lemma integrable_exp_boundedContinuous {Q : Measure ℝ} [IsFiniteMeasure Q] (f : ℝ →ᵇ ℝ) (t : ℝ) :
    Integrable (fun x => exp (t*f x)) Q := by
  apply Integrable.of_bound (by fun_prop) (exp (|t| * ‖f‖))
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    calc
      t*f x ≤ |t*f x| := le_abs_self _
      _ = |t| * |f x| := abs_mul _ _
      _ ≤ |t| * ‖f‖ := mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x) (abs_nonneg _))

lemma boundedContinuous_mgf_deriv {Q : Measure ℝ} [IsProbabilityMeasure Q] (f : ℝ →ᵇ ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x, exp (t*f x) ∂Q) (∫ x, f x ∂Q) 0 := by
  have hset : integrableExpSet (fun x => f x) Q = univ := by
    ext t; exact iff_true_intro (integrable_exp_boundedContinuous f t)
  have h := hasDerivAt_mgf (X := fun x => f x) (μ := Q) (t := 0) (by simp [hset])
  convert! h using 1; simp

lemma entropyTestBound_zero_eq {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hD : EntropyTestBound P Q 0) : P = Q := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let g : ℝ → ℝ := fun t => log (∫ x, exp (t*f x) ∂Q) - t*(∫ x, f x ∂P)
  have hg0 : g 0 = 0 := by simp [g]
  have hmin : IsLocalMin g 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have h := hD (t • f)
    simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul, integral_const_mul] at h
    rw [hg0]
    dsimp [g]
    exact (show 0 ≤ log (∫ x, exp (t*f x) ∂Q)-t*(∫ x, f x ∂P) by linarith)
  have hder : HasDerivAt g ((∫ x, f x ∂Q)-(∫ x, f x ∂P)) 0 := by
    have h := (boundedContinuous_mgf_deriv (Q := Q) f).log (by simp)
    convert! h.sub ((hasDerivAt_id (0:ℝ)).mul_const (∫ x, f x ∂P)) using 1; simp
  have hz := hmin.hasDerivAt_eq_zero hder
  linarith

lemma entropyTestBound_nonneg {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {D : ℝ} (hD : EntropyTestBound P Q D) : 0 ≤ D := by
  simpa using hD 0

end SKGap

end
end
end
end

end OAI
