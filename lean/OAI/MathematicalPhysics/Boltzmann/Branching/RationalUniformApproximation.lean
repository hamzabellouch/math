import OAI.MathematicalPhysics.Boltzmann.Branching.RenormalizationBounds
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.RenormalizedIntegrability

namespace OAI

section

/-! # Bounded rational renormalizations increasing to the identity -/
noncomputable section
open Set
namespace BoltzmannNonuniqueness.Renormalization

def rationalFunction (k z : ℝ) : ℝ := k*z/(k+z)

theorem rationalFunction_hasDerivAt {k z : ℝ} (hk : 0 < k) (hz : 0 ≤ z) :
    HasDerivAt (rationalFunction k) (k^2/(k+z)^2) z := by
  have hd := ((hasDerivAt_id z).const_mul k).div
    ((hasDerivAt_id z).const_add k) (show k+z ≠ 0 by positivity)
  convert hd using 1
  · rfl
  · dsimp only [id_eq]
    congr 1
    ring

theorem rationalFunction_derivWithin {k z : ℝ} (hk : 0 < k) (hz : 0 ≤ z) :
    derivWithin (rationalFunction k) (Ici 0) z = k^2/(k+z)^2 :=
  (rationalFunction_hasDerivAt hk hz).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Ici (0:ℝ) z hz)

def rational (k : ℝ) (hk : 1 ≤ k) : Renormalization where
  toFun := rationalFunction k
  regular := (contDiffOn_const.mul contDiffOn_id).div
    (contDiffOn_const.add contDiffOn_id) (fun z hz => by have : 0 ≤ z := hz; positivity)
  at_zero := by simp [rationalFunction]
  derivative_bound := by
    have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
    refine ⟨k,hk0.le,fun z hz => ?_⟩
    have hz0 : 0 ≤ z := hz
    rw [rationalFunction_derivWithin hk0 hz,abs_of_nonneg (by positivity)]
    apply (div_le_div_iff₀ (sq_pos_of_pos (by positivity : 0 < k+z)) (by linarith : 0 < 1+z)).mpr
    have ha : 0 ≤ k*(k-1) := mul_nonneg hk0.le (sub_nonneg.mpr hk)
    have hb : 0 ≤ k*z := mul_nonneg hk0.le hz
    nlinarith [sq_nonneg z]

theorem rational_nonneg {k z : ℝ} (hk : 1 ≤ k) (hz : 0 ≤ z) : 0 ≤ (rational k hk).toFun z := by
  change 0 ≤ k*z/(k+z)
  positivity

theorem rational_le_self {k z : ℝ} (hk : 1 ≤ k) (hz : 0 ≤ z) : (rational k hk).toFun z ≤ z := by
  change k*z/(k+z) ≤ z
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  apply (div_le_iff₀ (by positivity : 0 < k+z)).mpr
  nlinarith [sq_nonneg z]

theorem rational_le_parameter {k z : ℝ} (hk : 1 ≤ k) (hz : 0 ≤ z) : (rational k hk).toFun z ≤ k := by
  change k*z/(k+z) ≤ k
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  apply (div_le_iff₀ (by positivity : 0 < k+z)).mpr
  nlinarith [sq_nonneg k]

theorem rational_error {k z : ℝ} (hk : 1 ≤ k) (hz : 0 ≤ z) :
    z-(rational k hk).toFun z = z^2/(k+z) := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  change z-k*z/(k+z) = z^2/(k+z)
  field_simp
  ring

end BoltzmannNonuniqueness.Renormalization

end

end

section

/-! # Quantitative error of the bounded rational renormalizations -/
noncomputable section
namespace BoltzmannNonuniqueness.Renormalization

theorem weighted_rational_eq {k m u : ℝ} (hk : 1 ≤ k) (hm : 0 < m) (hu : 0 ≤ u) :
    m*(rational k hk).toFun (u/m) = k*m*u/(k*m+u) := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hd : 0 < k+u/m := add_pos_of_pos_of_nonneg hk0 (div_nonneg hu hm.le)
  change m*(k*(u/m)/(k+u/m)) = _
  field_simp

theorem weighted_rational_error {k m u : ℝ} (hk : 1 ≤ k) (hm : 0 < m) (hu : 0 ≤ u) :
    u-m*(rational k hk).toFun (u/m) = u^2/(k*m+u) := by
  rw [weighted_rational_eq hk hm hu]
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  field_simp
  ring

theorem weighted_rational_bounds {k m u : ℝ} (hk : 1 ≤ k) (hm : 0 < m) (hu : 0 ≤ u) :
    0 ≤ m*(rational k hk).toFun (u/m) ∧ m*(rational k hk).toFun (u/m) ≤ u := by
  have hz := div_nonneg hu hm.le
  refine ⟨mul_nonneg hm.le (rational_nonneg hk hz),?_⟩
  have h := mul_le_mul_of_nonneg_left (rational_le_self hk hz) hm.le
  simpa only [mul_div_cancel₀ _ hm.ne'] using h

theorem weighted_rational_error_le {k m m₀ u A : ℝ} (hk : 1 ≤ k)
    (hm₀ : 0 < m₀) (hmm : m₀ ≤ m) (hu : 0 ≤ u) (huA : u ≤ A) :
    |u-m*(rational k hk).toFun (u/m)| ≤ A/(k*m₀)*u := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hm : 0 < m := hm₀.trans_le hmm
  rw [abs_of_nonneg (sub_nonneg.mpr (weighted_rational_bounds hk hm hu).2),weighted_rational_error hk hm hu]
  calc
    u^2/(k*m+u) ≤ u^2/(k*m₀) := div_le_div_of_nonneg_left (sq_nonneg u) (mul_pos hk0 hm₀)
      (by nlinarith [mul_le_mul_of_nonneg_left hmm hk0.le])
    _ ≤ A/(k*m₀)*u := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (mul_nonneg hk0.le hm₀.le)
      nlinarith

end BoltzmannNonuniqueness.Renormalization

end

end

section

/-! # Uniform entropy-controlled approximation by rational renormalizations -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def maxwellianLower (R : ℝ) : ℝ :=
  (2*Real.pi)^(-(3/2:ℝ))*Real.exp (-R^2/2)

theorem maxwellianLower_pos (R : ℝ) : 0 < maxwellianLower R := by
  unfold maxwellianLower
  positivity

theorem maxwellianLower_le {R : ℝ} {v : Velocity} (hR : 0 ≤ R) (hv : ‖v‖ ≤ R) :
    maxwellianLower R ≤ maxwellian v := by
  unfold maxwellianLower maxwellian
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith [norm_nonneg v]

def rationalApproximation (k : ℝ) (hk : 1 ≤ k) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  maxwellian p.2*(Renormalization.rational k hk).toFun (f p/maxwellian p.2)

theorem rationalApproximation_measurable {k : ℝ} (hk : 1 ≤ k) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) : Measurable (rationalApproximation k hk f) :=
  (Renormalization.rational k hk).weighted_measurable hfm (by unfold maxwellian; fun_prop)
    hf (fun p => maxwellian_pos p.2)

omit [MeasurableSpace X] in
theorem rationalApproximation_error {R k : ℝ} (hR : 1 ≤ R) (hk : 1 ≤ k)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    |f p-rationalApproximation k hk f p| ≤
      (1/R+Real.exp R/(k*maxwellianLower R))*entropyGauge f p := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hb := Renormalization.weighted_rational_bounds hk (maxwellian_pos p.2) (hf p)
  have hM : 0 < maxwellianLower R := maxwellianLower_pos R
  have hA : 0 ≤ Real.exp R/(k*maxwellianLower R) := by positivity
  have hE : 0 ≤ entropyGauge f p := entropyGauge_nonneg hf p
  by_cases hp : ‖p.2‖ ≤ R ∧ f p ≤ Real.exp R
  · have h := Renormalization.weighted_rational_error_le hk (maxwellianLower_pos R)
      (maxwellianLower_le hR0.le hp.1) (hf p) hp.2
    calc
      _ ≤ Real.exp R/(k*maxwellianLower R)*f p := h
      _ ≤ Real.exp R/(k*maxwellianLower R)*entropyGauge f p :=
        mul_le_mul_of_nonneg_left (entropyGauge_ge_density hf p) hA
      _ ≤ _ := by
        rw [add_mul]
        exact le_add_of_nonneg_left (mul_nonneg (one_div_nonneg.mpr hR0.le) hE)
  · have he := entropyTruncation_error hR hf p
    rw [entropyTruncation,ite_eq_right hp,sub_zero,abs_of_nonneg (hf p)] at he
    change |f p-maxwellian p.2*(Renormalization.rational k hk).toFun (f p/maxwellian p.2)| ≤ _
    rw [abs_of_nonneg (sub_nonneg.mpr hb.2)]
    calc
      _ ≤ f p := sub_le_self _ hb.1
      _ ≤ entropyGauge f p/R := he
      _ = (1/R)*entropyGauge f p := by ring
      _ ≤ _ := by
        rw [add_mul]
        exact le_add_of_nonneg_right (mul_nonneg hA hE)

theorem rationalApproximation_L1_bound {μ : Measure (X × Velocity)} {R k C : ℝ}
    (hR : 1 ≤ R) (hk : 1 ≤ k) {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyGauge f) μ)
    (hC : (∫ p, entropyGauge f p ∂μ) ≤ C) :
    eLpNorm (fun p => f p-rationalApproximation k hk f p) 1 μ ≤
      ENNReal.ofReal ((1/R+Real.exp R/(k*maxwellianLower R))*C) := by
  have hM := maxwellianLower_pos R
  have hfi := integrable_of_entropyGauge hfm hf hi
  have hri := (Renormalization.rational k hk).weighted_integrable hfm
    (by unfold maxwellian; fun_prop) hf (fun p => maxwellian_pos p.2) hfi
  have hei := hfi.sub hri
  change Integrable (fun p => f p-rationalApproximation k hk f p) μ at hei
  rw [eLpNorm_one_eq_lintegral_enorm hei.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hei]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ p, (1/R+Real.exp R/(k*maxwellianLower R))*entropyGauge f p ∂μ :=
      integral_mono hei.norm (hi.const_mul _) (fun p => by
        simpa only [Real.norm_eq_abs] using rationalApproximation_error hR hk hf p)
    _ = _ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hC (by positivity)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Rational renormalizations approach every entropy-bounded family uniformly in L1 -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem rationalApproximation_uniform_L1 {μ : Measure (X × Velocity)}
    {f : ℕ → X × Velocity → ℝ} {C : ℝ} (hfm : ∀ n, Measurable (f n))
    (hf : ∀ n p, 0 ≤ f n p) (hi : ∀ n, Integrable (entropyGauge (f n)) μ)
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ) ≤ C) :
    Tendsto (fun k : ℕ => ⨆ n : ℕ, eLpNorm (fun p => f n p-
      rationalApproximation ((k:ℝ)+1) (by have := Nat.cast_nonneg (α := ℝ) k; linarith) (f n) p)
      1 μ) atTop (𝓝 0) := by
  have hC : 0 ≤ C := (integral_nonneg (fun p => entropyGauge_nonneg (hf 0) p)).trans (hb 0)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hhalf : 0 < ε/2 := ε.half_pos hε.ne'
  obtain ⟨j,hj⟩ := exists_entropyTruncation_radius C hhalf
  let R : ℝ := (j:ℝ)+1
  have hR : 1 ≤ R := by dsimp [R]; have := Nat.cast_nonneg (α := ℝ) j; linarith
  let D : ℝ := Real.exp R/maxwellianLower R*C
  have hM := maxwellianLower_pos R
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have ht : Tendsto (fun k : ℕ => ENNReal.ofReal (D/((k:ℝ)+1))) atTop (𝓝 0) := by
    have h : Tendsto (fun k : ℕ => D/((k:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h
  filter_upwards [ht.eventually (gt_mem_nhds hhalf)] with k hk
  apply iSup_le
  intro n
  have hk1 : 1 ≤ (k:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  calc
    _ ≤ ENNReal.ofReal ((1/R+Real.exp R/(((k:ℝ)+1)*maxwellianLower R))*C) :=
      rationalApproximation_L1_bound hR hk1 (hfm n) (hf n) (hi n) (hb n)
    _ = ENNReal.ofReal (C/R)+ENNReal.ofReal (D/((k:ℝ)+1)) := by
      rw [← ENNReal.ofReal_add (div_nonneg hC (zero_le_one.trans hR)) (div_nonneg hD (by positivity))]
      congr 1
      dsimp only [D]
      field_simp
    _ ≤ ε/2+ε/2 := add_le_add hj hk.le
    _ = ε := ε.add_halves

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
