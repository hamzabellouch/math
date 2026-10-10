import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace OAI

/-! # Algebra and integration in the one-block vanishing argument

The scalar one-block vanishing argument in Section 8 of
*Positively curved Einstein four-manifolds* (23 September 2026). -/

namespace PositiveEinsteinFour

open MeasureTheory Filter

noncomputable section

/-- The coefficient `c` in the paper's equation (15). -/
def couplingCoefficient (v b : ℝ) : ℝ := 2 / 5 - 3 / 10 * v * b

theorem couplingCoefficient_lower {v b : ℝ}
    (hvb : v + b ≤ 2) (hv : 0 ≤ v) (hb : 0 ≤ b) :
    1 / 10 ≤ couplingCoefficient v b := by
  have hsum : (v + b) ^ 2 ≤ 4 := by nlinarith
  have hprod : v * b ≤ 1 := by nlinarith [sq_nonneg (v - b)]
  unfold couplingCoefficient
  nlinarith

/-- The rational weight `R_v` in equation (15). -/
def normWeight (v : ℝ) : ℝ := 4 * (1 + v) / (1 + 6 * v + v ^ 2)

theorem weight_denominator_pos {v : ℝ} (hv : 0 ≤ v) :
    0 < 1 + 6 * v + v ^ 2 := by positivity

theorem normWeight_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ normWeight v := by
  unfold normWeight
  positivity

/-- The fourth power identity supplies the sharp weight comparison. -/
theorem weight_defect_identity (z : ℝ) :
    1 + 6 * z ^ 2 + (z ^ 2) ^ 2 - 4 * z * (1 + z ^ 2) = (z - 1) ^ 4 := by
  ring

theorem normWeight_mul_sqrt_le {v : ℝ} (hv : 0 ≤ v) :
    normWeight v * Real.sqrt v ≤ 1 := by
  have hs := Real.sq_sqrt hv
  have hd := weight_denominator_pos hv
  have hid := weight_defect_identity (Real.sqrt v)
  rw [hs] at hid
  have hp : 0 ≤ (Real.sqrt v - 1) ^ 4 := by positivity
  unfold normWeight
  rw [div_mul_eq_mul_div]
  apply (div_le_one hd).2
  nlinarith [hid]

theorem normWeight_mul_sqrt_lt {v : ℝ} (hv : 0 ≤ v) (hne : v ≠ 1) :
    normWeight v * Real.sqrt v < 1 := by
  have hs := Real.sq_sqrt hv
  have hd := weight_denominator_pos hv
  have hz : Real.sqrt v - 1 ≠ 0 := by
    intro h
    have : Real.sqrt v = 1 := sub_eq_zero.mp h
    rw [this] at hs
    exact hne (by simpa using hs.symm)
  have hp : 0 < (Real.sqrt v - 1) ^ 4 := by positivity
  have hid := weight_defect_identity (Real.sqrt v)
  rw [hs] at hid
  unfold normWeight
  rw [div_mul_eq_mul_div]
  apply (div_lt_one hd).2
  nlinarith [hid]

theorem normWeight_le_inv_sqrt {v : ℝ} (hv : 0 < v) :
    normWeight v ≤ 1 / Real.sqrt v := by
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hv)).2
  exact normWeight_mul_sqrt_le hv.le

theorem normWeight_lt_inv_sqrt {v : ℝ} (hv : 0 < v) (hne : v ≠ 1) :
    normWeight v < 1 / Real.sqrt v := by
  apply (lt_div_iff₀ (Real.sqrt_pos.mpr hv)).2
  exact normWeight_mul_sqrt_lt hv.le hne

/-- Weighted two-term Cauchy--Schwarz, without any square-root denominators. -/
theorem weighted_square_le {a b s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (s * a + t * b) ^ 2 ≤ (a + b) * (s ^ 2 * a + t ^ 2 * b) := by
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (s - t))]

private theorem inv_sqrt_sq {v : ℝ} (hv : 0 ≤ v) :
    (1 / Real.sqrt v) ^ 2 = 1 / v := by
  rw [div_pow, one_pow, Real.sq_sqrt hv]

/-- Two-term Cauchy--Schwarz with the zero-denominator convention used in
the paper. The energies `p` and `q` stand for squared gradient norms. -/
theorem radial_cost_bound {v b p q : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpzero : v = 0 → p = 0) (hqzero : b = 0 → q = 0) :
    (normWeight v * p + normWeight b * q) ^ 2 ≤
      (p + q) * (p / v + q / b) := by
  have hpbound : normWeight v * p ≤ (1 / Real.sqrt v) * p := by
    rcases hv.eq_or_lt with hv | hv
    · simp [hpzero hv.symm]
    · exact mul_le_mul_of_nonneg_right (normWeight_le_inv_sqrt hv) hp
  have hqbound : normWeight b * q ≤ (1 / Real.sqrt b) * q := by
    rcases hb.eq_or_lt with hb | hb
    · simp [hqzero hb.symm]
    · exact mul_le_mul_of_nonneg_right (normWeight_le_inv_sqrt hb) hq
  have hr : 0 ≤ normWeight v * p + normWeight b * q :=
    add_nonneg (mul_nonneg (normWeight_nonneg hv) hp)
      (mul_nonneg (normWeight_nonneg hb) hq)
  have hsq := weighted_square_le (s := 1 / Real.sqrt v) (t := 1 / Real.sqrt b) hp hq
  rw [inv_sqrt_sq hv, inv_sqrt_sq hb] at hsq
  have hbound := add_le_add hpbound hqbound
  calc
    (normWeight v * p + normWeight b * q) ^ 2 ≤
        ((1 / Real.sqrt v) * p + (1 / Real.sqrt b) * q) ^ 2 := by nlinarith
    _ ≤ (p + q) * (p / v + q / b) := by simpa [div_eq_mul_inv, mul_comm] using hsq

/-- Away from the norm-one level set, an active gradient makes the radial
cost comparison strict. Level-set gradient vanishing is supplied separately
by the geometric application. -/
theorem radial_cost_strict_of_pos {v b p q : ℝ}
    (hv : 0 < v) (hb : 0 < b) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hactive : (0 < p ∧ v ≠ 1) ∨ (0 < q ∧ b ≠ 1)) :
    (normWeight v * p + normWeight b * q) ^ 2 <
      (p + q) * (p / v + q / b) := by
  have hpbound := mul_le_mul_of_nonneg_right (normWeight_le_inv_sqrt hv) hp
  have hqbound := mul_le_mul_of_nonneg_right (normWeight_le_inv_sqrt hb) hq
  have hbound : normWeight v * p + normWeight b * q <
      (1 / Real.sqrt v) * p + (1 / Real.sqrt b) * q := by
    rcases hactive with ⟨hpa, hne⟩ | ⟨hqa, hne⟩
    · exact add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_right (normWeight_lt_inv_sqrt hv hne) hpa) hqbound
    · exact add_lt_add_of_le_of_lt hpbound
        (mul_lt_mul_of_pos_right (normWeight_lt_inv_sqrt hb hne) hqa)
  have hr : 0 ≤ normWeight v * p + normWeight b * q :=
    add_nonneg (mul_nonneg (normWeight_nonneg hv.le) hp)
      (mul_nonneg (normWeight_nonneg hb.le) hq)
  have hsq := weighted_square_le (s := 1 / Real.sqrt v) (t := 1 / Real.sqrt b) hp hq
  rw [inv_sqrt_sq hv.le, inv_sqrt_sq hb.le] at hsq
  calc
    (normWeight v * p + normWeight b * q) ^ 2 <
        ((1 / Real.sqrt v) * p + (1 / Real.sqrt b) * q) ^ 2 := by nlinarith
    _ ≤ (p + q) * (p / v + q / b) := by simpa [div_eq_mul_inv, mul_comm] using hsq

theorem radial_cost_strict {v b p q : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpzero : v = 0 → p = 0) (hqzero : b = 0 → q = 0)
    (hactive : (0 < p ∧ v ≠ 1) ∨ (0 < q ∧ b ≠ 1)) :
    (normWeight v * p + normWeight b * q) ^ 2 <
      (p + q) * (p / v + q / b) := by
  have hpbound : normWeight v * p ≤ (1 / Real.sqrt v) * p := by
    rcases hv.eq_or_lt with hv | hv
    · simp [hpzero hv.symm]
    · exact mul_le_mul_of_nonneg_right (normWeight_le_inv_sqrt hv) hp
  have hqbound : normWeight b * q ≤ (1 / Real.sqrt b) * q := by
    rcases hb.eq_or_lt with hb | hb
    · simp [hqzero hb.symm]
    · exact mul_le_mul_of_nonneg_right (normWeight_le_inv_sqrt hb) hq
  have hbound : normWeight v * p + normWeight b * q <
      (1 / Real.sqrt v) * p + (1 / Real.sqrt b) * q := by
    rcases hactive with ⟨hpa, hne⟩ | ⟨hqa, hne⟩
    · have hvpos : 0 < v := lt_of_le_of_ne hv (by intro h; linarith [hpzero h.symm])
      exact add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_right (normWeight_lt_inv_sqrt hvpos hne) hpa) hqbound
    · have hbpos : 0 < b := lt_of_le_of_ne hb (by intro h; linarith [hqzero h.symm])
      exact add_lt_add_of_le_of_lt hpbound
        (mul_lt_mul_of_pos_right (normWeight_lt_inv_sqrt hbpos hne) hqa)
  have hr : 0 ≤ normWeight v * p + normWeight b * q :=
    add_nonneg (mul_nonneg (normWeight_nonneg hv) hp)
      (mul_nonneg (normWeight_nonneg hb) hq)
  have hsq := weighted_square_le (s := 1 / Real.sqrt v) (t := 1 / Real.sqrt b) hp hq
  rw [inv_sqrt_sq hv, inv_sqrt_sq hb] at hsq
  calc
    (normWeight v * p + normWeight b * q) ^ 2 <
        ((1 / Real.sqrt v) * p + (1 / Real.sqrt b) * q) ^ 2 := by nlinarith
    _ ≤ (p + q) * (p / v + q / b) := by simpa [div_eq_mul_inv, mul_comm] using hsq

/-- The final numerical contradiction once both nonzero norms are constant
and the published Weyl gaps have been applied. -/
theorem not_two_constant_blocks {v b : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hvGap : 1 ≤ v ^ 2) (hbGap : 1 ≤ b ^ 2) : ¬ v + b < 2 := by
  have hv1 : 1 ≤ v := by nlinarith
  have hb1 : 1 ≤ b := by nlinarith
  linarith

theorem coupled_square_identity {c θ r j : ℝ} (hc : c ≠ 0) :
    -c * j + 2 * θ * r - θ ^ 2 / c =
      -(θ - c * r) ^ 2 / c - c * (j - r ^ 2) := by
  field_simp
  ring

theorem coupled_nonpositive {c θ r j I : ℝ} (hc : 0 < c)
    (hj : r ^ 2 ≤ j) (hI : I ≤ -c * j + 2 * θ * r - θ ^ 2 / c) :
    I ≤ 0 := by
  rw [coupled_square_identity hc.ne'] at hI
  rw [neg_div] at hI
  have hsq : 0 ≤ (θ - c * r) ^ 2 / c := div_nonneg (sq_nonneg _) hc.le
  have hgap : 0 ≤ c * (j - r ^ 2) := mul_nonneg hc.le (sub_nonneg.mpr hj)
  linarith

theorem coupled_strictly_negative {c θ r j I : ℝ} (hc : 0 < c)
    (hj : r ^ 2 < j) (hI : I ≤ -c * j + 2 * θ * r - θ ^ 2 / c) :
    I < 0 := by
  rw [coupled_square_identity hc.ne'] at hI
  rw [neg_div] at hI
  have hsq : 0 ≤ (θ - c * r) ^ 2 / c := div_nonneg (sq_nonneg _) hc.le
  have hgap : 0 < c * (j - r ^ 2) := mul_pos hc (sub_pos.mpr hj)
  linarith

/-- The measure-theoretic closing step: a nonnegative integral forces equality
in the pointwise Cauchy--Schwarz bound. No integrability of the separate
possibly singular summands is needed here beyond integrability of `I`. -/
theorem ae_equality_of_coupled_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {I c θ r j : X → ℝ}
    (hIi : Integrable I μ) (hIntegral : 0 ≤ ∫ x, I x ∂μ)
    (hc : ∀ᵐ x ∂μ, 0 < c x) (hj : ∀ᵐ x ∂μ, r x ^ 2 ≤ j x)
    (hI : ∀ᵐ x ∂μ,
      I x ≤ -c x * j x + 2 * θ x * r x - θ x ^ 2 / c x) :
    ∀ᵐ x ∂μ, j x = r x ^ 2 := by
  have hnonpos : ∀ᵐ x ∂μ, I x ≤ 0 := by
    filter_upwards [hc, hj, hI] with x hcx hjx hIx
    exact coupled_nonpositive hcx hjx hIx
  have hint : ∫ x, I x ∂μ = 0 :=
    le_antisymm (integral_nonpos_of_ae hnonpos) hIntegral
  have hneg : ∀ᵐ x ∂μ, 0 ≤ -I x := by
    filter_upwards [hnonpos] with x hx using neg_nonneg.mpr hx
  have hzero : (fun x => -I x) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hneg hIi.neg).1 (by rw [integral_neg, hint, neg_zero])
  filter_upwards [hc, hj, hI, hzero] with x hcx hjx hIx hzx
  apply le_antisymm _ hjx
  by_contra h
  have hstrict := coupled_strictly_negative hcx (lt_of_not_ge h) hIx
  simp only [Pi.zero_apply, neg_eq_zero] at hzx
  linarith

/-- Equality in the radial bound annihilates both gradient energies. The
assumptions concerning level sets are exactly the scalar level-set fact used
in the manuscript, and are kept separate from the new coupled bound. -/
theorem zero_energies_of_radial_equality {v b p q : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpzero : v = 0 → p = 0) (hqzero : b = 0 → q = 0)
    (hpone : v = 1 → p = 0) (hqone : b = 1 → q = 0)
    (heq : (p + q) * (p / v + q / b) =
      (normWeight v * p + normWeight b * q) ^ 2) : p = 0 ∧ q = 0 := by
  by_contra h
  have hactive : (0 < p ∧ v ≠ 1) ∨ (0 < q ∧ b ≠ 1) := by
    by_cases hp0 : p = 0
    · right
      have hq0 : q ≠ 0 := by intro hq0; exact h ⟨hp0, hq0⟩
      refine ⟨lt_of_le_of_ne hq (Ne.symm hq0), ?_⟩
      intro hb1
      exact hq0 (hqone hb1)
    · left
      refine ⟨lt_of_le_of_ne hp (Ne.symm hp0), ?_⟩
      intro hv1
      exact hp0 (hpone hv1)
  have hlt := radial_cost_strict hv hb hp hq hpzero hqzero hactive
  linarith

/-- The first conclusion of the one-block vanishing argument, including zero
sets. The new geometric estimate on `I` is an explicit premise of this scalar
reduction, not an assumed published theorem or a claim that the geometric
estimate has already been proved. -/
theorem ae_zero_energies_of_coupled_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {I θ v b p q : X → ℝ}
    (hIi : Integrable I μ) (hIntegral : 0 ≤ ∫ x, I x ∂μ)
    (hv : ∀ᵐ x ∂μ, 0 ≤ v x) (hb : ∀ᵐ x ∂μ, 0 ≤ b x)
    (hsum : ∀ᵐ x ∂μ, v x + b x ≤ 2)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hsupport : ∀ᵐ x ∂μ,
      (v x = 0 → p x = 0) ∧ (b x = 0 → q x = 0) ∧
      (v x = 1 → p x = 0) ∧ (b x = 1 → q x = 0))
    (hI : ∀ᵐ x ∂μ,
      I x ≤ -couplingCoefficient (v x) (b x) *
        ((p x + q x) * (p x / v x + q x / b x)) +
        2 * θ x * (normWeight (v x) * p x + normWeight (b x) * q x) -
        θ x ^ 2 / couplingCoefficient (v x) (b x)) :
    ∀ᵐ x ∂μ, p x = 0 ∧ q x = 0 := by
  have hc : ∀ᵐ x ∂μ, 0 < couplingCoefficient (v x) (b x) := by
    filter_upwards [hv, hb, hsum] with x hvx hbx hsumx
    exact lt_of_lt_of_le (by norm_num) (couplingCoefficient_lower hsumx hvx hbx)
  have hj : ∀ᵐ x ∂μ,
      (normWeight (v x) * p x + normWeight (b x) * q x) ^ 2 ≤
        (p x + q x) * (p x / v x + q x / b x) := by
    filter_upwards [hv, hb, hp, hq, hsupport] with x hvx hbx hpx hqx hsx
    exact radial_cost_bound hvx hbx hpx hqx hsx.1 hsx.2.1
  have heq := ae_equality_of_coupled_bound hIi hIntegral hc hj hI
  filter_upwards [hv, hb, hp, hq, hsupport, heq] with x hvx hbx hpx hqx hsx heqx
  exact zero_energies_of_radial_equality hvx hbx hpx hqx
    hsx.1 hsx.2.1 hsx.2.2.1 hsx.2.2.2 heqx

/-- A variance bound turns a vanishing gradient energy into an almost-everywhere
constant. The mean is left explicit so the lemma does not require a particular
normalization of the measure. -/
theorem ae_eq_mean_of_zero_energy {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {v p : X → ℝ}
    (hi : Integrable (fun x => (v x - ∫ y, v y ∂μ) ^ 2) μ)
    (hvariance : (∫ x, (v x - ∫ y, v y ∂μ) ^ 2 ∂μ) ≤ ∫ x, p x ∂μ)
    (hp : p =ᵐ[μ] 0) : v =ᵐ[μ] fun _ => ∫ x, v x ∂μ := by
  have hpint : ∫ x, p x ∂μ = 0 := by rw [integral_congr_ae hp]; simp
  have hvarint : (∫ x, (v x - ∫ y, v y ∂μ) ^ 2 ∂μ) = 0 :=
    le_antisymm (by simpa only [hpint] using hvariance)
      (integral_nonneg fun _ => sq_nonneg _)
  have hzero := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).1 hvarint
  filter_upwards [hzero] with x hx
  simpa only [Pi.zero_apply, sq_eq_zero_iff, sub_eq_zero] using hx

/-- The full scalar one-block vanishing step of Section 8. The combined
integrand estimate is a premise, and remains a separate geometric obligation;
this theorem does not identify it as a published result. The variance and gap
premises have exactly the normalizations needed in the closing argument. -/
theorem one_block_vanishes_of_coupled_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {I θ v b p q : X → ℝ}
    (hIi : Integrable I μ) (hIntegral : 0 ≤ ∫ x, I x ∂μ)
    (hv : ∀ᵐ x ∂μ, 0 ≤ v x) (hb : ∀ᵐ x ∂μ, 0 ≤ b x)
    (hsum : ∀ᵐ x ∂μ, v x + b x < 2)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hsupport : ∀ᵐ x ∂μ,
      (v x = 0 → p x = 0) ∧ (b x = 0 → q x = 0) ∧
      (v x = 1 → p x = 0) ∧ (b x = 1 → q x = 0))
    (hI : ∀ᵐ x ∂μ,
      I x ≤ -couplingCoefficient (v x) (b x) *
        ((p x + q x) * (p x / v x + q x / b x)) +
        2 * θ x * (normWeight (v x) * p x + normWeight (b x) * q x) -
        θ x ^ 2 / couplingCoefficient (v x) (b x))
    (hvi : Integrable (fun x => (v x - ∫ y, v y ∂μ) ^ 2) μ)
    (hbi : Integrable (fun x => (b x - ∫ y, b y ∂μ) ^ 2) μ)
    (hvv : (∫ x, (v x - ∫ y, v y ∂μ) ^ 2 ∂μ) ≤ ∫ x, p x ∂μ)
    (hbv : (∫ x, (b x - ∫ y, b y ∂μ) ^ 2 ∂μ) ≤ ∫ x, q x ∂μ)
    (hvgap : (∃ x, v x ≠ 0) → 1 ≤ ∫ x, v x ^ 2 ∂μ)
    (hbgap : (∃ x, b x ≠ 0) → 1 ≤ ∫ x, b x ^ 2 ∂μ) :
    (∀ x, v x = 0) ∨ ∀ x, b x = 0 := by
  classical
  have hzero := ae_zero_energies_of_coupled_bound hIi hIntegral hv hb
    (hsum.mono fun _ hx => hx.le) hp hq hsupport hI
  have hvconst := ae_eq_mean_of_zero_energy hvi hvv (hzero.mono fun _ hx => hx.1)
  have hbconst := ae_eq_mean_of_zero_energy hbi hbv (hzero.mono fun _ hx => hx.2)
  by_contra hboth
  push Not at hboth
  have hvmean : 1 ≤ (∫ x, v x ∂μ) ^ 2 := by
    have hgap := hvgap hboth.1
    have heq : (∫ x, v x ^ 2 ∂μ) = (∫ x, v x ∂μ) ^ 2 := by
      calc
        _ = ∫ _ : X, (∫ x, v x ∂μ) ^ 2 ∂μ :=
          integral_congr_ae (hvconst.mono fun _ hx => congrArg (fun z : ℝ => z ^ 2) hx)
        _ = _ := by simp
    rwa [heq] at hgap
  have hbmean : 1 ≤ (∫ x, b x ∂μ) ^ 2 := by
    have hgap := hbgap hboth.2
    have heq : (∫ x, b x ^ 2 ∂μ) = (∫ x, b x ∂μ) ^ 2 := by
      calc
        _ = ∫ _ : X, (∫ x, b x ∂μ) ^ 2 ∂μ :=
          integral_congr_ae (hbconst.mono fun _ hx => congrArg (fun z : ℝ => z ^ 2) hx)
        _ = _ := by simp
    rwa [heq] at hgap
  obtain ⟨x, hx⟩ := (hv.and (hb.and (hsum.and (hvconst.and hbconst)))).exists
  dsimp only at hx
  have hvnonneg : 0 ≤ ∫ x, v x ∂μ := by rw [← hx.2.2.2.1]; exact hx.1
  have hbnonneg : 0 ≤ ∫ x, b x ∂μ := by rw [← hx.2.2.2.2]; exact hx.2.1
  have hstrict : (∫ x, v x ∂μ) + (∫ x, b x ∂μ) < 2 := by
    rw [← hx.2.2.2.1, ← hx.2.2.2.2]
    exact hx.2.2.1
  exact not_two_constant_blocks hvnonneg hbnonneg hvmean hbmean hstrict

end

end PositiveEinsteinFour

end OAI
