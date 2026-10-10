import OAI.Probability.InvariantIsing.Spectral.SpectralConvexity

namespace OAI

/-! A quantitative estimate at zero for the finite spectral transform. -/

noncomputable section

open scoped BigOperators Topology
open Filter Set

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

/-- An exact remainder identity for the finite inverse resolvent. -/
theorem finiteR_sub_mean (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    finiteR ρ eig hρ hρsum x - ∑ a, ρ a * eig a =
      ∑ a, ρ a * (finiteR ρ eig hρ hρsum x - eig a) ^ 2 /
        (finiteInverse ρ eig hρ hρsum x - eig a) := by
  let b := finiteInverse ρ eig hρ hρsum x
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hterm : ∀ a,
      ρ a * (b - 1 / x - eig a) ^ 2 / (b - eig a) =
        ρ a * (b - eig a) - (2 / x) * ρ a +
          (1 / x ^ 2) * (ρ a / (b - eig a)) := by
    intro a
    have hba : b - eig a ≠ 0 := (sub_pos.mpr (hs.1 a)).ne'
    field_simp [hx.ne', hba]
    ring
  simp only [finiteR, ite_eq_left hx]
  change b - 1 / x - ∑ a, ρ a * eig a =
    ∑ a, ρ a * (b - 1 / x - eig a) ^ 2 / (b - eig a)
  simp_rw [hterm, mul_sub]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, hρsum, one_mul, mul_one]
  change b - 1 / x - ∑ a, ρ a * eig a =
    b - ∑ a, ρ a * eig a - 2 / x + (1 / x ^ 2) * finiteResolvent ρ eig b
  rw [hs.2]
  field_simp
  ring

theorem mean_le_finiteR (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) :
    (∑ a, ρ a * eig a) ≤ finiteR ρ eig hρ hρsum x := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  apply sub_nonneg.mp
  rw [finiteR_sub_mean ρ eig hρ hρsum hx]
  exact Finset.sum_nonneg fun a _ => div_nonneg
    (mul_nonneg (hρ a).le (sq_nonneg _)) (sub_pos.mpr (hs.1 a)).le

/-- The uniform `O(K²x)` estimate from manuscript `gen:R-at-zero`. -/
theorem finiteR_sub_mean_le (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {K x : ℝ} (_hK : 0 ≤ K)
    (heig : ∀ a, |eig a| ≤ K) (hx : 0 < x) (hsmall : 4 * K * x ≤ 1) :
    finiteR ρ eig hρ hρsum x - ∑ a, ρ a * eig a ≤ 8 * K ^ 2 * x := by
  let b := finiteInverse ρ eig hρ hρsum x
  let r := finiteR ρ eig hρ hρsum x
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hr := finiteR_mem_interval ρ eig hρ hρsum
    (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x
  have hbx : x * b = x * r + 1 := by
    dsimp [b, r]
    simp only [finiteR, ite_eq_left hx]
    field_simp
    ring
  have hterm : ∀ a, ρ a * (r - eig a) ^ 2 / (b - eig a) ≤ ρ a * (8 * K ^ 2 * x) := by
    intro a
    have he := abs_le.mp (heig a)
    have hsq : (r - eig a) ^ 2 ≤ 4 * K ^ 2 := by
      have hlow : -2 * K ≤ r - eig a := by linarith [hr.1]
      have hupp : r - eig a ≤ 2 * K := by linarith [hr.2]
      have hprod := mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hupp)
      nlinarith
    have hden : 0 < b - eig a := sub_pos.mpr (hs.1 a)
    have hrecip : 1 / (b - eig a) ≤ 2 * x := by
      apply (div_le_iff₀ hden).mpr
      have hrlow : -K ≤ r := hr.1
      have hex : eig a ≤ K := he.2
      have hscaled := mul_le_mul_of_nonneg_left (show -2 * K ≤ r - eig a by linarith) hx.le
      nlinarith
    calc
      ρ a * (r - eig a) ^ 2 / (b - eig a) =
          ρ a * ((r - eig a) ^ 2 * (1 / (b - eig a))) := by ring
      _ ≤ ρ a * (4 * K ^ 2 * (2 * x)) := by
        apply mul_le_mul_of_nonneg_left _ (hρ a).le
        exact mul_le_mul hsq hrecip (one_div_pos.mpr hden).le (by positivity)
      _ = ρ a * (8 * K ^ 2 * x) := by ring
  rw [finiteR_sub_mean ρ eig hρ hρsum hx]
  calc
    (∑ a, ρ a * (r - eig a) ^ 2 / (b - eig a)) ≤
        ∑ a, ρ a * (8 * K ^ 2 * x) := Finset.sum_le_sum fun a _ => hterm a
    _ = 8 * K ^ 2 * x := by rw [← Finset.sum_mul, hρsum, one_mul]

theorem continuousAt_finiteR_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) :
    ContinuousAt (finiteR ρ eig hρ hρsum) 0 := by
  let K := 1 + ∑ a, |eig a|
  have hK : 0 < K := by
    have hsum : 0 ≤ ∑ a, |eig a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    dsimp [K]
    linarith
  have heig : ∀ a, |eig a| ≤ K := by
    intro a
    have hs : |eig a| ≤ ∑ a, |eig a| :=
      Finset.single_le_sum (f := fun a => |eig a|)
        (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
    dsimp [K]
    linarith
  have ht : Tendsto (fun x : ℝ => 8 * K ^ 2 * |x|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).const_mul (8 * K ^ 2)
  have hevent : ∀ᶠ x : ℝ in 𝓝 0,
      ‖finiteR ρ eig hρ hρsum x - ∑ a, ρ a * eig a‖ ≤ 8 * K ^ 2 * |x| := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / (4 * K) by positivity)] with x hxsmall
    rw [Real.norm_eq_abs]
    by_cases hx : 0 < x
    · have hsmall : 4 * K * x ≤ 1 := by
        have h := (lt_div_iff₀ (show (0 : ℝ) < 4 * K by positivity)).mp hxsmall
        nlinarith
      rw [abs_of_nonneg (sub_nonneg.mpr (mean_le_finiteR ρ eig hρ hρsum hx)), abs_of_pos hx]
      exact finiteR_sub_mean_le ρ eig hρ hρsum hK.le heig hx hsmall
    · simp only [finiteR, ite_eq_right hx, sub_self, abs_zero]
      positivity
  have hdiff := squeeze_zero_norm' hevent ht
  have hlim : Tendsto (finiteR ρ eig hρ hρsum) (𝓝 0) (𝓝 (∑ a, ρ a * eig a)) :=
    (tendsto_sub_nhds_zero_iff).mp hdiff
  simpa only [ContinuousAt, finiteR, lt_self_iff_false, ite_false] using hlim

end InvariantIsing

end

end OAI
