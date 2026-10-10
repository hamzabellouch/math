import OAI.Probability.Renewal.Laplace
import OAI.Probability.Renewal.Fourier

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace HoneycombLocal

def pairLaw (p q : PMF ℕ) : PMF (ℕ × ℕ) :=
  ⟨fun z => p z.1 * q z.2, ENNReal.summable.hasSum_iff.mpr (by
    rw [ENNReal.tsum_prod']
    simp only [ENNReal.tsum_mul_left, q.tsum_coe, mul_one, p.tsum_coe])⟩

lemma pairLaw_apply (p q : PMF ℕ) (z : ℕ × ℕ) : pairLaw p q z = p z.1 * q z.2 := rfl

lemma pairLaw_toMeasure (p q : PMF ℕ) :
    (pairLaw p q).toMeasure = p.toMeasure.prod q.toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨j, l⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), pairLaw_apply]
  have hs : ({(j, l)} : Set (ℕ × ℕ)) = {j} ×ˢ {l} := by ext z; simp
  rw [hs, Measure.prod_prod, p.toMeasure_apply_singleton _ (measurableSet_singleton _),
    q.toMeasure_apply_singleton _ (measurableSet_singleton _)]

lemma sumLaw_succ_map (p : PMF ℕ) (k : ℕ) :
    sumLaw p (k + 1) = (pairLaw p (sumLaw p k)).map (fun z => z.1 + z.2) := by
  classical
  ext m
  simp only [sumLaw, PMF.bind_apply, PMF.map_apply, pairLaw_apply]
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro j
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro l
  split_ifs <;> simp

lemma sumLaw_transform {𝕂 : Type*} [RCLike 𝕂] (p : PMF ℕ) (k : ℕ) (F : ℕ → 𝕂)
    (h0 : F 0 = 1) (hmul : ∀ j l, F (j + l) = F j * F l) :
    (∫ j, F j ∂(sumLaw p k).toMeasure) = (∫ j, F j ∂p.toMeasure) ^ k := by
  induction k with
  | zero => simpa [sumLaw, PMF.toMeasure_pure] using h0
  | succ k hk =>
    rw [sumLaw_succ_map, ← PMF.toMeasure_map _ _ Measurable.of_discrete]
    rw [integral_map Measurable.of_discrete.aemeasurable Measurable.of_discrete.aestronglyMeasurable,
      pairLaw_toMeasure]
    simp_rw [hmul]
    rw [integral_prod_mul F F, hk, pow_succ, mul_comm]

lemma latticeChar_sumLaw (p : PMF ℕ) (k : ℕ) (t : ℝ) :
    latticeChar (sumLaw p k) t = latticeChar p t ^ k := by
  apply sumLaw_transform
  · simp
  · intro j l
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

lemma laplace_sumLaw (p : PMF ℕ) (k : ℕ) (u : ℝ) :
    laplace (sumLaw p k) u = laplace p u ^ k := by
  apply sumLaw_transform
  · simp
  · intro j l
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring

lemma sumLaw_inversion (p : PMF ℕ) (k m : ℕ) :
    (∫ t : ℝ in -Real.pi..Real.pi,
      latticeChar p t ^ k * Complex.exp (-((m : ℝ) * t : ℝ) * Complex.I)) =
      (2 * Real.pi : ℂ) * ((sumLaw p k m).toReal : ℂ) := by
  simpa only [latticeChar_sumLaw] using lattice_inversion (sumLaw p k) m

lemma tail_from_laplace (p : PMF ℕ) {t : ℝ} (ht : 0 < t) :
    (1 - Real.exp (-1)) * p.toMeasure.real {j | t < (j : ℝ)} ≤
      1 - laplace p t⁻¹ := by
  let s : Set ℕ := {j | t < (j : ℝ)}
  have hf := (integrable_const (1 - Real.exp (-1))).indicator
    (μ := p.toMeasure) (s := s) MeasurableSet.of_discrete
  have h := integral_mono hf (integrable_deficit p (inv_nonneg.mpr ht.le)) (fun j => ?_)
  · rw [integral_indicator_const _ MeasurableSet.of_discrete, deficit_integral p (inv_nonneg.mpr ht.le)] at h
    simpa only [smul_eq_mul, mul_comm] using h
  · by_cases hj : j ∈ s
    · rw [Set.indicator_of_mem hj]
      apply sub_le_sub_left
      apply Real.exp_le_exp.mpr
      dsimp [s] at hj
      have hr : 1 ≤ t⁻¹ * (j : ℝ) := by
        rw [inv_mul_eq_div, le_div_iff₀ ht]
        simpa using hj.le
      nlinarith
    · rw [Set.indicator_of_notMem hj]
      have hexp : Real.exp (-t⁻¹ * (j : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (inv_nonneg.mpr ht.le)) (Nat.cast_nonneg _))
      linarith

lemma one_sub_pow_le_nat_mul {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (k : ℕ) :
    1 - z ^ k ≤ k * (1 - z) := by
  induction k with
  | zero => simp
  | succ k hk =>
    have hp := pow_le_one₀ hz hz1 (n := k)
    have hn : 0 ≤ 1 - z := sub_nonneg.mpr hz1
    have hmul := mul_le_mul_of_nonneg_right hp hn
    rw [pow_succ]
    push_cast
    nlinarith

lemma sum_tail_power (p : PMF ℕ) {a : ℝ} (ha : 0 < a ∧ a < 1)
    (hpower : BoundedPowerInput p a) :
    ∃ D > (0 : ℝ), ∀ k : ℕ, 1 ≤ k → ∀ t : ℝ, 0 < t →
      (sumLaw p k).toMeasure.real {j | t < (j : ℝ)} ≤ D * k * t ^ (-a) := by
  rcases hpower with ⟨c, hc, C, hC, x₀, hx₀, htail, hLap⟩
  let w : ℝ := 1 - Real.exp (-1)
  have hw : 0 < w := by dsimp [w]; have := Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0); linarith
  let D := max (C / w) (x₀ ^ a)
  have hD : 0 < D := (div_pos hC hw).trans_le (le_max_left _ _)
  refine ⟨D, hD, ?_⟩
  intro k hk t ht
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have htpa : 0 ≤ t ^ (-a) := Real.rpow_nonneg ht.le _
  by_cases htx : x₀ ≤ t
  · have hsmall : t⁻¹ ≤ x₀⁻¹ := (inv_le_inv₀ ht hx₀).mpr htx
    have hlap := (hLap t⁻¹ (inv_pos.mpr ht) hsmall).2
    have hpow := one_sub_pow_le_nat_mul (laplace_pos p (inv_nonneg.mpr ht.le)).le
      (laplace_le_one p (inv_nonneg.mpr ht.le)) k
    have hmark := tail_from_laplace (sumLaw p k) ht
    rw [laplace_sumLaw] at hmark
    have hmulti := mul_le_mul_of_nonneg_left hlap hk0
    have hid : (t⁻¹) ^ a = t ^ (-a) := by rw [Real.inv_rpow ht.le, Real.rpow_neg ht.le]
    rw [hid] at hmulti
    have hbound : w * (sumLaw p k).toMeasure.real {j | t < (j : ℝ)} ≤ k * C * t ^ (-a) := by
      dsimp [w]; nlinarith
    have hcD : C ≤ D * w := (div_le_iff₀ hw).mp (le_max_left _ _)
    calc
      (sumLaw p k).toMeasure.real {j | t < (j : ℝ)} ≤ (k * C * t ^ (-a)) / w := by
        apply (le_div_iff₀ hw).mpr
        simpa only [mul_comm] using hbound
      _ ≤ (k * (D * w) * t ^ (-a)) / w := by gcongr
      _ = D * k * t ^ (-a) := by field_simp
  · have htX : t ≤ x₀ := (lt_of_not_ge htx).le
    have htpow : t ^ a ≤ x₀ ^ a := Real.rpow_le_rpow ht.le htX ha.1.le
    have hpos : 0 < t ^ a := Real.rpow_pos_of_pos ht a
    have hpowid : t ^ a * t ^ (-a) = 1 := by
      rw [Real.rpow_neg ht.le, mul_inv_cancel₀ hpos.ne']
    have hconst : x₀ ^ a ≤ D * k := by
      have := le_max_right (C / w) (x₀ ^ a)
      change x₀ ^ a ≤ D at this
      nlinarith
    calc
      (sumLaw p k).toMeasure.real {j | t < (j : ℝ)} ≤ 1 := measureReal_le_one
      _ = t ^ a * t ^ (-a) := hpowid.symm
      _ ≤ D * k * t ^ (-a) := mul_le_mul_of_nonneg_right (htpow.trans hconst) htpa

end HoneycombLocal

end

end OAI
