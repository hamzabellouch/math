import OAI.Analysis.MarkovType.FinitePowerIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace MarkovSuperreflexivity

variable {I Ω E F : Type*} [sectionFintypeI : Fintype I] [Fintype Ω]
  [NormedAddCommGroup E] [NormedAddCommGroup F]

noncomputable def finiteMoment (w : I → ℝ) (p : ℝ) (φ : I → E) : ℝ :=
  ∑ i, w i * ‖φ i‖ ^ p

noncomputable def finiteTail (ν : Ω → ℝ) (f : Ω → F) (t : ℝ) : ℝ :=
  ∑ ω, if t < ‖f ω‖ then ν ω else 0

noncomputable def largeCut (φ : I → E) (t : ℝ) : I → E :=
  fun i => if t < ‖φ i‖ then φ i else 0

noncomputable def smallCut (φ : I → E) (t : ℝ) : I → E :=
  fun i => if t < ‖φ i‖ then 0 else φ i

omit sectionFintypeI in
theorem largeCut_add_smallCut [Fintype I] (φ : I → E) (t : ℝ) :
    largeCut φ t + smallCut φ t = φ := by
  funext i
  simp only [Pi.add_apply, largeCut, smallCut]
  split_ifs <;> simp

theorem finiteTail_add_le (ν : Ω → ℝ) (hν : ∀ ω, 0 ≤ ν ω)
    (f g : Ω → F) (t : ℝ) :
    finiteTail ν (f + g) t ≤ finiteTail ν f (t / 2) + finiteTail ν g (t / 2) := by
  classical
  unfold finiteTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  change (if t < ‖f ω + g ω‖ then ν ω else 0) ≤
    (if t / 2 < ‖f ω‖ then ν ω else 0) +
      (if t / 2 < ‖g ω‖ then ν ω else 0)
  by_cases h : t < ‖f ω + g ω‖
  · have hpart : t / 2 < ‖f ω‖ ∨ t / 2 < ‖g ω‖ := by
      by_cases hf : t / 2 < ‖f ω‖
      · exact Or.inl hf
      by_cases hg : t / 2 < ‖g ω‖
      · exact Or.inr hg
      have hf' := le_of_not_gt hf
      have hg' := le_of_not_gt hg
      have htriangle := norm_add_le (f ω) (g ω)
      exfalso
      linarith
    rcases hpart with hf | hg
    · simp only [ite_eq_left h, ite_eq_left hf]
      split_ifs <;> linarith [hν ω]
    · simp only [ite_eq_left h, ite_eq_left hg]
      split_ifs <;> linarith [hν ω]
  · simp only [ite_eq_right h]
    split_ifs <;> linarith [hν ω]

section Linear

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

def FiniteWeakType (w : I → ℝ) (ν : Ω → ℝ)
    (T : (I → E) →ₗ[ℝ] (Ω → F)) (p A : ℝ) : Prop :=
  ∀ (φ : I → E) (t : ℝ), 0 < t →
    finiteTail ν (T φ) t ≤ (A / t) ^ p * finiteMoment w p φ

theorem finiteTail_split_weak (w : I → ℝ) (ν : Ω → ℝ) (hν : ∀ ω, 0 ≤ ν ω)
    (T : (I → E) →ₗ[ℝ] (Ω → F)) {p₀ p₁ A₀ A₁ : ℝ}
    (h₀ : FiniteWeakType w ν T p₀ A₀) (h₁ : FiniteWeakType w ν T p₁ A₁)
    (φ : I → E) {t : ℝ} (ht : 0 < t) :
    finiteTail ν (T φ) t ≤
      (A₀ / (t / 2)) ^ p₀ * finiteMoment w p₀ (largeCut φ t) +
      (A₁ / (t / 2)) ^ p₁ * finiteMoment w p₁ (smallCut φ t) := by
  have hsplit : T φ = T (largeCut φ t) + T (smallCut φ t) := by
    rw [← map_add, largeCut_add_smallCut]
  rw [hsplit]
  exact (finiteTail_add_le ν hν _ _ t).trans
    (add_le_add (h₀ _ _ (half_pos ht)) (h₁ _ _ (half_pos ht)))

end Linear

noncomputable def largeMomentKernel (p q r t : ℝ) : ℝ :=
  r ^ q * lowerPowerKernel (p - q) r t

noncomputable def smallMomentKernel (p q r t : ℝ) : ℝ :=
  r ^ q * upperPowerKernel (q - p) r t

theorem integrable_largeMomentKernel {p q r : ℝ} (hqp : q < p) (hr : 0 ≤ r) :
    Integrable (largeMomentKernel p q r) :=
  (integrable_lowerPowerKernel (sub_pos.mpr hqp) hr).const_mul _

theorem integral_largeMomentKernel {p q r : ℝ}
    (hp : 0 < p) (hqp : q < p) (hr : 0 ≤ r) :
    (∫ t, largeMomentKernel p q r t) = r ^ p / (p - q) := by
  simp only [largeMomentKernel, integral_const_mul,
    integral_lowerPowerKernel (sub_pos.mpr hqp) hr]
  have hsum : q + (p - q) ≠ 0 := by linarith
  rw [← mul_div_assoc, ← Real.rpow_add' hr hsum]
  congr 1
  congr 1
  ring

theorem integrable_smallMomentKernel {p q r : ℝ}
    (hq : 0 < q) (hpq : p < q) (hr : 0 ≤ r) :
    Integrable (smallMomentKernel p q r) := by
  by_cases hr₀ : r = 0
  · subst r
    have hz : smallMomentKernel p q 0 = fun _ : ℝ => 0 := by
      funext t
      simp only [smallMomentKernel, Real.zero_rpow hq.ne', zero_mul]
    rw [hz]
    exact integrable_zero ℝ ℝ volume
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr₀)
  exact (integrable_upperPowerKernel (sub_pos.mpr hpq) hrpos).const_mul _

theorem integral_smallMomentKernel {p q r : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p < q) (hr : 0 ≤ r) :
    (∫ t, smallMomentKernel p q r t) = r ^ p / (q - p) := by
  by_cases hr₀ : r = 0
  · simp [smallMomentKernel, hr₀, Real.zero_rpow hq.ne', Real.zero_rpow hp.ne']
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr₀)
  simp only [smallMomentKernel, integral_const_mul,
    integral_upperPowerKernel (sub_pos.mpr hpq) hrpos]
  rw [← mul_div_assoc, ← Real.rpow_add hrpos]
  congr 1
  congr 1
  ring

noncomputable def finiteLayerKernel (ν : Ω → ℝ) (p : ℝ) (f : Ω → F) (t : ℝ) : ℝ :=
  p * ∑ ω, ν ω * lowerPowerKernel p ‖f ω‖ t

theorem integrable_finiteLayerKernel (ν : Ω → ℝ) {p : ℝ} (hp : 0 < p) (f : Ω → F) :
    Integrable (finiteLayerKernel ν p f) :=
  (integrable_finsetSum _ (fun ω _ =>
    (integrable_lowerPowerKernel hp (norm_nonneg (f ω))).const_mul (ν ω))).const_mul p

theorem integral_finiteLayerKernel (ν : Ω → ℝ) {p : ℝ} (hp : 0 < p) (f : Ω → F) :
    (∫ t, finiteLayerKernel ν p f t) = finiteMoment ν p f := by
  classical
  change (∫ t : ℝ, p * ∑ ω, ν ω * lowerPowerKernel p ‖f ω‖ t) = finiteMoment ν p f
  rw [integral_const_mul, integral_finsetSum _ (fun ω _ =>
    (integrable_lowerPowerKernel hp (norm_nonneg (f ω))).const_mul (ν ω))]
  simp_rw [integral_const_mul, integral_lowerPowerKernel hp (norm_nonneg _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  field_simp [hp.ne']

theorem finiteLayerKernel_eq_of_pos (ν : Ω → ℝ) (p : ℝ) (f : Ω → F)
    {t : ℝ} (ht : 0 < t) :
    finiteLayerKernel ν p f t = p * t ^ (p - 1) * finiteTail ν f t := by
  classical
  simp only [finiteLayerKernel, finiteTail, lowerPowerKernel, ht, true_and]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> ring

noncomputable def finiteLargeKernel (w : I → ℝ) (p q : ℝ) (φ : I → E) (t : ℝ) : ℝ :=
  ∑ i, w i * largeMomentKernel p q ‖φ i‖ t

noncomputable def finiteSmallKernel (w : I → ℝ) (p q : ℝ) (φ : I → E) (t : ℝ) : ℝ :=
  ∑ i, w i * smallMomentKernel p q ‖φ i‖ t

theorem integrable_finiteLargeKernel (w : I → ℝ) {p q : ℝ}
    (hqp : q < p) (φ : I → E) : Integrable (finiteLargeKernel w p q φ) :=
  integrable_finsetSum _ (fun i _ =>
    (integrable_largeMomentKernel hqp (norm_nonneg (φ i))).const_mul (w i))

theorem integrable_finiteSmallKernel (w : I → ℝ) {p q : ℝ}
    (hq : 0 < q) (hpq : p < q) (φ : I → E) : Integrable (finiteSmallKernel w p q φ) :=
  integrable_finsetSum _ (fun i _ =>
    (integrable_smallMomentKernel hq hpq (norm_nonneg (φ i))).const_mul (w i))

theorem integral_finiteLargeKernel (w : I → ℝ) {p q : ℝ}
    (hp : 0 < p) (hqp : q < p) (φ : I → E) :
    (∫ t, finiteLargeKernel w p q φ t) = finiteMoment w p φ / (p - q) := by
  classical
  change (∫ t : ℝ, ∑ i, w i * largeMomentKernel p q ‖φ i‖ t) =
    finiteMoment w p φ / (p - q)
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_largeMomentKernel hqp (norm_nonneg (φ i))).const_mul (w i))]
  simp_rw [integral_const_mul, integral_largeMomentKernel hp hqp (norm_nonneg _)]
  simp only [finiteMoment, Finset.sum_div, mul_div_assoc]

theorem integral_finiteSmallKernel (w : I → ℝ) {p q : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hpq : p < q) (φ : I → E) :
    (∫ t, finiteSmallKernel w p q φ t) = finiteMoment w p φ / (q - p) := by
  classical
  change (∫ t : ℝ, ∑ i, w i * smallMomentKernel p q ‖φ i‖ t) =
    finiteMoment w p φ / (q - p)
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_smallMomentKernel hq hpq (norm_nonneg (φ i))).const_mul (w i))]
  simp_rw [integral_const_mul, integral_smallMomentKernel hp hq hpq (norm_nonneg _)]
  simp only [finiteMoment, Finset.sum_div, mul_div_assoc]

theorem weakThresholdFactor {A t : ℝ} (hA : 0 ≤ A) (ht : 0 < t) (q : ℝ) :
    (A / (t / 2)) ^ q = (2 * A) ^ q * t ^ (-q) := by
  have heq : A / (t / 2) = (2 * A) / t := by field_simp [ht.ne']
  rw [heq, Real.div_rpow (mul_nonneg (by norm_num) hA) ht.le,
    Real.rpow_neg ht.le, div_eq_mul_inv]

theorem largeCut_weighted_kernel (w : I → ℝ) (φ : I → E) (p : ℝ)
    {q A t : ℝ} (hq : 0 < q) (hA : 0 ≤ A) (ht : 0 < t) :
    t ^ (p - 1) * ((A / (t / 2)) ^ q * finiteMoment w q (largeCut φ t)) =
      (2 * A) ^ q * finiteLargeKernel w p q φ t := by
  classical
  have hpows : t ^ (p - q - 1) = t ^ (p - 1) * t ^ (-q) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rw [weakThresholdFactor hA ht q]
  simp only [finiteMoment, finiteLargeKernel]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : t < ‖φ i‖
  · simp only [largeCut, largeMomentKernel, lowerPowerKernel,
      ht, hi, and_self, ite_true]
    rw [hpows]
    ring
  · simp [largeCut, hi, largeMomentKernel, lowerPowerKernel, ht, Real.zero_rpow hq.ne']

theorem smallCut_weighted_kernel (w : I → ℝ) (φ : I → E) (p : ℝ)
    {q A t : ℝ} (hq : 0 < q) (hA : 0 ≤ A) (ht : 0 < t) :
    t ^ (p - 1) * ((A / (t / 2)) ^ q * finiteMoment w q (smallCut φ t)) =
      (2 * A) ^ q * finiteSmallKernel w p q φ t := by
  classical
  have hpows : t ^ (p - q - 1) = t ^ (p - 1) * t ^ (-q) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rw [weakThresholdFactor hA ht q]
  simp only [finiteMoment, finiteSmallKernel]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : t < ‖φ i‖
  · simp [smallCut, hi, smallMomentKernel, upperPowerKernel, ht,
      not_le.mpr hi, Real.zero_rpow hq.ne']
  · have hir : ‖φ i‖ ≤ t := le_of_not_gt hi
    simp only [smallCut, ite_eq_right hi, smallMomentKernel, upperPowerKernel,
      ht, hir, and_self, ite_true, neg_sub]
    rw [hpows]
    ring

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

theorem finiteLayerKernel_le (w : I → ℝ) (ν : Ω → ℝ) (hν : ∀ ω, 0 ≤ ν ω)
    (T : (I → E) →ₗ[ℝ] (Ω → F)) {p₀ p p₁ A₀ A₁ : ℝ}
    (hp₀ : 0 < p₀) (hp : 0 < p) (hp₁ : 0 < p₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (h₀ : FiniteWeakType w ν T p₀ A₀) (h₁ : FiniteWeakType w ν T p₁ A₁)
    (φ : I → E) (t : ℝ) :
    finiteLayerKernel ν p (T φ) t ≤
      p * (2 * A₀) ^ p₀ * finiteLargeKernel w p p₀ φ t +
      p * (2 * A₁) ^ p₁ * finiteSmallKernel w p p₁ φ t := by
  by_cases ht : 0 < t
  · rw [finiteLayerKernel_eq_of_pos ν p (T φ) ht]
    calc
      p * t ^ (p - 1) * finiteTail ν (T φ) t ≤
          p * t ^ (p - 1) *
            ((A₀ / (t / 2)) ^ p₀ * finiteMoment w p₀ (largeCut φ t) +
             (A₁ / (t / 2)) ^ p₁ * finiteMoment w p₁ (smallCut φ t)) :=
        mul_le_mul_of_nonneg_left (finiteTail_split_weak w ν hν T h₀ h₁ φ ht)
          (mul_nonneg hp.le (Real.rpow_nonneg ht.le _))
      _ = p * (t ^ (p - 1) *
            ((A₀ / (t / 2)) ^ p₀ * finiteMoment w p₀ (largeCut φ t))) +
          p * (t ^ (p - 1) *
            ((A₁ / (t / 2)) ^ p₁ * finiteMoment w p₁ (smallCut φ t))) := by ring
      _ = p * (2 * A₀) ^ p₀ * finiteLargeKernel w p p₀ φ t +
          p * (2 * A₁) ^ p₁ * finiteSmallKernel w p p₁ φ t := by
        rw [largeCut_weighted_kernel w φ p hp₀ hA₀ ht,
          smallCut_weighted_kernel w φ p hp₁ hA₁ ht]
        ring
  · simp [finiteLayerKernel, finiteLargeKernel, finiteSmallKernel,
      largeMomentKernel, smallMomentKernel, lowerPowerKernel, upperPowerKernel, ht]

theorem finite_marcinkiewicz
    (w : I → ℝ) (_hw : ∀ i, 0 ≤ w i) (ν : Ω → ℝ) (hν : ∀ ω, 0 ≤ ν ω)
    (T : (I → E) →ₗ[ℝ] (Ω → F)) {p₀ p p₁ A₀ A₁ : ℝ}
    (hp₀ : 0 < p₀) (hp₀p : p₀ < p) (hpp₁ : p < p₁)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (h₀ : FiniteWeakType w ν T p₀ A₀) (h₁ : FiniteWeakType w ν T p₁ A₁)
    (φ : I → E) :
    finiteMoment ν p (T φ) ≤
      (p * ((2 * A₀) ^ p₀ / (p - p₀) + (2 * A₁) ^ p₁ / (p₁ - p))) *
        finiteMoment w p φ := by
  have hp : 0 < p := hp₀.trans hp₀p
  have hp₁ : 0 < p₁ := hp.trans hpp₁
  have hlo := integrable_finiteLargeKernel w hp₀p φ
  have hhi := integrable_finiteSmallKernel w hp₁ hpp₁ φ
  have hbound := integral_mono (integrable_finiteLayerKernel ν hp (T φ))
    ((hlo.const_mul (p * (2 * A₀) ^ p₀)).add
      (hhi.const_mul (p * (2 * A₁) ^ p₁)))
    (finiteLayerKernel_le w ν hν T hp₀ hp hp₁ hA₀ hA₁ h₀ h₁ φ)
  change (∫ t : ℝ, finiteLayerKernel ν p (T φ) t) ≤
    ∫ t : ℝ, p * (2 * A₀) ^ p₀ * finiteLargeKernel w p p₀ φ t +
      p * (2 * A₁) ^ p₁ * finiteSmallKernel w p p₁ φ t at hbound
  rw [integral_finiteLayerKernel ν hp (T φ),
    integral_add (hlo.const_mul _) (hhi.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_finiteLargeKernel w hp hp₀p φ,
    integral_finiteSmallKernel w hp hp₁ hpp₁ φ] at hbound
  convert hbound using 1 ; ring

end MarkovSuperreflexivity

end OAI
