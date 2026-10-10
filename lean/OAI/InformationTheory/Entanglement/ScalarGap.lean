import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace SecretKey
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
lemma sqrt_memLp_two {p : Ω → ℝ} (hp : Integrable p μ) (hn : ∀ x, 0≤p x) :
    MemLp (fun x => Real.sqrt (p x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq hp.1.aemeasurable.sqrt.aestronglyMeasurable).mpr
  simpa only [Real.sq_sqrt (hn _)] using hp
lemma sqrt_product_integrable {p q : Ω → ℝ} (hp : Integrable p μ) (hq : Integrable q μ)
    (hn : ∀ x, 0≤p x) (hm : ∀ x, 0≤q x) : Integrable (fun x => Real.sqrt (p x*q x)) μ := by
  have hi := (sqrt_memLp_two hp hn).integrable_mul (sqrt_memLp_two hq hm)
  simpa only [Pi.mul_def,Real.sqrt_mul (hn _)] using hi
lemma integral_sqrt_product_le {p q : Ω → ℝ} (hp : Integrable p μ) (hq : Integrable q μ)
    (hn : ∀ x, 0≤p x) (hm : ∀ x, 0≤q x) :
    (∫ x, Real.sqrt (p x*q x) ∂μ) ≤ Real.sqrt ((∫ x, p x ∂μ)*(∫ x, q x ∂μ)) := by
  have hh : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hh
    (f := fun x => Real.sqrt (p x)) (g := fun x => Real.sqrt (q x))
    (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _)
    (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _)
    (by simpa using sqrt_memLp_two hp hn) (by simpa using sqrt_memLp_two hq hm)
  simpa only [Real.rpow_two,Real.sq_sqrt (hn _),Real.sq_sqrt (hm _),
    ← Real.sqrt_eq_rpow,Real.sqrt_mul (hn _),
    Real.sqrt_mul (integral_nonneg hn)] using h

lemma two_sqrt_products_le {a b c d : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) :
    Real.sqrt (a*b)+Real.sqrt (c*d) ≤ Real.sqrt ((a+d)*(b+c)) := by
  have h := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin 2))
    (f := ![a,d]) (g := ![b,c]) (by intro i; fin_cases i <;> assumption)
    (by intro i; fin_cases i <;> assumption)
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,← Real.sqrt_mul ha,← Real.sqrt_mul hd,
    ← Real.sqrt_mul (add_nonneg ha hd),mul_comm d c] using h
lemma two_sqrt_le_add {a b : ℝ} (ha : 0≤a) (hb : 0≤b) : 2*Real.sqrt (a*b)≤a+b := by
  have hs := Real.sq_sqrt (mul_nonneg ha hb)
  have hn := Real.sqrt_nonneg (a*b)
  nlinarith [sq_nonneg (a-b)]

theorem scalar_secret_bit_gap {a b c d q η : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d)
    (hs : a+b+c+d=1) (he : b+c≤η/2) (hq : q≤η-(b+c))
    (hf : (a+d-q)/2≤Real.sqrt (a*b)+Real.sqrt (c*d)+2*Real.sqrt (b*c)) :
    1/5≤η := by
  have hu := add_le_add (two_sqrt_products_le ha hb hc hd) (two_sqrt_le_add hb hc)
  have hlow : (1-η)/2≤Real.sqrt ((b+c)*(1-(b+c)))+(b+c) := by
    have hx : (a+d)*(b+c)=(b+c)*(1-(b+c)) := by nlinarith [hs]
    rw [hx] at hu
    linarith
  by_contra hh
  have heta : η<1/5 := lt_of_not_ge hh
  have en : 0≤b+c := add_nonneg hb hc
  have eb : b+c<1/10 := by linarith
  have eone : 0≤1-(b+c) := by linarith
  have hr := Real.sq_sqrt (mul_nonneg en eone)
  have sr := Real.sqrt_nonneg ((b+c)*(1-(b+c)))
  have hprod : (b+c)*(1-(b+c))≤9/100 := by
    nlinarith [mul_nonneg en (by linarith : 0≤1/10-(b+c))]
  have hsqrt : Real.sqrt ((b+c)*(1-(b+c)))≤3/10 := by nlinarith
  linarith
end SecretKey

end

end OAI
