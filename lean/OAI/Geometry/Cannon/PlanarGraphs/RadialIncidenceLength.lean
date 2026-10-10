import Mathlib

namespace OAI

section
section
section
section
section
open MeasureTheory Set
open scoped BigOperators

namespace CannonRadialEnergy

attribute [local instance] Classical.propDecidable

theorem radial_incidence_length {ι : Type*} [Fintype ι]
    {a b A : ℝ} (hab : a ≤ b) (hA : 0 ≤ A)
    (d r w : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (hw : ∀ i, 0 ≤ w i)
    (hcover : ∀ t ∈ Icc a b,
      1 ≤ ∑ i, if |t - d i| ≤ A * r i then w i else 0) :
    b - a ≤ 2 * A * ∑ i, r i * w i := by
  classical
  let J : ι → Set ℝ := fun i => Icc (d i - A * r i) (d i + A * r i)
  let f : ι → ℝ → ℝ := fun i => (J i).indicator (fun _ => w i)
  have hf (i : ι) : Integrable (f i) volume := by
    apply (integrable_indicator_iff measurableSet_Icc).2
    exact integrable_const (w i)
  have hg : Integrable ((Icc a b).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
    apply (integrable_indicator_iff measurableSet_Icc).2
    exact integrable_const 1
  have hiff (i : ι) (t : ℝ) : t ∈ J i ↔ |t - d i| ≤ A * r i := by
    simp only [J, mem_Icc, abs_le]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  have he (t : ℝ) : (∑ i, f i t) =
      ∑ i, if |t-d i| ≤ A*r i then w i else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [f, indicator_apply, hiff]
  have hnonneg (i : ι) (t : ℝ) : 0 ≤ f i t := by
    exact indicator_nonneg (fun _ _ => hw i) t
  have hpoint (t : ℝ) : (Icc a b).indicator (fun _ : ℝ => (1 : ℝ)) t ≤ ∑ i, f i t := by
    by_cases ht : t ∈ Icc a b
    · simpa only [indicator_of_mem ht, he] using hcover t ht
    · rw [indicator_of_notMem ht]
      exact Finset.sum_nonneg (fun i _ => hnonneg i t)
  have hbound := integral_mono hg (integrable_finsetSum _ (fun i _ => hf i)) hpoint
  have hint (i : ι) : (∫ t, f i t) = 2 * A * r i * w i := by
    have hh : d i-A*r i ≤ d i+A*r i := by nlinarith [mul_nonneg hA (hr i)]
    dsimp [f,J]
    rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le hh,
      smul_eq_mul]
    ring
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le hab,
    smul_eq_mul, mul_one, integral_finsetSum _ (fun i _ => hf i)] at hbound
  simp only [hint] at hbound
  calc
    b-a ≤ ∑ i, 2*A*r i*w i := hbound
    _ = 2*A*∑ i, r i*w i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem radial_incidence_energy {ι : Type*} [Fintype ι]
    {a b A : ℝ} (hab : a ≤ b) (hA : 0 ≤ A)
    (d r w : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (hw : ∀ i, 0 ≤ w i)
    (hcover : ∀ t ∈ Icc a b,
      1 ≤ ∑ i, if |t - d i| ≤ A * r i then w i else 0) :
    (b - a)^2 ≤ 4 * A^2 * (∑ i, r i^2) * ∑ i, w i^2 := by
  have hh := radial_incidence_length hab hA d r w hr hw hcover
  have hsq : (b-a)^2 ≤ (2*A*(∑ i, r i*w i))^2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr hab) hh 2
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ r w
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4*A^2 by positivity)
  calc
    (b-a)^2 ≤ (2*A*(∑ i, r i*w i))^2 := hsq
    _ = 4*A^2*(∑ i, r i*w i)^2 := by ring
    _ ≤ 4*A^2*((∑ i, r i^2)*(∑ i, w i^2)) := hm
    _ = _ := by ring

end CannonRadialEnergy

end
end
end
end
end

end OAI
