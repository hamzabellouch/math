import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

namespace OAI

namespace Erdos970

section

open MeasureTheory Set
open scoped BigOperators

namespace AdditiveLargeSieve

theorem endpoint_sample {f f' : ℝ → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (hderiv : ∀ x, HasDerivAt f (f' x) x) {a δ : ℝ} (hδ : 0 < δ) :
    δ * f a ≤ (∫ x in a..a + δ, f x) + δ * ∫ x in a..a + δ, |f' x| := by
  have hab : a ≤ a + δ := by linarith
  have hpoint (t : ℝ) (ht : t ∈ Icc a (a + δ)) :
      f a ≤ f t + ∫ x in a..a + δ, |f' x| := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hderiv x) (hf'.intervalIntegrable a t)
    have hnorm := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := f') ht.1
    have hmono := intervalIntegral.integral_mono_interval (μ := volume) (f := fun x => |f' x|)
      (le_refl a) ht.1 ht.2 (Filter.Eventually.of_forall fun x => abs_nonneg (f' x))
      (hf'.abs.intervalIntegrable a (a + δ))
    rw [hftc] at hnorm
    have := neg_le_abs (f t - f a)
    linarith
  have hint := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (μ := volume) (c := f a))
    ((hf.add continuous_const).intervalIntegrable a (a + δ)) hpoint
  simp only [Pi.add_apply] at hint
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const] at hint
  simpa only [add_sub_cancel_left, smul_eq_mul] using hint

theorem disjoint_sample_intervals {ι : Type*} {s : Finset ι} {t : ι → ℝ} {δ : ℝ}
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|) :
    Set.Pairwise (↑s) (fun i j => Disjoint (Ioc (t i) (t i + δ))
      (Ioc (t j) (t j + δ))) := by
  intro i hi j hj hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  have h := hsep i hi j hj hij
  rcases le_abs.mp h with h | h <;> linarith [hxi.1, hxi.2, hxj.1, hxj.2]

theorem sum_local_integrals_le {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    {δ L U : ℝ} (hδ : 0 < δ) (hLU : L ≤ U)
    (hinside : ∀ i ∈ s, L ≤ t i ∧ t i + δ ≤ U)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    {f : ℝ → ℝ} (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) :
    (∑ i ∈ s, ∫ x in t i..t i + δ, f x) ≤ ∫ x in L..U, f x := by
  have hle (i : ι) : t i ≤ t i + δ := by linarith
  simp_rw [intervalIntegral.integral_of_le (hle _)]
  rw [← integral_biUnion_finset s (fun _ _ => measurableSet_Ioc)
    (disjoint_sample_intervals hsep) (fun i _ => (hf.intervalIntegrable _ _).1),
    intervalIntegral.integral_of_le hLU]
  apply setIntegral_mono_set (hf.intervalIntegrable L U).1
    (Filter.Eventually.of_forall hpos)
  exact Filter.Eventually.of_forall fun x hx => by
    rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
    exact ⟨lt_of_le_of_lt (hinside i hi).1 hxi.1, hxi.2.trans (hinside i hi).2⟩

theorem separated_sampling {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    {δ L U : ℝ} (hδ : 0 < δ) (hLU : L ≤ U)
    (hinside : ∀ i ∈ s, L ≤ t i ∧ t i + δ ≤ U)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |t i - t j|)
    {f f' : ℝ → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (hderiv : ∀ x, HasDerivAt f (f' x) x) (hpos : ∀ x, 0 ≤ f x) :
    (∑ i ∈ s, f (t i)) ≤
      δ⁻¹ * (∫ x in L..U, f x) + ∫ x in L..U, |f' x| := by
  have hlocal := Finset.sum_le_sum (s := s) fun i _ => endpoint_sample hf hf' hderiv
    (a := t i) hδ
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at hlocal
  have hfbound := sum_local_integrals_le s t hδ hLU hinside hsep hf hpos
  have hdbound := sum_local_integrals_le s t hδ hLU hinside hsep hf'.abs
    (fun x => abs_nonneg (f' x))
  have hbound : δ * (∑ i ∈ s, f (t i)) ≤
      (∫ x in L..U, f x) + δ * ∫ x in L..U, |f' x| :=
    hlocal.trans (add_le_add hfbound (mul_le_mul_of_nonneg_left hdbound hδ.le))
  calc
    (∑ i ∈ s, f (t i)) ≤ ((∫ x in L..U, f x) +
        δ * ∫ x in L..U, |f' x|) / δ := (le_div_iff₀ hδ).2 (by simpa [mul_comm] using hbound)
    _ = _ := by field_simp

end AdditiveLargeSieve

end

end Erdos970

end OAI
