import OAI.NumberTheory.JointDickman.Counting.ShortIntervalConsequences
import OAI.NumberTheory.JointDickman.Counting.ComplexShortIntervalConsequences

namespace OAI

/-! # Finite complex combinations of nonprincipal short averages -/
namespace JointDickman.PublishedInputs
open Finset Filter MeasureTheory
open scoped Topology

theorem measurable_complexShortAverage (f : ArithmeticFunction ℂ) (H : ℝ) :
    Measurable (complexShortAverage f H) := by
  have hm : Measurable (fun p : ℕ × ℕ => ∑ n ∈ Ioc p.1 p.2, f n) := measurable_of_countable _
  exact (hm.comp (Nat.measurable_floor.prodMk
    (measurable_id.add_const H).nat_floor)).div_const (H : ℂ)

theorem norm_complexShortAverage_le (f : ArithmeticFunction ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {H z b : ℝ} (hH : 0 < H) (hz : z ≤ b) :
    ‖complexShortAverage f H z‖ ≤ (⌊b+H⌋₊ : ℝ)/H := by
  rw [complexShortAverage,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hH]
  apply div_le_div_of_nonneg_right _ hH.le
  calc
    _ ≤ ∑ n ∈ Ioc ⌊z⌋₊ ⌊z+H⌋₊, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc ⌊z⌋₊ ⌊z+H⌋₊, (1 : ℝ) := sum_le_sum (fun n _ => hf n)
    _ = ((Ioc ⌊z⌋₊ ⌊z+H⌋₊).card : ℝ) := by simp
    _ ≤ (⌊b+H⌋₊ : ℝ) := by
      exact_mod_cast (show (Ioc ⌊z⌋₊ ⌊z+H⌋₊).card ≤ ⌊b+H⌋₊ from by
        simpa only [Nat.card_Ioc] using (Nat.sub_le ⌊z+H⌋₊ ⌊z⌋₊).trans
          (Nat.floor_mono (by linarith : z+H ≤ b+H)))

theorem complexShortAverage_sq_integrable (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {H : ℝ} (hH : 0 < H) (a b : ℝ) :
    IntervalIntegrable (fun z => ‖complexShortAverage f H z‖^2) volume a b := by
  let K : ℝ := (⌊max a b+H⌋₊ : ℝ)/H
  refine (intervalIntegrable_const (c := K^2)).mono_fun'
    (((measurable_complexShortAverage f H).norm.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with z hz
  have hh := norm_complexShortAverage_le f hf hH hz.2
  simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using
    pow_le_pow_left₀ (norm_nonneg _) hh 2

noncomputable def complexFiniteShort {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (f : ι → ArithmeticFunction ℂ) (H z : ℝ) : ℂ :=
  ∑ i ∈ S, c i*complexShortAverage (f i) H z

theorem complexFiniteShort_norm_sq_le {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (f : ι → ArithmeticFunction ℂ) (H z : ℝ) :
    ‖complexFiniteShort S c f H z‖^2 ≤
      (∑ i ∈ S, ‖c i‖^2)*(∑ i ∈ S, ‖complexShortAverage (f i) H z‖^2) := by
  have hn : ‖complexFiniteShort S c f H z‖ ≤ ∑ i ∈ S, ‖c i‖*‖complexShortAverage (f i) H z‖ := by
    simpa only [complexFiniteShort,norm_mul] using norm_sum_le S (fun i => c i*complexShortAverage (f i) H z)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (sum_mul_sq_le_sq_mul_sq S (fun i => ‖c i‖) (fun i => ‖complexShortAverage (f i) H z‖))

theorem complexFiniteShort_energy_le {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (f : ι → ArithmeticFunction ℂ) (hf : ∀ i ∈ S, ∀ n, ‖f i n‖ ≤ 1)
    {H X : ℝ} (hH : 0 < H) (hX : 0 < X) :
    (1/X)*(∫ z in X..2*X, ‖complexFiniteShort S c f H z‖^2) ≤
      (∑ i ∈ S, ‖c i‖^2)*∑ i ∈ S, (1/X)*(∫ z in X..2*X, ‖complexShortAverage (f i) H z‖^2) := by
  have hK : 0 ≤ ∑ i ∈ S, ‖c i‖^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hfi i hi := complexShortAverage_sq_integrable (f i) (hf i hi) hH X (2*X)
  have hsum : IntervalIntegrable (fun z => (∑ i ∈ S, ‖c i‖^2)*
      ∑ i ∈ S, ‖complexShortAverage (f i) H z‖^2) volume X (2*X) := by
    simpa only [Finset.sum_apply] using (IntervalIntegrable.sum S hfi).const_mul (∑ i ∈ S, ‖c i‖^2)
  have hc : IntervalIntegrable (fun z => ‖complexFiniteShort S c f H z‖^2) volume X (2*X) := by
    apply hsum.mono_fun'
    · exact ((Finset.measurable_sum S (fun i _ =>
        (measurable_complexShortAverage (f i) H).const_mul (c i))).norm.pow_const 2).aestronglyMeasurable
    · exact Eventually.of_forall (fun z => by
        simpa only [Real.norm_eq_abs,abs_pow,abs_norm] using complexFiniteShort_norm_sq_le S c f H z)
  have hi := intervalIntegral.integral_mono (by linarith : X ≤ 2*X) hc hsum
    (complexFiniteShort_norm_sq_le S c f H)
  have hh := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1/X)
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum hfi] at hh
  simpa only [mul_sum,mul_assoc,mul_left_comm (1/X)] using hh

theorem complexFiniteShort_eventually_eventually
    (hMRT : ComplexShortIntervalInput) {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (f : ℕ → ℕ → ι → ArithmeticFunction ℂ)
    (hmult : ∀ B n i, i ∈ S → (f B n i).IsMultiplicative)
    (hf : ∀ B n i, i ∈ S → ∀ k, ‖f B n i k‖ ≤ 1)
    (H : ℕ → ℝ) (X : ℕ → ℕ → ℝ)
    (hH : Tendsto H atTop atTop) (hX : ∀ B, Tendsto (X B) atTop atTop)
    (hdist : ∀ B i, i ∈ S → Tendsto (fun n => minimumDistance (f B n i) (X B n)) atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/X B n)*(∫ z in X B n..2*X B n, ‖complexFiniteShort S c (f B n) (H B) z‖^2) < ε := by
  intro ε hε
  let K := (∑ i ∈ S, ‖c i‖^2)*(S.card : ℝ)
  have hK : 0 ≤ K := mul_nonneg (sum_nonneg (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _)
  let δ := ε/(K+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall i (hi : i ∈ S) := complexShortAverage_eventually_eventually hMRT
    (fun B n => f B n i) (fun B n => hmult B n i hi) (fun B n k => hf B n i hi k)
    H X hH hX (fun B => hdist B i hi) δ hδ
  filter_upwards [(eventually_all_finset S).mpr hsmall,hH.eventually_gt_atTop 0] with B hsmall hHB
  filter_upwards [(eventually_all_finset S).mpr hsmall,(hX B).eventually_gt_atTop 0] with n hsmall hXB
  have he := complexFiniteShort_energy_le S c (f B n) (hf B n) hHB hXB
  have hs : (∑ i ∈ S, (1/X B n)*(∫ z in X B n..2*X B n,
      ‖complexShortAverage (f B n i) (H B) z‖^2)) ≤ (S.card : ℝ)*δ := by
    simpa only [sum_const,nsmul_eq_mul] using sum_le_sum (fun i hi => (hsmall i hi).le)
  have he' := he.trans (mul_le_mul_of_nonneg_left hs (sum_nonneg (fun _ _ => sq_nonneg _)))
  have hkδ : K*δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < K+1)).mpr
    nlinarith
  exact he'.trans_lt (by simpa only [K,mul_assoc] using hkδ)

end JointDickman.PublishedInputs

end OAI
