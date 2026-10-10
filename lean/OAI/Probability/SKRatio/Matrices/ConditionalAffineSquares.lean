import Mathlib
import OAI.Probability.SKRatio.Matrices.ConditionalGaussianSquares

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.MatrixNet
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

lemma weighted_square_conditioned_product_tail {A u : ℝ} (hA : 0≤A) (hu : 0<u) :
    ∃ c : ℝ, 0<c ∧ ∀ {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {ι : Type} [Fintype ι]
      (s : Finset ι) (a : Ω → ({i // i∉s} → ℝ) → s → ℝ),
      (∀ i, Measurable (fun p : Ω × ({i // i∉s} → ℝ) => a p.1 p.2 i)) →
      (∀ ω y i, |a ω y i|≤A) → ∀ {n : ℕ}, 0<n → s.card≤n →
      (μ.prod (standardArrayLaw ι)) {p | u ≤ |(∑ i : s,
        a p.1 (fun j => p.2 j) i * (p.2 i^2-1))/(n:ℝ)|} ≤
          ENNReal.ofReal (3*exp (-c*n)) := by
  obtain ⟨c,hc,ht⟩ := weighted_square_conditioned_tail hA hu
  refine ⟨c,hc,?_⟩
  intro Ω _ μ _ ι _ s a hm ha n hn hs
  have hE : MeasurableSet {p : Ω × (ι → ℝ) | u ≤ |(∑ i : s,
      a p.1 (fun j => p.2 j) i * (p.2 i^2-1))/(n:ℝ)|} := by
    apply measurableSet_le measurable_const
    apply Measurable.abs
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro i _
    have hr : Measurable (fun p : Ω × (ι → ℝ) => (p.1, fun j : {i // i∉s} => p.2 j)) := by
      fun_prop
    exact ((hm i).comp hr).mul
      (((measurable_pi_apply (i : ι)).comp measurable_snd).pow_const 2 |>.sub measurable_const)
  rw [Measure.prod_apply hE]
  calc
    _ ≤ ∫⁻ _ω : Ω, ENNReal.ofReal (3*exp (-c*n)) ∂μ := by
      apply lintegral_mono
      intro ω
      exact ht s (a ω) (fun i => (hm i).comp (measurable_const.prodMk measurable_id)) (ha ω) hn hs
    _ = _ := by simp

lemma average_abs_le_square_add_one {ι : Type*} [Fintype ι] (z : ι → ℝ)
    {n : ℕ} (hn : Fintype.card ι≤n) :
    (∑ i, |z i|)/(n:ℝ) ≤ (∑ i, z i^2)/(n:ℝ)+1 := by
  by_cases hn0 : n=0
  · simp [hn0]
  have hsum : ∑ i, |z i| ≤ (∑ i, z i^2)+(n:ℝ) := by
    calc
      _ ≤ ∑ i, (z i^2+1) := Finset.sum_le_sum (fun i _ => by
        nlinarith [sq_nonneg (|z i|-1),sq_abs (z i),abs_nonneg (z i)])
      _ = (∑ i, z i^2)+(Fintype.card ι:ℝ) := by simp [Finset.sum_add_distrib]
      _ ≤ _ := add_le_add_right (by exact_mod_cast hn : (Fintype.card ι:ℝ) ≤ n) _
  have h := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n : (0:ℝ)≤n)
  simpa [add_div,hn0] using h

lemma weighted_affine_square_error {ι : Type*} [Fintype ι]
    (β : ℝ) (a z : ι → ℝ) {A C : ℝ} (hA : 0≤A)
    (ha : ∀ i, |a i|≤A) {n : ℕ} (hn : 0<n) (hs : Fintype.card ι≤n)
    (hz : (∑ i, z i^2)/(n:ℝ)≤C) :
    |(∑ i, a i*((β/sqrt n*z i+β^2/(n:ℝ))^2-β^2/n))-
      β^2*((∑ i, a i*(z i^2-1))/(n:ℝ))| ≤
      A*(|2*β^3/sqrt n| *(C+1)+β^4/n) := by
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hsR : sqrt (n:ℝ) ≠ 0 := (sqrt_pos.mpr hnR).ne'
  have he (x : ℝ) : (β/sqrt n*x+β^2/(n:ℝ))^2-β^2/n =
      β^2*((x^2-1)/(n:ℝ))+(2*β^3/sqrt n)*(x/n)+β^4/(n:ℝ)^2 := by
    rw [add_sq,mul_pow,div_pow,sq_sqrt hnR.le]
    field_simp
    ring
  have hzs : (∑ i, |z i|)/(n:ℝ) ≤ C+1 :=
    (average_abs_le_square_add_one z hs).trans (add_le_add_left hz 1)
  have heq : (∑ i, a i*((β/sqrt n*z i+β^2/(n:ℝ))^2-β^2/n))-
      β^2*((∑ i, a i*(z i^2-1))/(n:ℝ)) =
      ∑ i, a i*((2*β^3/sqrt n)*(z i/n)+β^4/(n:ℝ)^2) := by
    simp_rw [he]
    rw [Finset.sum_div,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  calc
    _ ≤ ∑ i, |a i*((2*β^3/sqrt n)*(z i/n)+β^4/(n:ℝ)^2)| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ i, A*(|2*β^3/sqrt n| *(|z i|/n)+β^4/(n:ℝ)^2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul (ha i) _ (abs_nonneg _) hA
      apply (abs_add_le _ _).trans_eq
      rw [abs_mul,abs_div (z i),abs_of_pos hnR,abs_of_nonneg (by positivity : 0≤β^4/(n:ℝ)^2)]
    _ = A*(|2*β^3/sqrt n| *((∑ i, |z i|)/n)+(Fintype.card ι:ℝ)*(β^4/(n:ℝ)^2)) := by
      simp only [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_div,Finset.sum_const,
        Finset.card_univ,nsmul_eq_mul,mul_div_assoc]
    _ ≤ A*(|2*β^3/sqrt n| *(C+1)+(n:ℝ)*(β^4/(n:ℝ)^2)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact add_le_add (mul_le_mul_of_nonneg_left hzs (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hs : (Fintype.card ι:ℝ)≤n) (by positivity))
    _ = _ := by
      have hh : (n:ℝ)*(β^4/(n:ℝ)^2)=β^4/n := by field_simp [hnR.ne']
      rw [hh]

theorem weighted_affine_conditioned_tail (β C : ℝ) {A u : ℝ}
    (hA : 0≤A) (hu : 0<u) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      {ι : Type} [Fintype ι] (s : Finset ι)
      (a : Ω → ({i // i∉s} → ℝ) → s → ℝ), s.card≤n →
      (∀ i, Measurable (fun p : Ω × ({i // i∉s} → ℝ) => a p.1 p.2 i)) →
      (∀ ω y i, |a ω y i|≤A) →
      (μ.prod (standardArrayLaw ι)) {p |
        u < |∑ i : s, a p.1 (fun j => p.2 j) i *
          ((β/sqrt n*p.2 i+β^2/(n:ℝ))^2-β^2/n)| ∧
        (∑ i : s, p.2 i^2)/(n:ℝ) ≤ C} ≤
          ENNReal.ofReal (3*exp (-c*n)) := by
  let d := u/(2*(β^2+1))
  have hd : 0<d := by dsimp [d]; positivity
  obtain ⟨c,hc,ht⟩ := weighted_square_conditioned_product_tail hA hd
  have hconv : Tendsto (fun n : ℕ => A*(|2*β^3/sqrt n| *(C+1)+β^4/n)) atTop (𝓝 0) := by
    have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
    have h₁ := ((tendsto_const_nhds (x := 2*β^3)).div_atTop (tendsto_sqrt_atTop.comp hn)).abs.mul_const (C+1)
    have h₂ := (tendsto_const_nhds (x := β^4)).div_atTop hn
    simpa only [abs_zero,zero_mul,zero_add,mul_zero,Function.comp_def] using (h₁.add h₂).const_mul A
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_gt_atTop 0,hconv.eventually (gt_mem_nhds (half_pos hu))] with n hn hb
  intro Ω _ μ _ ι _ s a hs hm ha
  apply (measure_mono (t := {p : Ω × (ι → ℝ) | d ≤ |(∑ i : s,
    a p.1 (fun j => p.2 j) i*(p.2 i^2-1))/(n:ℝ)|}) ?_).trans (ht μ s a hm ha hn hs)
  rintro p ⟨hp,hrow⟩
  change d ≤ _
  apply le_of_not_gt
  intro hsmall
  have hh := weighted_affine_square_error β (a p.1 (fun j => p.2 j)) (fun i : s => p.2 i)
    hA (ha _ _) hn (by simpa using hs) hrow
  have hs' : β^2*|(∑ i : s, a p.1 (fun j => p.2 j) i*(p.2 i^2-1))/(n:ℝ)| ≤ u/2 := by
    apply (mul_le_mul_of_nonneg_left hsmall.le (sq_nonneg β)).trans
    dsimp only [d]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(β^2+1))).mpr
    nlinarith
  have htri := abs_sub_le (∑ i : s, a p.1 (fun j => p.2 j) i *
    ((β/sqrt n*p.2 i+β^2/(n:ℝ))^2-β^2/n))
    (β^2*((∑ i : s, a p.1 (fun j => p.2 j) i*(p.2 i^2-1))/(n:ℝ))) 0
  simp only [sub_zero,abs_mul,abs_of_nonneg (sq_nonneg β)] at htri
  linarith only [hp,hh,hb,hs',htri]

end SKRatio.MatrixNet

end
end

end OAI
