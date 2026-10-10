import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma sq_le_discrete_tail_sum (t : ℕ → ℝ) (_ht : ∀ k, 0≤t k)
    {x : ℝ} (hx : 0≤x) (N : ℕ) (hxN : x≤t N) :
    x^2≤(t 0)^2+∑ k∈Finset.range N, (t (k+1))^2*(if t k<x then 1 else 0) := by
  induction N with
  | zero => simpa using pow_le_pow_left₀ hx hxN 2
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases H : x≤t N
    · have hn : 0≤(t (N+1))^2*(if t N<x then 1 else 0) := by split_ifs <;> positivity
      linarith [ih H]
    · rw [ite_eq_left (lt_of_not_ge H),mul_one]
      have hsum : 0≤∑ k∈Finset.range N, (t (k+1))^2*(if t k<x then 1 else 0) := by
        apply Finset.sum_nonneg
        intro k _
        split_ifs <;> positivity
      have hpow := pow_le_pow_left₀ hx hxN 2
      nlinarith [sq_nonneg (t 0)]

theorem secondMoment_le_discrete_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (hf0 : ∀ ω, 0≤f ω) (t b : ℕ → ℝ) (ht : ∀ k, 0≤t k)
    (N : ℕ) (hbound : ∀ ω, f ω≤t N)
    (htail : ∀ k, μ.real {ω | t k<f ω}≤b k)
    (hsum : Summable (fun k => (t (k+1))^2*b k)) :
    (∫ ω, (f ω)^2 ∂μ)≤(t 0)^2+∑' k, (t (k+1))^2*b k := by
  let F : ℕ → Ω → ℝ := fun k => ({ω | t k<f ω}).indicator (fun _ => (1:ℝ))
  have hF : ∀ k, Integrable (F k) μ := fun k =>
    (integrable_const 1).indicator (measurableSet_lt measurable_const hf)
  have hfi : Integrable (fun ω => (f ω)^2) μ := by
    apply (integrable_const ((t N)^2)).mono' (hf.pow_const 2).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hf0 ω) (hbound ω) 2
  have hgi : Integrable (fun ω => (t 0)^2+∑ k∈Finset.range N, (t (k+1))^2*F k ω) μ :=
    (integrable_const _).add (integrable_finsetSum _ (fun k _ => (hF k).const_mul _))
  have H := integral_mono hfi hgi (fun ω => sq_le_discrete_tail_sum t ht (hf0 ω) N (hbound ω))
  have hInt : (∫ ω, (t 0)^2+∑ k∈Finset.range N, (t (k+1))^2*F k ω ∂μ)=
      (t 0)^2+∑ k∈Finset.range N, (t (k+1))^2*μ.real {ω | t k<f ω} := by
    rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun k _ => (hF k).const_mul _)),
      integral_finsetSum _ (fun k _ => (hF k).const_mul _)]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul]
    congr 1
    exact integral_indicator_const _ (measurableSet_lt measurable_const hf) |>.trans (by simp)
  rw [hInt] at H
  apply H.trans
  exact add_le_add le_rfl (by
    calc
      _ ≤ ∑ k∈Finset.range N, (t (k+1))^2*b k :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (htail k) (sq_nonneg _))
      _ ≤ ∑' k, (t (k+1))^2*b k :=
        hsum.sum_le_tsum _ (fun k _ => mul_nonneg (sq_nonneg _) ((measureReal_nonneg).trans (htail k)))
  )

lemma summable_cubic_exponential_tail (C : ℝ) :
    Summable (fun k : ℕ => (C*(1+((k+1:ℕ):ℝ))^3)^2*Real.exp (-(k:ℝ))) := by
  have hs := Real.summable_pow_mul_exp_neg_nat_mul 6 (r:=1) (by norm_num)
  have hshift := (summable_nat_add_iff 2).mpr hs
  have hsimple : Summable (fun k : ℕ => ((k:ℝ)+2)^6*Real.exp (-((k:ℝ)+2))) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,neg_mul,one_mul] using hshift
  have heq : (fun k : ℕ => (C*(1+((k+1:ℕ):ℝ))^3)^2*Real.exp (-(k:ℝ))) =
      (fun k : ℕ => (C^2*Real.exp 2)*(((k:ℝ)+2)^6*Real.exp (-((k:ℝ)+2)))) := by
    funext k
    have he : Real.exp 2*Real.exp (-((k:ℝ)+2))=Real.exp (-(k:ℝ)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    simp only [Nat.cast_add,Nat.cast_one]
    calc
      _ = C^2*((k:ℝ)+2)^6*(Real.exp 2*Real.exp (-((k:ℝ)+2))) := by rw [he]; ring
      _ = _ := by ring
  rw [heq]
  exact hsimple.mul_left (C^2*Real.exp 2)

theorem positive_event_probability_of_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (hf0 : ∀ ω, 0≤f ω) (hfi : Integrable f μ)
    (hf2 : Integrable (fun ω => (f ω)^2) μ) {M : ℝ} (hM : 0<M)
    (hmean : 1≤∫ ω, f ω ∂μ) (hmoment : (∫ ω, (f ω)^2 ∂μ)≤M) :
    1/M≤μ.real {ω | 0<f ω} := by
  have hA : MeasurableSet {ω | 0<f ω} := measurableSet_lt measurable_const hf
  have hi : Integrable (({ω | 0<f ω}).indicator (fun _ => M^2)) μ :=
    (integrable_const _).indicator hA
  have H := integral_mono (hfi.const_mul (2*M)) (hf2.add hi) (fun ω => by
    change 2*M*f ω≤(f ω)^2+({ω | 0<f ω}).indicator (fun _ => M^2) ω
    by_cases hp : 0<f ω
    · rw [indicator_of_mem (show ω∈{ω | 0<f ω} from hp)]
      nlinarith [sq_nonneg (f ω-M)]
    · have he : f ω=0 := le_antisymm (not_lt.mp hp) (hf0 ω)
      rw [indicator_of_notMem (show ω∉{ω | 0<f ω} from hp),he]
      norm_num)
  simp only [Pi.add_apply] at H
  rw [integral_const_mul,integral_add hf2 hi,integral_indicator_const _ hA,smul_eq_mul] at H
  have hmul := mul_le_mul_of_nonneg_left hmean (show 0≤2*M by positivity)
  apply (div_le_iff₀ hM).mpr
  apply (mul_le_mul_iff_left₀ hM).mp
  nlinarith
end NeutralAtom

end

end
end

end OAI
