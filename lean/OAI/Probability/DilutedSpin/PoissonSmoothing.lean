import OAI.Probability.DilutedSpin.ReservoirTrees

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Poisson's add-one identity gives a *smoothing* estimate for every bounded
 test, without any regularity in the count. This is the needed large-rate
 transfer for the cavity reservoir, not the O(1) unmatched-points estimate. -/
lemma poisson_bounded_shift (r : ℝ≥0) (hr : 0<r) {f : ℕ → ℝ} {B : ℝ}
    (hf : ∀ n, |f n|≤B) :
    |(∫ n, f (n+1) ∂poissonMeasure r)-(∫ n, f n ∂poissonMeasure r)| ≤
      B / Real.sqrt r := by
  have hB : 0≤B := (abs_nonneg (f 0)).trans (hf 0)
  have hreal : (0:ℝ)<r := hr
  have hi : Integrable f (poissonMeasure r) := (bounded_memLp (Measurable.of_discrete) hf 1).integrable le_rfl
  have hi' : Integrable (fun n => f (n+1)) (poissonMeasure r) :=
    (bounded_memLp (Measurable.of_discrete) (fun n => hf (n+1)) 1).integrable le_rfl
  have hn : MemLp (fun n : ℕ => (n:ℝ)) 2 (poissonMeasure r) :=
    poisson_memLp_lipschitz r (by norm_num : (0:ℝ)≤1) (fun _ _ => by simp)
  have hc := hn.sub (memLp_const (r:ℝ))
  have hcs : (∫ n : ℕ, |(n:ℝ)-r| ∂poissonMeasure r)≤Real.sqrt r := by
    simpa only [Pi.sub_apply,poisson_variance] using integral_abs_le_sqrt_sq (poissonMeasure r) hc
  have hnf : Integrable (fun n : ℕ => (n:ℝ)*f n) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 0) (B := B)
    intro n
    rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
    simpa only [zero_add,mul_comm] using mul_le_mul_of_nonneg_left (hf n) (Nat.cast_nonneg n)
  have hid : Integrable (fun n : ℕ => ((n:ℝ)-r)*f n) (poissonMeasure r) := by
    have heq : (fun n : ℕ => ((n:ℝ)-r)*f n)=
        (fun n : ℕ => (n:ℝ)*f n)-(fun n => (r:ℝ)*f n) := by
      funext n
      change ((n:ℝ)-r)*f n=(n:ℝ)*f n-(r:ℝ)*f n
      ring
    rw [heq]
    exact hnf.sub (hi.const_mul r)
  have he : (r:ℝ)*((∫ n, f (n+1) ∂poissonMeasure r)-(∫ n, f n ∂poissonMeasure r)) =
      ∫ n : ℕ, ((n:ℝ)-r)*f n ∂poissonMeasure r := by
    simp_rw [sub_mul]
    rw [integral_sub hnf (hi.const_mul r),integral_const_mul,poisson_add_one r f hi',mul_sub]
  have hab := abs_integral_le_integral_abs (f := fun n : ℕ => ((n:ℝ)-r)*f n) (μ := poissonMeasure r)
  have hm : (∫ n : ℕ, |((n:ℝ)-r)*f n| ∂poissonMeasure r) ≤
      B * Real.sqrt r := by
    calc
      _ ≤ ∫ n : ℕ, |(n:ℝ)-r| * B ∂poissonMeasure r := by
        apply integral_mono hid.abs ((hc.integrable (by norm_num)).abs.mul_const B)
        intro n
        change |((n:ℝ)-r)*f n| ≤ |(n:ℝ)-r| * B
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hf n) (abs_nonneg _)
      _ = B*(∫ n : ℕ, |(n:ℝ)-r| ∂poissonMeasure r) := by rw [integral_mul_const,mul_comm]
      _ ≤ B*Real.sqrt r := mul_le_mul_of_nonneg_left hcs hB
  rw [← he,abs_mul,abs_of_pos hreal] at hab
  have hs : 0<Real.sqrt (r:ℝ) := Real.sqrt_pos.2 hreal
  have hsq := Real.sq_sqrt (le_of_lt hreal)
  rw [le_div_iff₀ hs]
  nlinarith [hab.trans hm]

lemma poisson_bounded_rate_add (r s : ℝ≥0) (hr : 0<r) {f : ℕ → ℝ} {B : ℝ}
    (hf : ∀ n, |f n|≤B) :
    |(∫ n, f n ∂poissonMeasure (r+s))-(∫ n, f n ∂poissonMeasure r)| ≤
      B*(s:ℝ)/Real.sqrt r := by
  have hB : 0≤B := (abs_nonneg (f 0)).trans (hf 0)
  let g (k : ℕ) := ∫ n, f (n+k) ∂poissonMeasure r
  have hg (k : ℕ) : |g (k+1)-g k|≤B/Real.sqrt r := by
    simpa only [g,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      poisson_bounded_shift r hr (f := fun n => f (n+k)) (fun n => hf (n+k))
  have hl := nat_lipschitz_of_step (div_nonneg hB (Real.sqrt_nonneg r)) hg
  have hgi : Integrable g (poissonMeasure s) :=
    (bounded_memLp (Measurable.of_discrete) (fun k => abs_integral_le_bound (μ := poissonMeasure r) (fun n => hf (n+k))) 1).integrable le_rfl
  have hc : |(∫ k, g k ∂poissonMeasure s)-g 0| ≤ B/Real.sqrt r*(s:ℝ) := by
    have hconst : (∫ _ : ℕ, g 0 ∂poissonMeasure s)=g 0 := by simp
    rw [← hconst,← integral_sub hgi (integrable_const (g 0))]
    calc
      _ ≤ ∫ k, |g k-g 0| ∂poissonMeasure s := abs_integral_le_integral_abs
      _ ≤ ∫ k : ℕ, (B/Real.sqrt r)*(k:ℝ) ∂poissonMeasure s := by
        apply integral_mono (hgi.sub (integrable_const (g 0))).abs ((poisson_integrable_count s).const_mul _)
        intro k
        change |g k-g 0|≤(B/Real.sqrt r)*(k:ℝ)
        simpa only [Nat.cast_zero,sub_zero,abs_of_nonneg (Nat.cast_nonneg k : (0:ℝ)≤k)] using hl k 0
      _ = _ := by rw [integral_const_mul,poisson_mean]
  have hi (t : ℝ≥0) : Integrable f (poissonMeasure t) :=
    (bounded_memLp (Measurable.of_discrete) hf 1).integrable le_rfl
  have hconv : (∫ k, g k ∂poissonMeasure s)=∫ n, f n ∂poissonMeasure (r+s) := by
    rw [add_comm r s,← poissonMeasure_conv_poissonMeasure s r]
    rw [integral_conv (by simpa only [poissonMeasure_conv_poissonMeasure] using hi (s+r))]
    simp only [g,Nat.add_comm]
  dsimp only [g] at hc
  simp only [Nat.add_zero] at hc
  change |(∫ k, g k ∂poissonMeasure s)-(∫ n, f n ∂poissonMeasure r)|≤_ at hc
  rw [hconv] at hc
  simpa only [div_mul_eq_mul_div] using hc
end DilutedSpinGlass

end

end OAI
