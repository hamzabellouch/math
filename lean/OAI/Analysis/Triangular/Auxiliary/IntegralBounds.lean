import OAI.Analysis.Triangular.Basic

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace AtomicTriangular.IntegralVectors
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma weighted_interval_bound {a b t M : ℝ} (hab : a≤b) (hbt : b≤t)
    (f : ℝ → E) (hf : ∀ x ∈ Icc a b, ‖f x‖≤M) :
    ‖∫ x in a..b, (t-x) • f x‖ ≤ ((t-a)^2-(t-b)^2)/2*M := by
  calc
    _ ≤ ∫ x in a..b, (t-x)*M := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab
      · exact ae_of_all _ fun x hx => by
          rw [norm_smul,Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr (hx.2.trans hbt))]
          exact mul_le_mul_of_nonneg_left (hf x ⟨hx.1.le,hx.2⟩) (sub_nonneg.mpr (hx.2.trans hbt))
      · exact (show Continuous (fun x : ℝ => (t-x)*M) by fun_prop).intervalIntegrable a b
    _ = _ := by
      rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_sub (f:=fun _ : ℝ => t)
        (g:=fun x : ℝ => x) intervalIntegrable_const (continuous_id.intervalIntegrable _ _),integral_id]
      simp only [intervalIntegral.integral_const,smul_eq_mul]
      ring

lemma norm_integral_grid {δ : ℝ} (hδ : 0≤δ) (n : ℕ) (f : ℝ → E) (hf : Continuous f)
    (M : ℕ → ℝ) (hM : ∀ i<n, ∀ x ∈ Icc ((i:ℝ)*δ) ((i+1:ℕ)*δ), ‖f x‖≤M i) :
    ‖∫ x in (0:ℝ)..(n:ℝ)*δ, f x‖ ≤ δ*∑ i ∈ Finset.range n, M i := by
  have hi := intervalIntegral.sum_integral_adjacent_intervals (a:=fun i : ℕ => (i:ℝ)*δ)
    (μ:=volume) (n:=n) (f:=f) (fun i _ => hf.intervalIntegrable _ _)
  simp only [Nat.cast_zero,zero_mul] at hi
  rw [←hi]
  calc
    _ ≤ ∑ i ∈ Finset.range n, ‖∫ x in (i:ℝ)*δ..(i+1:ℕ)*δ, f x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, δ*M i := by
      apply Finset.sum_le_sum
      intro i hi
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const
        (fun x hx => hM i (Finset.mem_range.mp hi) x (by
          rw [Set.uIoc_of_le (show (i:ℝ)*δ≤(i+1:ℕ)*δ by push_cast; nlinarith)] at hx
          exact ⟨hx.1.le,hx.2⟩))
        (a := (i:ℝ)*δ) (b := (i+1:ℕ)*δ)
      have hd : |((i+1:ℕ):ℝ)*δ-(i:ℝ)*δ|=δ := by
        rw [show ((i+1:ℕ):ℝ)*δ-(i:ℝ)*δ=δ by push_cast; ring,abs_of_nonneg hδ]
      rw [hd] at hh
      simpa only [mul_comm] using hh
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma weighted_integral_grid {δ : ℝ} (hδ : 0≤δ) (n : ℕ) (f : ℝ → E) (hf : Continuous f)
    (M : ℕ → ℝ) (hM : ∀ i<n, ∀ x ∈ Icc ((i:ℝ)*δ) ((i+1:ℕ)*δ), ‖f x‖≤M i) :
    ‖∫ x in (0:ℝ)..(n:ℝ)*δ, ((n:ℝ)*δ-x) • f x‖ ≤
      δ^2*∑ i ∈ Finset.range n, ((n:ℝ)-i-1/2)*M i := by
  have hc : Continuous (fun x : ℝ => ((n:ℝ)*δ-x) • f x) := by fun_prop
  have hi := intervalIntegral.sum_integral_adjacent_intervals (a:=fun i : ℕ => (i:ℝ)*δ)
    (μ:=volume) (n:=n) (f:=fun x : ℝ => ((n:ℝ)*δ-x) • f x) (fun i _ => hc.intervalIntegrable _ _)
  simp only [Nat.cast_zero,zero_mul] at hi
  rw [←hi]
  calc
    _ ≤ ∑ i ∈ Finset.range n, ‖∫ x in (i:ℝ)*δ..(i+1:ℕ)*δ, ((n:ℝ)*δ-x) • f x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, δ^2*((n:ℝ)-i-1/2)*M i := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i+1≤n := Finset.mem_range.mp hi
      have hiR : ((i+1:ℕ):ℝ)≤n := by exact_mod_cast hin
      have hh := weighted_interval_bound (show (i:ℝ)*δ≤(i+1:ℕ)*δ by push_cast; nlinarith)
        (mul_le_mul_of_nonneg_right hiR hδ) f (hM i (Finset.mem_range.mp hi))
      calc
        _ ≤ (((n:ℝ)*δ-(i:ℝ)*δ)^2-((n:ℝ)*δ-((i+1:ℕ):ℝ)*δ)^2)/2*M i := by
          exact hh
        _ = _ := by push_cast; ring
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
lemma norm_integral_neg (f : ℝ → E) (t : ℝ) :
    ‖∫ x in (0:ℝ)..-t, f x‖ = ‖∫ x in (0:ℝ)..t, f (-x)‖ := by
  rw [intervalIntegral.integral_comp_neg,neg_zero,intervalIntegral.integral_symm,norm_neg]
lemma norm_weighted_integral_neg (f : ℝ → E) (t : ℝ) :
    ‖∫ x in (0:ℝ)..-t, (-t-x) • f x‖ = ‖∫ x in (0:ℝ)..t, (t-x) • f (-x)‖ := by
  rw [norm_integral_neg]
  simp only [show ∀ x : ℝ, -t- -x=-(t-x) by intro x; ring,neg_smul,
    intervalIntegral.integral_neg,norm_neg]
lemma norm_integral_grid_abs {δ t : ℝ} (hδ : 0≤δ) (n : ℕ) (ht : |t|=(n:ℝ)*δ)
    (f : ℝ → E) (hf : Continuous f) (M : ℕ → ℝ)
    (hM : ∀ i<n, ∀ x, (i:ℝ)*δ≤|x| → |x|≤(i+1:ℕ)*δ → ‖f x‖≤M i) :
    ‖∫ x in (0:ℝ)..t, f x‖ ≤ δ*∑ i ∈ Finset.range n, M i := by
  rcases le_total 0 t with ht0|ht0
  · rw [abs_of_nonneg ht0] at ht
    rw [ht]
    exact norm_integral_grid hδ n f hf M (fun i hi x hx => hM i hi x
      (by rw [abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.1)
      (by rw [abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.2))
  · rw [abs_of_nonpos ht0] at ht
    have hte : t= -((n:ℝ)*δ) := by linarith
    rw [hte,norm_integral_neg]
    exact norm_integral_grid hδ n (fun x => f (-x)) (hf.comp continuous_neg) M (fun i hi x hx => hM i hi (-x)
      (by rw [abs_neg,abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.1)
      (by rw [abs_neg,abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.2))
lemma weighted_integral_grid_abs {δ t : ℝ} (hδ : 0≤δ) (n : ℕ) (ht : |t|=(n:ℝ)*δ)
    (f : ℝ → E) (hf : Continuous f) (M : ℕ → ℝ)
    (hM : ∀ i<n, ∀ x, (i:ℝ)*δ≤|x| → |x|≤(i+1:ℕ)*δ → ‖f x‖≤M i) :
    ‖∫ x in (0:ℝ)..t, (t-x) • f x‖ ≤ δ^2*∑ i ∈ Finset.range n, ((n:ℝ)-i-1/2)*M i := by
  rcases le_total 0 t with ht0|ht0
  · rw [abs_of_nonneg ht0] at ht
    rw [ht]
    exact weighted_integral_grid hδ n f hf M (fun i hi x hx => hM i hi x
      (by rw [abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.1)
      (by rw [abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.2))
  · rw [abs_of_nonpos ht0] at ht
    have hte : t= -((n:ℝ)*δ) := by linarith
    rw [hte,norm_weighted_integral_neg]
    exact weighted_integral_grid hδ n (fun x => f (-x)) (hf.comp continuous_neg) M (fun i hi x hx => hM i hi (-x)
      (by rw [abs_neg,abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.1)
      (by rw [abs_neg,abs_of_nonneg (le_trans (by positivity) hx.1)]; exact hx.2))
end AtomicTriangular.IntegralVectors
end

end OAI
