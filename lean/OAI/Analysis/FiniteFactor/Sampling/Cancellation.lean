import OAI.Analysis.FiniteFactor.Sampling.IntegratedCorrelation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical
noncomputable section

/-- Exact finite-average expansion, before bounding or discarding any term. -/
theorem sampling_average_square_expansion {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (f : ι → Ω → ℝ) (g : Ω → ℝ)
    (hpair : ∀ n ∈ S, ∀ k ∈ S, Integrable (fun x => f n x*f k x) μ)
    (hmix : ∀ n ∈ S, Integrable (fun x => f n x*g x) μ)
    (hg : Integrable (fun x => g x^2) μ) :
    (∫ x, ((∑ n ∈ S, f n x)/(S.card : ℝ)-g x)^2 ∂μ) =
      (∑ n ∈ S, ∑ k ∈ S, ∫ x, f n x*f k x ∂μ)/(S.card : ℝ)^2 -
      2*(∑ n ∈ S, ∫ x, f n x*g x ∂μ)/(S.card : ℝ)+(∫ x, g x^2 ∂μ) := by
  have he (x : Ω) : ((∑ n ∈ S, f n x)/(S.card : ℝ)-g x)^2 =
      (∑ n ∈ S, ∑ k ∈ S, f n x*f k x)/(S.card : ℝ)^2 -
      2*(∑ n ∈ S, f n x*g x)/(S.card : ℝ)+g x^2 := by
    have hsq : (∑ n ∈ S, ∑ k ∈ S, f n x*f k x) = (∑ n ∈ S, f n x)^2 := by
      rw [pow_two]; simp_rw [Finset.sum_mul,Finset.mul_sum]
    rw [hsq,← Finset.sum_mul]
    ring
  have hpi := integrable_finsetSum S (fun n hn => integrable_finsetSum S (fun k hk => hpair n hn k hk))
  have hmi := integrable_finsetSum S (fun n hn => hmix n hn)
  have hiP : Integrable (fun x => (∑ n ∈ S, ∑ k ∈ S, f n x*f k x)/(S.card : ℝ)^2) μ := hpi.div_const _
  have hiM : Integrable (fun x => 2*(∑ n ∈ S, f n x*g x)/(S.card : ℝ)) μ := (hmi.const_mul 2).div_const _
  have hiSub : Integrable (fun x => (∑ n ∈ S, ∑ k ∈ S, f n x*f k x)/(S.card : ℝ)^2 -
      2*(∑ n ∈ S, f n x*g x)/(S.card : ℝ)) μ := hiP.sub hiM
  have hpis : (∫ x, ∑ n ∈ S, ∑ k ∈ S, f n x*f k x ∂μ) =
      ∑ n ∈ S, ∑ k ∈ S, ∫ x, f n x*f k x ∂μ := by
    rw [integral_finsetSum S (fun n hn => integrable_finsetSum S (fun k hk => hpair n hn k hk))]
    apply sum_congr rfl
    intro n hn
    exact integral_finsetSum S (fun k hk => hpair n hn k hk)
  simp_rw [he]
  rw [integral_add hiSub hg,integral_sub hiP hiM,integral_div,integral_div,integral_const_mul,
    hpis,integral_finsetSum S (fun n hn => hmix n hn)]

/-- Integrability of the full error follows from the same finite expansion. -/
theorem sampling_average_square_integrable {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (f : ι → Ω → ℝ) (g : Ω → ℝ)
    (hpair : ∀ n ∈ S, ∀ k ∈ S, Integrable (fun x => f n x*f k x) μ)
    (hmix : ∀ n ∈ S, Integrable (fun x => f n x*g x) μ)
    (hg : Integrable (fun x => g x^2) μ) :
    Integrable (fun x => ((∑ n ∈ S, f n x)/(S.card : ℝ)-g x)^2) μ := by
  have hpi := integrable_finsetSum S (fun n hn => integrable_finsetSum S (fun k hk => hpair n hn k hk))
  have hmi := integrable_finsetSum S (fun n hn => hmix n hn)
  have h : Integrable (fun x => (∑ n ∈ S, ∑ k ∈ S, f n x*f k x)/(S.card : ℝ)^2 -
      2*(∑ n ∈ S, f n x*g x)/(S.card : ℝ)+g x^2) μ :=
    ((hpi.div_const _).sub ((hmi.const_mul 2).div_const _)).add hg
  apply h.congr
  apply Eventually.of_forall
  intro x
  have hsq : (∑ n ∈ S, ∑ k ∈ S, f n x*f k x) = (∑ n ∈ S, f n x)^2 := by
    rw [pow_two]; simp_rw [Finset.sum_mul,Finset.mul_sum]
  dsimp only
  rw [hsq,← Finset.sum_mul]
  ring

/-- The distinct-pair and mixed main terms cancel to -A/P. Since A is
nonnegative, the surviving upper bound is the actual diagonal term plus 3ε. -/
theorem sampling_finite_cancellation {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (B : ι → ι → ℝ) (M : ι → ℝ) (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hpair : ∀ n ∈ S, ∀ k ∈ S, n ≠ k → |B n k-A| ≤ ε)
    (hmix : ∀ n ∈ S, |M n-A| ≤ ε) :
    (∑ n ∈ S, ∑ k ∈ S, B n k)/(S.card : ℝ)^2 -
      2*(∑ n ∈ S, M n)/(S.card : ℝ)+A ≤
      (∑ n ∈ S, B n n)/(S.card : ℝ)^2+3*ε := by
  let N : ℝ := S.card
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hS.card_pos
  have hN1 : 1 ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ S.card from hS.card_pos)
  have hp (n : ι) (hn : n ∈ S) :
      (∑ k ∈ S, B n k) ≤ B n n+(N-1)*(A+ε) := by
    have hoff : (∑ k ∈ S.erase n, B n k) ≤ ((S.erase n).card : ℝ)*(A+ε) := by
      calc
        _ ≤ ∑ _k ∈ S.erase n, (A+ε) := sum_le_sum (fun k hk => by
          have hmem := mem_erase.mp hk
          have hb := (abs_le.mp (hpair n hn k hmem.2 (Ne.symm hmem.1))).2
          linarith)
        _ = _ := by simp; ring
    have hc : ((S.erase n).card : ℝ) = N-1 := by
      rw [card_erase_of_mem hn,Nat.cast_sub (by exact hS.card_pos),Nat.cast_one]
    rw [hc] at hoff
    have he := sum_erase_add S (fun k => B n k) hn
    linarith
  have hpall : (∑ n ∈ S, ∑ k ∈ S, B n k) ≤
      (∑ n ∈ S, B n n)+N*(N-1)*(A+ε) := by
    calc
      _ ≤ ∑ n ∈ S, (B n n+(N-1)*(A+ε)) := sum_le_sum hp
      _ = _ := by rw [sum_add_distrib]; simp [N]; ring
  have hmall : N*(A-ε) ≤ ∑ n ∈ S, M n := by
    calc
      _ = ∑ _n ∈ S, (A-ε) := by simp [N]; ring
      _ ≤ _ := sum_le_sum (fun n hn => by have hh := (abs_le.mp (hmix n hn)).1; linarith)
  change _/N^2-2*_/N+A ≤ _/N^2+3*ε
  have hpdiv := div_le_div_of_nonneg_right hpall (sq_nonneg N)
  have hmdiv := div_le_div_of_nonneg_right hmall hN.le
  have hcancel : ((∑ n ∈ S, B n n)+N*(N-1)*(A+ε))/N^2-
      2*(N*(A-ε))/N+A =
      (∑ n ∈ S, B n n)/N^2+3*ε-(A+ε)/N := by field_simp; ring
  have hnneg : 0 ≤ (A+ε)/N := div_nonneg (add_nonneg hA hε) hN.le
  simp only [mul_div_assoc] at hmdiv hcancel ⊢
  nlinarith

end
end FiniteFactor

end OAI
