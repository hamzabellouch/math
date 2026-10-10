import OAI.Analysis.FreeEntropy.VectorSeries

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset

 def truncEval (a : ℕ → ℝ) (r : ℝ) (N : ℕ) : ℝ := ∑ n ∈ range (N+1), r^n * a n
 theorem truncEval_nonneg {a : ℕ → ℝ} {r : ℝ} (ha : ∀ n, 0 ≤ a n) (hr : 0 ≤ r) (N : ℕ) :
    0 ≤ truncEval a r N := sum_nonneg fun n _ => mul_nonneg (pow_nonneg hr _) (ha n)
 theorem truncEval_mono {a : ℕ → ℝ} {r : ℝ} (ha : ∀ n, 0 ≤ a n) (hr : 0 ≤ r)
    {N K : ℕ} (hNK : N ≤ K) : truncEval a r N ≤ truncEval a r K := by
  apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
  intro n _ _
  exact mul_nonneg (pow_nonneg hr _) (ha n)
 theorem truncEval_le {a b : ℕ → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hab : ∀ n, a n ≤ b n) (N : ℕ) : truncEval a r N ≤ truncEval b r N :=
  sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hab n) (pow_nonneg hr n)
@[simp] theorem truncEval_zero (a : ℕ → ℝ) (r : ℝ) : truncEval a r 0 = a 0 := by simp [truncEval]
 theorem truncEval_succ_shift (a : ℕ → ℝ) (r : ℝ) (N : ℕ) :
    truncEval a r (N+1) = a 0 + r * truncEval (fun n => a (n+1)) r N := by
  unfold truncEval
  rw [sum_range_succ']
  simp only [pow_zero, one_mul, mul_sum, pow_succ]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro n _
  ring

 theorem triangle_le_rectangle (f : ℕ → ℕ → ℝ) (hf : ∀ i j, 0 ≤ f i j) (N : ℕ) :
    (∑ n ∈ range (N+1), ∑ k ∈ range (n+1), f k (n-k)) ≤
      ∑ k ∈ range (N+1), ∑ j ∈ range (N+1), f k j := by
  let s := (range (N+1) ×ˢ range (N+1)).filter (fun v : ℕ × ℕ => v.1+v.2 ≤ N)
  rw [sum_sigma']
  calc
    _ = ∑ v ∈ s, f v.1 v.2 := by
      apply sum_bij (fun x _ => (x.2, x.1-x.2))
      · intro x hx
        obtain ⟨hx1,hx2⟩ := mem_sigma.mp hx
        simp only [mem_range] at hx1 hx2
        simp only [s, mem_filter, mem_product, mem_range]
        omega
      · intro x hx y hy he
        obtain ⟨hx1,hx2⟩ := mem_sigma.mp hx
        obtain ⟨hy1,hy2⟩ := mem_sigma.mp hy
        simp only [mem_range] at hx1 hx2 hy1 hy2
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        rcases x with ⟨xn,xk⟩
        rcases y with ⟨yn,yk⟩
        dsimp at h1 h2 hx1 hx2 hy1 hy2
        have hxy : xn = yn := by omega
        subst yn
        subst yk
        rfl
      · intro y hy
        simp only [s, mem_filter, mem_product, mem_range] at hy
        refine ⟨⟨y.1+y.2,y.1⟩, ?_, ?_⟩
        · simp only [mem_sigma, mem_range]; omega
        · apply Prod.ext <;> simp
      · intro x hx; rfl
    _ ≤ ∑ v ∈ range (N+1) ×ˢ range (N+1), f v.1 v.2 := by
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun v _ _ => hf v.1 v.2)
    _ = _ := sum_product _ _ _

 def scalarConv (a b : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ range (n+1), a k * b (n-k)
 theorem truncEval_conv_le {a b : ℕ → ℝ} {r : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hr : 0 ≤ r) (N : ℕ) :
    truncEval (scalarConv a b) r N ≤ truncEval a r N * truncEval b r N := by
  unfold truncEval
  rw [sum_mul_sum]
  calc
    _ = ∑ n ∈ range (N+1), ∑ k ∈ range (n+1), (r^k*a k)*(r^(n-k)*b (n-k)) := by
      apply sum_congr rfl
      intro n hn
      rw [scalarConv, mul_sum]
      apply sum_congr rfl
      intro k hk
      have hkn : k+(n-k)=n := Nat.add_sub_of_le (Nat.le_of_lt_succ (mem_range.mp hk))
      have hp : r^n = r^k*r^(n-k) := by rw [← pow_add, hkn]
      rw [hp]; ring
    _ ≤ _ := by
      exact triangle_le_rectangle (fun k j => (r^k*a k)*(r^j*b j))
        (fun k j => mul_nonneg (mul_nonneg (pow_nonneg hr _) (ha k))
          (mul_nonneg (pow_nonneg hr _) (hb j))) N

 theorem substBound_trunc_le {b a : ℕ → ℝ} {r B : ℝ}
    (hb : ∀ n, 0 ≤ b n) (ha : ∀ n, 0 ≤ a n) (hr : 0 ≤ r)
    (N : ℕ) (hB : truncEval b r N ≤ B) :
    truncEval (substBound b a) r N ≤ ∑ k ∈ range (N+1), a k * (r*B)^k := by
  have hB0 : 0 ≤ B := (truncEval_nonneg hb hr N).trans hB
  induction N generalizing a with
  | zero => simp [substBound]
  | succ N ih =>
    have hBN : truncEval b r N ≤ B := (truncEval_mono hb hr (by omega)).trans hB
    have ha' : ∀ n, 0 ≤ a (n+1) := fun n => ha (n+1)
    have hi := ih ha' hBN
    have ht : (fun n => substBound b a (n+1)) = scalarConv b (substBound b (fun n => a (n+1))) := by
      funext n
      rw [substBound, scalarConv]
    rw [truncEval_succ_shift, show substBound b a 0 = a 0 by rw [substBound], ht]
    calc
      _ ≤ a 0 + r * (truncEval b r N * truncEval (substBound b (fun n => a (n+1))) r N) := by
        gcongr
        exact truncEval_conv_le hb (substBound_nonneg hb ha') hr N
      _ ≤ a 0 + r * (B * ∑ k ∈ range (N+1), a (k+1) * (r*B)^k) := by
        apply add_le_add_right (mul_le_mul_of_nonneg_left _ hr)
        exact mul_le_mul hBN hi (truncEval_nonneg (substBound_nonneg hb ha') hr N) hB0
      _ = _ := by
        conv_rhs => rw [sum_range_succ']
        simp only [pow_zero, mul_one, pow_succ, mul_sum]
        rw [add_comm]
        congr 1
        apply sum_congr rfl
        intro k hk
        ring

variable {α : Type} [Fintype α]
 def seriesWeight (f : Series α) (r : ℝ) (N : ℕ) : ℝ := truncEval (degreeNorm f) r N
 theorem seriesWeight_nonneg (f : Series α) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    0 ≤ seriesWeight f r N := truncEval_nonneg (degreeNorm_nonneg f) hr N
 theorem seriesWeight_conv_le (f g : Series α) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    seriesWeight (conv f g) r N ≤ seriesWeight f r N * seriesWeight g r N := by
  apply (truncEval_le hr (degreeNorm_conv_le f g) N).trans
  exact truncEval_conv_le (degreeNorm_nonneg f) (degreeNorm_nonneg g) hr N
 theorem seriesWeight_subst_le (M f : Series α) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    seriesWeight (subst M f) r N ≤
      ∑ k ∈ range (N+1), degreeNorm f k * (r * seriesWeight M r N)^k := by
  apply (truncEval_le hr (fun k => ?_) N).trans
  · exact substBound_trunc_le (degreeNorm_nonneg M) (degreeNorm_nonneg f) hr N le_rfl
  · have h := vsubst_norm_le k M f
    change degreeNorm (vsubst M f) k ≤ substBound (degreeNorm M) (degreeNorm f) k at h
    rw [vsubst_scalar] at h
    exact h

end FiniteEntropySeparation.FreeSeries

end

end OAI
