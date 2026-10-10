import Mathlib

namespace OAI

open Matrix

namespace CurrentKS.RationalOptimization
noncomputable section
open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma exact_step_decrease (y c v : E) {r : ℝ} (hr : 0 ≤ r)
    (hv : ‖v‖ ≤ 1) (hsep : r ≤ inner ℝ v (c-y)) :
    ‖y+r • v-c‖^2 ≤ ‖y-c‖^2-r^2 := by
  have he : y+r • v-c = (y-c)+r • v := by abel
  rw [he,norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
  have hi : inner ℝ (y-c) v ≤ -r := by
    rw [real_inner_comm] at hsep
    have hh : inner ℝ (y-c) v = -(inner ℝ (c-y) v) := by
      rw [← inner_neg_left]
      congr 1
      abel
    linarith
  have hv0 := norm_nonneg v
  have hv2 : ‖v‖^2 ≤ 1 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hi hr
  have ht := mul_le_mul_of_nonneg_left hv2 (sq_nonneg r)
  nlinarith

lemma rounded_step_decrease (y c v y' : E) {r R δ : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hy : ‖y-c‖ ≤ R)
    (hv : ‖v‖ ≤ 1) (hsep : r ≤ inner ℝ v (c-y))
    (hround : ‖y'-(y+r • v)‖ ≤ δ)
    (hsmall : 2*(R+r)*δ+δ^2 ≤ r^2/2) :
    ‖y'-c‖^2 ≤ ‖y-c‖^2-r^2/2 := by
  have hstep := exact_step_decrease y c v hr hv hsep
  have hnorm : ‖y+r • v-c‖ ≤ R+r := by
    have he : y+r • v-c = (y-c)+r • v := by abel
    rw [he]
    calc
      _ ≤ ‖y-c‖+‖r • v‖ := norm_add_le _ _
      _ ≤ R+r := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]; nlinarith
  have hn : ‖y'-c‖ ≤ ‖y+r • v-c‖+δ := by
    calc
      _ = ‖(y+r • v-c)+(y'-(y+r • v))‖ := by congr 1; abel
      _ ≤ ‖y+r • v-c‖+‖y'-(y+r • v)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_right hround _
  have hn0 := norm_nonneg (y+r • v-c)
  have hn' := sq_le_sq₀ (norm_nonneg (y'-c)) (add_nonneg hn0 hδ) |>.mpr hn
  have hh := mul_le_mul hnorm (le_refl δ) hδ (add_nonneg hR hr)
  nlinarith

lemma separating_margin (K : Set E) (c y v : E) {r b : ℝ}
    (hr : 0 ≤ r) (hball : Metric.closedBall c r ⊆ K)
    (hv : ‖v‖ = 1) (hsep : ∀ z ∈ K, b ≤ inner ℝ v z)
    (hy : inner ℝ v y ≤ b) : r ≤ inner ℝ v (c-y) := by
  have hz : c-r • v ∈ Metric.closedBall c r := by
    rw [Metric.mem_closedBall,dist_eq_norm]
    have he : c-r • v-c = -(r • v) := by abel
    rw [he,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,hv,mul_one]
  have hs := hsep _ (hball hz)
  rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hv] at hs
  rw [inner_sub_right]
  nlinarith

omit [InnerProductSpace ℝ E] in
theorem exists_hit_of_sq_decrease (K : Set E) (next : E → E) (x c : E)
    {R q : ℝ} (hq : 0 < q) (hx : ‖x-c‖^2 ≤ R^2)
    (hnext : ∀ y, y ∉ K → ‖y-c‖^2 ≤ R^2 → ‖next y-c‖^2 ≤ ‖y-c‖^2-q)
    (T : ℕ) (hT : R^2 < T*q) :
    ∃ k ≤ T, (next^[k]) x ∈ K := by
  by_contra! hfail
  have hbound : ∀ k ≤ T, ‖(next^[k]) x-c‖^2 ≤ R^2-k*q := by
    intro k hk
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have hk' : k ≤ T := Nat.le_trans (Nat.le_succ k) hk
      have hi := ih hk'
      have hs := hnext ((next^[k]) x) (hfail k hk') (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
      rw [Function.iterate_succ_apply']
      push_cast
      linarith
  have hb := hbound T le_rfl
  nlinarith [sq_nonneg ‖(next^[T]) x-c‖]

end
end CurrentKS.RationalOptimization

end OAI
