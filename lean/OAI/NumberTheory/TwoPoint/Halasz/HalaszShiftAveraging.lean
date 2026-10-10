import OAI.NumberTheory.TwoPoint.Halasz.HalaszFiniteHolder

namespace OAI

/-! Averaging short multiplicative shifts of a one-bounded sequence. -/
namespace TwoPointCorrelations

open Finset

lemma halasz_short_shift_error (f : ℕ → ℂ) (hf : ∀ n,‖f n‖≤1) (N d : ℕ) :
    ‖(∑ n∈range N,f (n+d))-(∑ n∈range N,f n)‖≤2*d := by
  have he : (∑ n∈range N,f (n+d))-(∑ n∈range N,f n)=
      (∑ n∈range d,f (n+N))-(∑ n∈range d,f n) := by
    have h1 := sum_range_add f N d
    have h2 := sum_range_add f d N
    rw [Nat.add_comm d N] at h2
    have hh := h1.symm.trans h2
    simp_rw [Nat.add_comm] at hh ⊢
    linear_combination -hh
  rw [he]
  have h1 : ‖∑ n∈range d,f (n+N)‖≤d := by
    calc
      _ ≤ ∑ n∈range d,‖f (n+N)‖ := norm_sum_le _ _
      _ ≤ ∑ _n∈range d,(1:ℝ) := sum_le_sum (fun _ _ => hf _)
      _ = _ := by simp
  have h2 : ‖∑ n∈range d,f n‖≤d := by
    calc
      _ ≤ ∑ n∈range d,‖f n‖ := norm_sum_le _ _
      _ ≤ ∑ _n∈range d,(1:ℝ) := sum_le_sum (fun _ _ => hf _)
      _ = _ := by simp
  exact (norm_sub_le _ _).trans (by linarith)

theorem halasz_double_shift_averaging (f : ℕ → ℂ) (hf : ∀ n,‖f n‖≤1)
    (N M₁ M₂ : ℕ) (B : ℝ)
    (hB : ∀ n∈range N, ‖∑ a : Fin M₁,∑ b : Fin M₂,
      f (n+(a.val+1)*(b.val+1))‖≤B) :
    ((M₁*M₂:ℕ):ℝ)*‖∑ n∈range N,f n‖≤(N:ℝ)*B+2*((M₁*M₂:ℕ):ℝ)^2 := by
  let S := ∑ n∈range N,f n
  let T := ∑ a : Fin M₁,∑ b : Fin M₂,∑ n∈range N,f (n+(a.val+1)*(b.val+1))
  have he : T=∑ n∈range N,∑ a : Fin M₁,∑ b : Fin M₂,
      f (n+(a.val+1)*(b.val+1)) := by
    calc
      _ = ∑ a : Fin M₁,∑ n∈range N,∑ b : Fin M₂,f (n+(a.val+1)*(b.val+1)) := by
        apply sum_congr rfl
        intro a _
        rw [sum_comm]
      _ = _ := sum_comm
  have hT : ‖T‖≤(N:ℝ)*B := by
    rw [he]
    apply (norm_sum_le _ _).trans
    exact (sum_le_sum hB).trans_eq (by simp)
  have herror : ‖T-((M₁*M₂:ℕ):ℂ)*S‖≤2*((M₁*M₂:ℕ):ℝ)^2 := by
    have he' : T-((M₁*M₂:ℕ):ℂ)*S=
        ∑ a : Fin M₁,∑ b : Fin M₂,((∑ n∈range N,
          f (n+(a.val+1)*(b.val+1)))-S) := by
      simp only [T,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_mul]
      ring
    rw [he']
    apply (norm_sum_le _ _).trans
    apply (sum_le_sum (fun _ _ => norm_sum_le _ _)).trans
    calc
      _ ≤ ∑ _a : Fin M₁,∑ _b : Fin M₂,2*((M₁*M₂:ℕ):ℝ) := by
        apply sum_le_sum
        intro a _
        apply sum_le_sum
        intro b _
        have hh := halasz_short_shift_error f hf N ((a.val+1)*(b.val+1))
        have hab : (a.val+1)*(b.val+1)≤M₁*M₂ := Nat.mul_le_mul (by omega) (by omega)
        exact hh.trans (by exact_mod_cast Nat.mul_le_mul_left 2 hab)
      _ = _ := by simp [pow_two]; ring
  calc
    _ = ‖((M₁*M₂:ℕ):ℂ)*S‖ := by rw [norm_mul,Complex.norm_natCast]
    _ = ‖T+(((M₁*M₂:ℕ):ℂ)*S-T)‖ := by congr 1; ring
    _ ≤ ‖T‖+‖((M₁*M₂:ℕ):ℂ)*S-T‖ := norm_add_le _ _
    _ = ‖T‖+‖T-((M₁*M₂:ℕ):ℂ)*S‖ := by rw [norm_sub_rev]
    _ ≤ _ := add_le_add hT herror

end TwoPointCorrelations

end OAI
