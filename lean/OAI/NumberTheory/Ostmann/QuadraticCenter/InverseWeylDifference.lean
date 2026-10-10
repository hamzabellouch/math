import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylPhase

namespace OAI

namespace Ostmann.QuadraticCenter
open Finset
open scoped ComplexConjugate

theorem weylPhase_conj (x : ℝ) : conj (weylPhase x) = weylPhase (-x) := by
  simp only [weylPhase, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

theorem complex_sum_norm_sq_triangle (z : ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ range N, z n‖^2 = (∑ n ∈ range N, ‖z n‖^2)+
      2*∑ j ∈ range N, ∑ i ∈ range j, (conj (z i)*z j).re := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hc : (inner ℂ (∑ i ∈ range N, z i) (z N)).re =
        ∑ i ∈ range N, (conj (z i)*z N).re := by
      simp [mul_comm,mul_sum,sum_add_distrib]
    rw [sum_range_succ,norm_add_sq (𝕜 := ℂ),ih]
    simp only [RCLike.re_to_complex]
    rw [hc,sum_range_succ,sum_range_succ]
    ring

theorem sum_triangle_displacement {R : Type*} [AddCommMonoid R]
    (g : ℕ → ℕ → R) (N : ℕ) :
    (∑ j ∈ range (N+1), ∑ i ∈ range j, g j i) =
      ∑ h ∈ range N, ∑ i ∈ range (N-h), g (i+h+1) i := by
  rw [sum_sigma', sum_sigma']
  apply sum_bij (fun a _ => ⟨a.1-a.2-1,a.2⟩)
  · intro a ha
    simp only [mem_sigma, mem_range] at ha ⊢
    omega
  · intro a ha b hb he
    simp only [mem_sigma, mem_range] at ha hb
    have h1 := congrArg Sigma.fst he
    have h2 : a.2 = b.2 := by cases a; cases b; simpa using congrArg Sigma.snd he
    obtain ⟨a1,a2⟩ := a
    obtain ⟨b1,b2⟩ := b
    simp only at ha hb h1 h2
    have : a1=b1 := by omega
    subst b1
    subst b2
    rfl
  · intro b hb
    simp only [mem_sigma, mem_range] at hb
    refine ⟨⟨b.2+b.1+1,b.2⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_range]
      omega
    · have h : b.2+b.1+1-b.2-1 = b.1 := by omega
      cases b
      simp only [h]
  · intro a ha
    simp only [mem_sigma, mem_range] at ha
    have h : a.2+(a.1-a.2-1)+1 = a.1 := by omega
    simp only [h]

noncomputable def quadraticWeylSum (alpha beta start : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ range N, weylPhase (alpha*(start+n)^2+beta*(start+n))

theorem quadratic_correlation_norm (alpha beta start : ℝ) (h M : ℕ) :
    ‖∑ i ∈ range M,
      conj (weylPhase (alpha*(start+i)^2+beta*(start+i))) *
        weylPhase (alpha*(start+(i+h+1:ℕ))^2+beta*(start+(i+h+1:ℕ)))‖ =
      ‖∑ i ∈ range M, weylPhase ((i:ℝ)*(2*alpha*(h+1)))‖ := by
  let c : ℝ := alpha*((h+1:ℕ):ℝ)^2+2*alpha*start*(h+1)+beta*(h+1)
  have ht (i : ℕ) :
      conj (weylPhase (alpha*(start+i)^2+beta*(start+i))) *
        weylPhase (alpha*(start+(i+h+1:ℕ))^2+beta*(start+(i+h+1:ℕ))) =
      weylPhase c*weylPhase ((i:ℝ)*(2*alpha*(h+1))) := by
    rw [weylPhase_conj, ← weylPhase_add, ← weylPhase_add]
    congr 1
    dsimp [c]
    push_cast
    ring
  simp_rw [ht]
  rw [← mul_sum, norm_mul, weylPhase_norm, one_mul]

theorem quadratic_weyl_differencing (alpha beta start : ℝ) (N : ℕ) :
    ‖quadraticWeylSum alpha beta start (N+1)‖^2 ≤ (N+1:ℝ)+
      2*∑ h ∈ range N, ‖∑ i ∈ range (N-h), weylPhase ((i:ℝ)*(2*alpha*(h+1)))‖ := by
  rw [quadraticWeylSum, complex_sum_norm_sq_triangle]
  simp only [weylPhase_norm, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
  rw [sum_triangle_displacement]
  simp only [Nat.cast_add, Nat.cast_one]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply sum_le_sum
  intro h hh
  have hr := Complex.re_le_norm (∑ i ∈ range (N-h),
    conj (weylPhase (alpha*(start+i)^2+beta*(start+i))) *
      weylPhase (alpha*(start+(i+h+1:ℕ))^2+beta*(start+(i+h+1:ℕ))))
  rw [quadratic_correlation_norm] at hr
  simpa only [Complex.re_sum, Nat.cast_add, Nat.cast_one] using hr

end Ostmann.QuadraticCenter

end OAI
