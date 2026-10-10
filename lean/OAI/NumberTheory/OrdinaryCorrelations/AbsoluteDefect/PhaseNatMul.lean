import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryAdditiveBilinear

def phase (x : ℝ) : ℂ := Complex.exp ((2*Real.pi*x:ℝ)*Complex.I)

lemma norm_phase (x : ℝ) : ‖phase x‖=1 := by
  simp [phase,Complex.norm_exp]

lemma phase_nat_mul (x : ℝ) (n : ℕ) : phase (x*n)=phase x^n := by
  unfold phase
  rw [←Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma abel_identity (u : ℕ → ℂ) (z : ℂ) (N : ℕ) :
    (1-z)*(∑n∈range (N+1),u n*z^n) =
      u 0+(∑n∈range N,(u (n+1)-u n)*z^(n+1))-u N*z^(N+1) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
    rw [sum_range_succ,mul_add,ih,sum_range_succ]
    simp only [pow_succ]
    ring

lemma abel_bound_succ (u : ℕ → ℂ) {z : ℂ} (hz : ‖z‖=1)
    {K δ : ℝ} (hK : 0≤K) (hδ : 0≤δ)
    (hu : ∀n,‖u n‖≤K) (hv : ∀n,‖u (n+1)-u n‖≤δ) (N : ℕ) :
    ‖1-z‖*‖∑n∈range (N+1),u n*z^n‖≤2*K+(N:ℝ)*δ := by
  rw [←norm_mul,abel_identity]
  have hs : ‖∑n∈range N,(u (n+1)-u n)*z^(n+1)‖≤(N:ℝ)*δ := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑n∈range N,δ := by
        apply sum_le_sum
        intro n hn
        simpa only [norm_mul,mul_one] using
          mul_le_mul (hv n) (by simp [norm_pow,hz] : ‖z^(n+1)‖ ≤ 1)
            (norm_nonneg _) hδ
      _ = _ := by simp
  have ht : ‖u N*z^(N+1)‖≤K := by
    simpa only [norm_mul,mul_one] using
      mul_le_mul (hu N) (by simp [norm_pow,hz] : ‖z^(N+1)‖ ≤ 1)
        (norm_nonneg _) hK
  calc
    _ ≤ ‖u 0+(∑n∈range N,(u (n+1)-u n)*z^(n+1))‖+‖u N*z^(N+1)‖ := norm_sub_le _ _
    _ ≤ (‖u 0‖+‖∑n∈range N,(u (n+1)-u n)*z^(n+1)‖)+‖u N*z^(N+1)‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ 2*K+(N:ℝ)*δ := by linarith [hu 0]

theorem abel_bound (u : ℕ → ℂ) {z : ℂ} (hz : ‖z‖=1)
    {K δ : ℝ} (hK : 0≤K) (hδ : 0≤δ)
    (hu : ∀n,‖u n‖≤K) (hv : ∀n,‖u (n+1)-u n‖≤δ) (N : ℕ) :
    ‖1-z‖*‖∑n∈range N,u n*z^n‖≤2*K+(N:ℝ)*δ := by
  cases N with
  | zero => simp; positivity
  | succ N =>
    have hh := abel_bound_succ u hz hK hδ hu hv N
    push_cast
    nlinarith

def smooth (u : ℕ → ℂ) (D n : ℕ) : ℂ := (D:ℂ)⁻¹*∑j∈range D,u (n+j)

lemma smooth_bound (u : ℕ → ℂ) (hu : ∀n,‖u n‖≤1) (D n : ℕ) :
    ‖smooth u D n‖≤1 := by
  by_cases hD : D=0
  · simp [smooth,hD]
  have hn : ‖∑j∈range D,u (n+j)‖≤(D:ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑j∈range D,(1:ℝ) := sum_le_sum (fun j hj => hu (n+j))
      _ = _ := by simp
  calc
    _ = (D:ℝ)⁻¹*‖∑j∈range D,u (n+j)‖ := by simp [smooth]
    _ ≤ (D:ℝ)⁻¹*(D:ℝ) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = 1 := inv_mul_cancel₀ (by exact_mod_cast hD)

lemma smooth_difference (u : ℕ → ℂ) (D n : ℕ) :
    smooth u D (n+1)-smooth u D n=(D:ℂ)⁻¹*(u (n+D)-u n) := by
  unfold smooth
  rw [←mul_sub,←sum_sub_distrib]
  congr 1
  have hh := sum_range_sub (fun j => u (n+j)) D
  simpa only [Nat.add_zero,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh

lemma smooth_step_bound (u : ℕ → ℂ) (hu : ∀n,‖u n‖≤1) (D n : ℕ) :
    ‖smooth u D (n+1)-smooth u D n‖≤2/(D:ℝ) := by
  rw [smooth_difference,norm_mul,norm_inv,Complex.norm_natCast]
  have hn : ‖u (n+D)-u n‖≤2 := (norm_sub_le _ _).trans (by linarith [hu (n+D),hu n])
  calc
    _ ≤ (D:ℝ)⁻¹*2 := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := by ring

lemma step_to_stride (w : ℕ → ℂ) {δ : ℝ}
    (hw : ∀n,‖w (n+1)-w n‖≤δ) (n d : ℕ) :
    ‖w (n+d)-w n‖≤(d:ℝ)*δ := by
  induction d with
  | zero => simp
  | succ d ih =>
    have he : w (n+(d+1))-w n=(w ((n+d)+1)-w (n+d))+(w (n+d)-w n) := by
      rw [Nat.add_assoc]
      ring
    rw [he]
    calc
      _ ≤ ‖w ((n+d)+1)-w (n+d)‖+‖w (n+d)-w n‖ := norm_add_le _ _
      _ ≤ δ+(d:ℝ)*δ := add_le_add (hw (n+d)) ih
      _ = _ := by push_cast; ring

lemma product_step_bound (w : ℕ → ℂ) {δ : ℝ} (hδ : 0≤δ)
    (hw : ∀n,‖w n‖≤1) (hv : ∀n,‖w (n+1)-w n‖≤δ) (p q a n : ℕ) :
    ‖w (p*(a+(n+1)))*star (w (q*(a+(n+1))))-
      w (p*(a+n))*star (w (q*(a+n)))‖≤((p:ℝ)+q)*δ := by
  let x := p*(a+n)
  let y := q*(a+n)
  have hp : p*(a+(n+1))=x+p := by dsimp [x]; ring
  have hq : q*(a+(n+1))=y+q := by dsimp [y]; ring
  rw [hp,hq]
  have he : w (x+p)*star (w (y+q))-w x*star (w y)=
      (w (x+p)-w x)*star (w (y+q))+w x*star (w (y+q)-w y) := by
    simp only [star_sub]
    ring
  rw [he]
  have hu := step_to_stride w hv x p
  have hv' := step_to_stride w hv y q
  calc
    _ ≤ ‖(w (x+p)-w x)*star (w (y+q))‖+‖w x*star (w (y+q)-w y)‖ := norm_add_le _ _
    _ = ‖w (x+p)-w x‖*‖w (y+q)‖+‖w x‖*‖w (y+q)-w y‖  := by simp only [norm_mul,norm_star]
    _ ≤ (p:ℝ)*δ*1+1*((q:ℝ)*δ) := by
      exact add_le_add (mul_le_mul hu (hw (y+q)) (norm_nonneg _) (by positivity))
        (mul_le_mul (hw x) hv' (norm_nonneg _) (by positivity))
    _ = _ := by ring

theorem smoothed_cross_phase (u : ℕ → ℂ) (hu : ∀n,‖u n‖≤1)
    (D p q a N : ℕ) (α : ℝ) :
    ‖1-phase (α*((p:ℝ)-q))‖*
      ‖∑n∈range N, (smooth u D (p*(a+n))*star (smooth u D (q*(a+n))))*
        phase (α*((p:ℝ)-q)*(n:ℝ))‖ ≤
      2+(N:ℝ)*(((p:ℝ)+q)*(2/(D:ℝ))) := by
  simp_rw [phase_nat_mul]
  let w := smooth u D
  have hb : ∀n,‖w (p*(a+n))*star (w (q*(a+n)))‖≤1 := by
    intro n
    simp only [norm_mul,norm_star]
    exact (mul_le_mul_of_nonneg_right (smooth_bound u hu D _) (norm_nonneg _)).trans
      (by simpa only [one_mul] using smooth_bound u hu D _)
  have hv : ∀n,‖w (p*(a+(n+1)))*star (w (q*(a+(n+1))))-
      w (p*(a+n))*star (w (q*(a+n)))‖≤((p:ℝ)+q)*(2/(D:ℝ)) := by
    intro n
    exact product_step_bound (smooth u D) (by positivity)
      (smooth_bound u hu D) (smooth_step_bound u hu D) p q a n
  simpa only [mul_one] using abel_bound (fun n => w (p*(a+n))*star (w (q*(a+n))))
    (norm_phase (α*((p:ℝ)-q))) (K:=1) (δ:=((p:ℝ)+q)*(2/(D:ℝ)))
    (by norm_num) (by positivity) hb hv N

end OrdinaryAdditiveBilinear

end

end OAI
