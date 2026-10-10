import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

namespace OAI

/-! Quantitative inexact Euler estimates. All error assumptions concern
the vector field and the actual local differential equation; no endpoint
approximation is assumed. -/

noncomputable section
namespace ContinuumCoulomb.EulerApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def iterate (h : ℝ) (evaluate : ℕ → E → E) (x₀ : E) : ℕ → E
  | 0 => x₀
  | n+1 => iterate h evaluate x₀ n + h • evaluate n (iterate h evaluate x₀ n)

theorem step_error (v evaluate : ℕ → E → E) (z : ℕ → E)
    (x : E) (n : ℕ) {h L δ D : ℝ} (hh : 0 ≤ h)
    (hLip : ‖v n x-v n (z n)‖ ≤ L*‖x-z n‖)
    (heval : ‖evaluate n x-v n x‖ ≤ δ)
    (hdefect : ‖z n+h • v n (z n)-z (n+1)‖ ≤ D) :
    ‖x+h • evaluate n x-z (n+1)‖ ≤ (1+h*L)*‖x-z n‖+h*δ+D := by
  have hid : x+h • evaluate n x-z (n+1) =
      (x-z n) + h • (evaluate n x-v n (z n)) + (z n+h • v n (z n)-z (n+1)) := by
    module
  have hv : ‖evaluate n x-v n (z n)‖ ≤ δ+L*‖x-z n‖ := by
    have heq : evaluate n x-v n (z n) = (evaluate n x-v n x)+(v n x-v n (z n)) := by abel
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add heval hLip)
  rw [hid]
  calc
    _ ≤ ‖x-z n‖+‖h • (evaluate n x-v n (z n))‖+‖z n+h • v n (z n)-z (n+1)‖ :=
      by
        have h₁ := norm_add_le ((x-z n)+h • (evaluate n x-v n (z n)))
          (z n+h • v n (z n)-z (n+1))
        have h₂ := norm_add_le (x-z n) (h • (evaluate n x-v n (z n)))
        linarith
    _ ≤ ‖x-z n‖+h*(δ+L*‖x-z n‖)+D := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh]
      gcongr
    _ = _ := by ring

theorem finite_recurrence_bound (u : ℕ → ℝ) (N : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u 0)
    (hstep : ∀ k < N, u (k+1) ≤ (1+a)*u k+b) :
    ∀ n ≤ N, u n ≤ (u 0+(n:ℝ)*b)*Real.exp ((n:ℝ)*a) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hnk : n < N := by omega
    have hprev := ih (Nat.le_of_lt hnk)
    have hbase : 0 ≤ u 0+(n:ℝ)*b := add_nonneg hu (mul_nonneg (Nat.cast_nonneg _) hb)
    have hfac : (1+a)*Real.exp ((n:ℝ)*a) ≤ Real.exp (((n:ℝ)+1)*a) := by
      calc
        _ ≤ Real.exp a*Real.exp ((n:ℝ)*a) :=
          mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp a]) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hexp : 1 ≤ Real.exp (((n:ℝ)+1)*a) :=
      Real.one_le_exp_iff.mpr (mul_nonneg (by positivity) ha)
    calc
      u (n+1) ≤ (1+a)*u n+b := hstep n hnk
      _ ≤ (1+a)*((u 0+(n:ℝ)*b)*Real.exp ((n:ℝ)*a))+b := by gcongr
      _ = (u 0+(n:ℝ)*b)*((1+a)*Real.exp ((n:ℝ)*a))+b := by ring
      _ ≤ (u 0+(n:ℝ)*b)*Real.exp (((n:ℝ)+1)*a)+b*Real.exp (((n:ℝ)+1)*a) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hfac hbase)
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hb)
      _ = (u 0+((n+1:ℕ):ℝ)*b)*Real.exp (((n+1:ℕ):ℝ)*a) := by
        push_cast
        ring

theorem iterate_error (v evaluate : ℕ → E → E) (z : ℕ → E) (x₀ : E)
    (N : ℕ) {h L δ D : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hD : 0 ≤ D)
    (hLip : ∀ n < N, ∀ x, ‖v n x-v n (z n)‖ ≤ L*‖x-z n‖)
    (heval : ∀ n < N, ∀ x, ‖evaluate n x-v n x‖ ≤ δ)
    (hdefect : ∀ n < N, ‖z n+h • v n (z n)-z (n+1)‖ ≤ D) :
    ‖iterate h evaluate x₀ N-z N‖ ≤
      (‖x₀-z 0‖+(N:ℝ)*(h*δ+D))*Real.exp ((N:ℝ)*(h*L)) := by
  let u : ℕ → ℝ := fun n => ‖iterate h evaluate x₀ n-z n‖
  have hb : 0 ≤ h*δ+D := add_nonneg (mul_nonneg hh hδ) hD
  have hs (n : ℕ) (hn : n < N) : u (n+1) ≤ (1+h*L)*u n+(h*δ+D) := by
    exact (step_error v evaluate z (iterate h evaluate x₀ n) n hh
      (hLip n hn _) (heval n hn _) (hdefect n hn)).trans_eq (by ring)
  exact finite_recurrence_bound u N (mul_nonneg hh hL) hb (norm_nonneg _) hs N le_rfl

/-- The actual solution has a quadratic one-step error whenever its
velocity is bounded and the field is jointly Lipschitz in time and space. -/
theorem local_defect (v : ℝ → E → E) (z : ℝ → E)
    {t h L M : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hz : ∀ s ∈ Set.Icc t (t+h),
      HasDerivWithinAt z (v s (z s)) (Set.Icc t (t+h)) s)
    (hbound : ∀ s ∈ Set.Icc t (t+h), ‖v s (z s)‖ ≤ M)
    (hLip : ∀ s ∈ Set.Icc t (t+h),
      ‖v s (z s)-v t (z t)‖ ≤ L*(|s-t|+‖z s-z t‖)) :
    ‖z t+h • v t (z t)-z (t+h)‖ ≤ L*(1+M)*h^2 := by
  have hab : t ≤ t+h := by linarith
  have hspeed (s : ℝ) (hs : s ∈ Set.Icc t (t+h)) : ‖z s-z t‖ ≤ M*(s-t) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hz
      (fun r hr => hbound r ⟨hr.1,hr.2.le⟩) s hs
  let F : ℝ → E := fun s => z s-(s-t) • v t (z t)
  have hF (s : ℝ) (hs : s ∈ Set.Icc t (t+h)) :
      HasDerivWithinAt F (v s (z s)-v t (z t)) (Set.Icc t (t+h)) s := by
    have hlin : HasDerivAt (fun r : ℝ => (r-t) • v t (z t)) (v t (z t)) s := by
      simpa only [id_eq,one_smul] using ((hasDerivAt_id s).sub_const t).smul_const (v t (z t))
    exact (hz s hs).sub hlin.hasDerivWithinAt
  have hderiv (s : ℝ) (hs : s ∈ Set.Ico t (t+h)) :
      ‖v s (z s)-v t (z t)‖ ≤ L*(1+M)*h := by
    have hs' : s ∈ Set.Icc t (t+h) := ⟨hs.1,hs.2.le⟩
    have hnorm := hspeed s hs'
    have habs : |s-t| = s-t := abs_of_nonneg (sub_nonneg.mpr hs.1)
    calc
      _ ≤ L*(|s-t|+‖z s-z t‖) := hLip s hs'
      _ ≤ L*((s-t)+M*(s-t)) := by rw [habs]; gcongr
      _ = L*(1+M)*(s-t) := by ring
      _ ≤ L*(1+M)*h := mul_le_mul_of_nonneg_left (by linarith [hs.2]) (by positivity)
  have hest := norm_image_sub_le_of_norm_deriv_le_segment' hF hderiv (t+h) ⟨hab,le_rfl⟩
  have hid : F (t+h)-F t = -(z t+h • v t (z t)-z (t+h)) := by
    dsimp [F]
    simp only [add_sub_cancel_left,sub_self,zero_smul,sub_zero]
    abel
  rw [hid,norm_neg] at hest
  convert hest using 1
  ring

end ContinuumCoulomb.EulerApproximation

end

end OAI
