import OAI.NumberTheory.TwoPoint.Halasz.HalaszLogBilinear
import OAI.NumberTheory.TwoPoint.Halasz.HalaszShiftAveraging

namespace OAI

/-! From a normalized logarithmic polynomial bound to the actual ordinary
exponential sum, with both Taylor and shift-boundary errors retained. -/
namespace TwoPointCorrelations

open Complex Finset

theorem halasz_log_shift_bound (k H M : ℕ) (hM : 1≤M) (t : ℝ)
    {x A : ℝ} (hx : 0<x) (hMx : (M:ℝ)^2≤x/2)
    (hpoly : ∀ n∈range H,
      ‖∑ b : Fin M,halaszVinogradovPolynomial k M
        (halaszScaledFrequency (halaszLogCoefficient t (x+n))
          (fun j => (((b.val+1)^(j.val+1):ℕ):ℤ)))‖/(M:ℝ)^2≤A) :
    ‖∑ n∈range H,Complex.exp (Complex.I*((t*Real.log (x+n):ℝ):ℂ))‖≤
      (H:ℝ)*(A+2*|t| *((M:ℝ)^2/x)^(k+1))+2*(M:ℝ)^2 := by
  let f : ℕ → ℂ := fun n => Complex.exp (Complex.I*((t*Real.log (x+n):ℝ):ℂ))
  let T := 2*|t| *((M:ℝ)^2/x)^(k+1)
  have hM0 : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have hM2 : 0<(M:ℝ)^2 := sq_pos_of_pos hM0
  have hf : ∀ n,‖f n‖≤1 := by
    intro n
    dsimp only [f]
    rw [Complex.norm_exp_I_mul_ofReal]
  have hB : ∀ n∈range H,‖∑ a : Fin M,∑ b : Fin M,
      f (n+(a.val+1)*(b.val+1))‖≤(M:ℝ)^2*(A+T) := by
    intro n hn
    have hxn : 0<x+n := by positivity
    have hlocal := halasz_log_bilinear_taylor k M M t hxn
      (by push_cast; nlinarith [show (0:ℝ)≤n by positivity])
    have hp := (div_le_iff₀ hM2).mp (hpoly n hn)
    have hquot : (M:ℝ)^2/(x+n)≤(M:ℝ)^2/x :=
      div_le_div_of_nonneg_left (sq_nonneg _) hx (by linarith [show (0:ℝ)≤n from Nat.cast_nonneg n])
    have herror := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity : 0≤(M:ℝ)^2/(x+n)) hquot (k+1))
      (by positivity : 0≤2*|t|)
    have heq : (∑ a : Fin M,∑ b : Fin M,f (n+(a.val+1)*(b.val+1)))=
        ∑ b : Fin M,∑ a : Fin M,Complex.exp
          (Complex.I*((t*Real.log ((x+n)+(a.val+1)*(b.val+1)):ℝ):ℂ)) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro a _
      dsimp only [f]
      congr 3
      push_cast
      ring_nf
    rw [heq]
    apply hlocal.trans
    push_cast at hp hlocal ⊢
    simp only [← pow_two] at hp hlocal ⊢
    have hE := mul_le_mul_of_nonneg_left herror (sq_nonneg (M:ℝ))
    dsimp only [T] at *
    nlinarith
  have hh := halasz_double_shift_averaging f hf H M M ((M:ℝ)^2*(A+T)) hB
  dsimp only [f] at hh
  apply (mul_le_mul_iff_right₀ hM2).mp
  convert hh using 1
  · push_cast
    ring
  · dsimp only [T]
    push_cast
    ring

end TwoPointCorrelations

end OAI
