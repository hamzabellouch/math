import OAI.Analysis.LipschitzHilbert.Fourier.SincMaskSpectrum
import OAI.Analysis.LipschitzHilbert.Fourier.SincMaskSchwartz
import OAI.Analysis.LipschitzHilbert.Packets.LinePacketReplacement

namespace OAI

/-! Exact sinc-masked synthesis waves retain the analyzing budget and
have a factor-two envelope constant when their derivative bandwidth is
at most the packet's inverse length. -/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace LipschitzHilbert.LinePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : LinePacketFamily N κ ι) (n : ℕ)
  (a b c d : ∀ j, ι j → κ → ℝ)

private theorem sincMasked_bound (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
    ‖sincProductSchwartz (P.wave j u k) n (a j u k) (b j u k) (c j u k) (d j u k) x‖ ≤
      (2*P.constant)*(lineEnvelope (P.centerX j u) (P.length j) 3 x*
        lineEnvelope (P.centerZ j u) P.width 2 P.lineY) := by
  apply (sincProductSchwartz_norm_le (P.wave j u k) n _ _ _ _ x).trans
  apply (P.wave_bound j u k x).trans
  exact mul_le_mul_of_nonneg_right (by linarith [P.constant_pos])
    (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))

private theorem sincMasked_deriv
    (hband : ∀ j u k, 2*(n:ℝ)*(|a j u k|+|c j u k|) ≤ 1/P.length j)
    (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
    ‖deriv (sincProductSchwartz (P.wave j u k) n (a j u k) (b j u k) (c j u k) (d j u k)) x‖ ≤
      ((2*P.constant)/P.length j)*(lineEnvelope (P.centerX j u) (P.length j) 3 x*
        lineEnvelope (P.centerZ j u) P.width 2 P.lineY) := by
  let E := lineEnvelope (P.centerX j u) (P.length j) 3 x*
    lineEnvelope (P.centerZ j u) P.width 2 P.lineY
  have hE : 0 ≤ E := mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  calc
    _ ≤ ‖deriv (P.wave j u k) x‖+
        (2*(n:ℝ)*(|a j u k|+|c j u k|))*‖P.wave j u k x‖ :=
      sincProductSchwartz_deriv_le (P.wave j u k) n _ _ _ _ x
    _ ≤ (P.constant/P.length j)*E+
        (2*(n:ℝ)*(|a j u k|+|c j u k|))*(P.constant*E) :=
      add_le_add (P.deriv_bound j u k x)
        (mul_le_mul_of_nonneg_left (P.wave_bound j u k x) (by positivity))
    _ ≤ (P.constant/P.length j)*E+(1/P.length j)*(P.constant*E) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (hband j u k)
        (mul_nonneg P.constant_pos.le hE))
    _ = _ := by dsimp only [E]; ring

/-- Only the synthesis waves change. Coefficients and all lattice
geometry are retained literally. -/
def sincMasked
    (hband : ∀ j u k, 2*(n:ℝ)*(|a j u k|+|c j u k|) ≤ 1/P.length j) :
    LinePacketFamily N κ ι :=
  P.replaceWaves (2*P.constant) (mul_pos (by norm_num) P.constant_pos)
    (fun j u k => sincProductSchwartz (P.wave j u k) n (a j u k) (b j u k) (c j u k) (d j u k))
    (P.sincMasked_bound n a b c d) (P.sincMasked_deriv n a b c d hband)

variable (hband : ∀ j u k, 2*(n:ℝ)*(|a j u k|+|c j u k|) ≤ 1/P.length j)

@[simp] theorem sincMasked_coeff (j : Fin N) (u : ι j) :
    (P.sincMasked n a b c d hband).coeff j u = P.coeff j u := rfl

@[simp] theorem sincMasked_wave (j : Fin N) (u : ι j) (k : κ) (x : ℝ) :
    (P.sincMasked n a b c d hband).wave j u k x =
      (sincProductMask n (a j u k*x+b j u k) (c j u k*x+d j u k):ℂ)*P.wave j u k x :=
  sincProductSchwartz_apply (P.wave j u k) n _ _ _ _ x

theorem sincMasked_budget {B : ℝ} (hB : P.HasLocalBudget B) :
    (P.sincMasked n a b c d hband).HasLocalBudget B := hB

/-- Uniform annuli are weakened by precisely the mask bandwidth. -/
theorem sincMasked_cutoffs (lo hi delta : ℝ)
    (hdelta : ∀ j u k, (2*(n:ℝ))*((|a j u k|+|c j u k|)/(2*Real.pi)) ≤ delta*(2:ℝ)^j.val)
    (hlow : ∀ j u k xi, |xi| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j u k) xi = 0)
    (hhigh : ∀ j u k xi, hi*(2:ℝ)^j.val < |xi| → 𝓕 (P.wave j u k) xi = 0) :
    (∀ j u k xi, |xi| < (lo-delta)*(2:ℝ)^j.val →
      𝓕 ((P.sincMasked n a b c d hband).wave j u k) xi = 0) ∧
    (∀ j u k xi, (hi+delta)*(2:ℝ)^j.val < |xi| →
      𝓕 ((P.sincMasked n a b c d hband).wave j u k) xi = 0) := by
  have hlocal (j : Fin N) (u : ι j) (k : κ) :=
    sincProductMask_fourier_annulus (P.wave j u k).integrable n
      (a j u k) (b j u k) (c j u k) (d j u k)
      (lo*(2:ℝ)^j.val) (hi*(2:ℝ)^j.val)
      (fun xi hxi => by simpa only [SchwartzMap.fourier_coe] using hlow j u k xi hxi)
      (fun xi hxi => by simpa only [SchwartzMap.fourier_coe] using hhigh j u k xi hxi)
  constructor
  · intro j u k xi hxi
    have hs := (hlocal j u k).1 xi (by nlinarith [hdelta j u k])
    rw [SchwartzMap.fourier_coe]
    have heq : ((P.sincMasked n a b c d hband).wave j u k : ℝ → ℂ) =
        fun x => (sincProductMask n (a j u k*x+b j u k) (c j u k*x+d j u k):ℂ)*P.wave j u k x := by
      funext x
      exact P.sincMasked_wave n a b c d hband j u k x
    rw [heq]
    exact hs
  · intro j u k xi hxi
    have hs := (hlocal j u k).2 xi (by nlinarith [hdelta j u k])
    rw [SchwartzMap.fourier_coe]
    have heq : ((P.sincMasked n a b c d hband).wave j u k : ℝ → ℂ) =
        fun x => (sincProductMask n (a j u k*x+b j u k) (c j u k*x+d j u k):ℂ)*P.wave j u k x := by
      funext x
      exact P.sincMasked_wave n a b c d hband j u k x
    rw [heq]
    exact hs

end LipschitzHilbert.LinePacketFamily

end

end OAI
