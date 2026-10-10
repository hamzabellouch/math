import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Bump

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

namespace OrdinaryGaussianWindow
open OrdinaryDirichletMeanSquare MeasureTheory

def scaledWindow {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (u : ι → ℝ) (ε x : ℝ) : ℂ :=
  ∑ n ∈ s, a n * (bump ((x-u n)/ε) : ℂ)

lemma scaledWindow_eq {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (u : ι → ℝ) (ε x : ℝ) :
    scaledWindow s a u ε x = window s a (fun n => u n / ε) (x / ε) := by
  simp only [scaledWindow, window, sub_div]

theorem scaled_window_spectral_identity {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (u : ι → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ, ‖scaledWindow s a u ε x‖^2) =
      ε^2/4 * ∫ t : ℝ, gaussian (ε*t/2) * ‖polynomial s a u t‖^2 := by
  simp_rw [scaledWindow_eq]
  have h1 := Measure.integral_comp_mul_right
    (fun x : ℝ => ‖window s a (fun n => u n/ε) x‖^2) ε⁻¹
  simp only [← div_eq_mul_inv, abs_of_pos hε, inv_inv] at h1
  rw [h1, gaussian_window_spectral_identity]
  have h2 := Measure.integral_comp_mul_right
    (fun t : ℝ => gaussian (ε*t/2) * ‖polynomial s a u t‖^2) (2/ε)
  have hp (t : ℝ) : polynomial s a (fun n => 2*(u n/ε)) t =
      polynomial s a u (t*(2/ε)) := by
    unfold polynomial phase
    congr 1
    funext n
    congr 2
    congr 1
    push_cast
    ring
  have he (t : ℝ) : ε*(t*(2/ε))/2 = t := by field_simp
  simp_rw [he] at h2
  simp_rw [hp]
  rw [h2]
  rw [abs_inv, abs_of_pos (div_pos (by norm_num : (0:ℝ)<2) hε)]
  simp only [smul_eq_mul]
  field_simp
  ring

end OrdinaryGaussianWindow

end

end OAI
