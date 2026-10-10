import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.SelectedBarrierTransferBarrier

namespace OAI

open MeasureTheory Filter Set Metric
open scoped Topology
noncomputable section
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma scaled_priced_field {s : ℝ} (hs : 0 < s) (Z : ℝ) (μ : TFSpace → ℝ) (x : TFSpace) :
    s^4*(Z/‖s • x‖-1/s^4-tfPotential μ (s • x)) =
      nuclearField (s^3*Z) x-tfPotential (tfDilation s μ) x-1 := by
  have hh := scaled_screened_field_eq hs Z μ x
  unfold nuclearField at hh ⊢
  have hone : s^4*(1/s^4) = 1 := mul_one_div_cancel (pow_ne_zero _ hs.ne')
  nlinarith only [hh,hone]

lemma rpow_max_scale {s H : ℝ} (hs : 0 ≤ s) :
    s^6*(max H 0)^(3/2:ℝ) = (max (s^4*H) 0)^(3/2:ℝ) := by
  rw [←scaled_positive_reaction hs (le_max_right H 0)]
  congr 1
  rcases le_total H 0 with hH | hH
  · rw [max_eq_right hH,max_eq_right (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hs 4) hH),mul_zero]
  · rw [max_eq_left hH,max_eq_left (mul_nonneg (pow_nonneg hs 4) hH)]

lemma original_TF_scale {s Z k ε C : ℝ} {μ : TFSpace → ℝ} {x : TFSpace}
    (hs : 0 < s) (hx : x ≠ 0)
    (hcap : ‖s • x‖^4*(Z/‖s • x‖-1/s^4-tfPotential μ (s • x)) ≤ C)
    (hTF : |μ (s • x)-k*(max (Z/‖s • x‖-1/s^4-tfPotential μ (s • x)) 0)^(3/2:ℝ)| ≤ ε/‖s • x‖^6) :
    nuclearField (s^3*Z) x-tfPotential (tfDilation s μ) x ≤ 1+C/‖x‖^4 ∧
    |tfDilation s μ x-k*(max (nuclearField (s^3*Z) x-tfPotential (tfDilation s μ) x-1) 0)^(3/2:ℝ)| ≤ ε/‖x‖^6 := by
  have hnorm : ‖s • x‖ = s*‖x‖ := by rw [norm_smul,Real.norm_of_nonneg hs.le]
  have hsf := scaled_priced_field hs Z μ x
  let H := Z/‖s • x‖-1/s^4-tfPotential μ (s • x)
  constructor
  · have hh : ‖x‖^4*(s^4*H) ≤ C := by simpa only [hnorm,mul_pow,mul_assoc,mul_left_comm,mul_comm,H] using hcap
    have hdiv : s^4*H ≤ C/‖x‖^4 := (le_div_iff₀ (pow_pos (norm_pos_iff.mpr hx) 4)).mpr (by nlinarith only [hh])
    dsimp only [H] at hdiv
    rw [hsf] at hdiv
    linarith
  · have hh := mul_le_mul_of_nonneg_left hTF (pow_nonneg hs.le 6)
    have hrhs : s^6*(ε/‖s • x‖^6) = ε/‖x‖^6 := by rw [hnorm,mul_pow]; field_simp
    rw [hrhs,←abs_of_nonneg (pow_nonneg hs.le 6),←abs_mul] at hh
    change |s^6*(μ (s • x)-k*(max H 0)^(3/2:ℝ))| ≤ _ at hh
    rw [mul_sub,show s^6*(k*(max H 0)^(3/2:ℝ)) = k*(s^6*(max H 0)^(3/2:ℝ)) by ring,
      rpow_max_scale hs.le] at hh
    dsimp only [H] at hh
    rw [hsf] at hh
    exact hh

end CoulombBarrier

end

end OAI
