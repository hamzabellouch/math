import OAI.Analysis.LipschitzHilbert.Estimates.ComparableCommutatorSum

namespace OAI

/-! The nine nearby dyadic input frequencies form an actual Schwartz
family with uniform spectral and square-energy bounds. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

def nearbyInputPiece (h : SchwartzMap ℝ ℂ) (i j : ℤ) : SchwartzMap ℝ ℂ :=
  if i-4≤j ∧ j≤ i+4 then lineSchwartzProjection dyadicDifference (scale j) (scale_pos j).ne' h else 0

def nearbyInput (J : Finset ℤ) (h : SchwartzMap ℝ ℂ) (i : ℤ) : SchwartzMap ℝ ℂ :=
  ∑ j∈J, nearbyInputPiece h i j

theorem nearbyInputPiece_frequency (h : SchwartzMap ℝ ℂ) (i j : ℤ) (eta : ℝ)
    (heta : (𝓕 (nearbyInputPiece h i j) : SchwartzMap ℝ ℂ) eta≠0) : |eta|≤64/scale i := by
  classical
  by_cases hij : i-4≤j ∧ j≤ i+4
  · simp only [nearbyInputPiece,ite_eq_left hij] at heta
    have hh := (dyadicProjection_frequency (scale j) (scale_pos j) h eta heta).2
    have hr : scale i/scale j≤16 := by
      rw [scale,scale,←zpow_sub₀ (by norm_num : (2:ℝ)≠0)]
      have hz := zpow_le_zpow_right₀ (show (1:ℝ)≤2 by norm_num) (show i-j≤4 by omega)
      norm_num at hz
      exact hz
    have hm := mul_le_mul_of_nonneg_left hh (scale_pos i).le
    have he : scale i*((13/6)/scale j)=(13/6)*(scale i/scale j) := by ring
    rw [he] at hm
    apply (le_div_iff₀ (scale_pos i)).mpr
    nlinarith
  · simp only [nearbyInputPiece,ite_eq_right hij,FourierTransform.fourier_zero,zero_apply,ne_eq,not_true_eq_false] at heta

theorem nearbyInput_frequency (J : Finset ℤ) (h : SchwartzMap ℝ ℂ) (i : ℤ) (eta : ℝ)
    (heta : (𝓕 (nearbyInput J h i) : SchwartzMap ℝ ℂ) eta≠0) : |eta|≤64/scale i := by
  by_contra hn
  apply heta
  simp only [nearbyInput,FourierTransform.fourier_sum,sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_contra hj
  exact hn (nearbyInputPiece_frequency h i j eta hj)

theorem nearbyInput_energy (I J : Finset ℤ) (h : SchwartzMap ℝ ℂ) :
    (∑ i∈I, ∫ x, ‖nearbyInput J h i x‖^2)≤49152*(∫ x, ‖h x‖^2) := by
  classical
  let H := fun j => lineSchwartzProjection dyadicDifference (scale j) (scale_pos j).ne' h
  have hp (i j : ℤ) : (∫ x, ‖nearbyInputPiece h i j x‖^2)≤
      (lineScaleWeight i j)^2*(256*(∫ x, ‖H j x‖^2)) := by
    by_cases hij : i-4≤j ∧ j≤ i+4
    · have hn : (j-i).natAbs≤4 := by omega
      have hw : (1/16:ℝ)≤lineScaleWeight i j := by
        have hh := pow_le_pow_of_le_one (show (0:ℝ)≤1/2 by norm_num)
          (show (1/2:ℝ)≤1 by norm_num) hn
        norm_num only [show (1/2:ℝ)^4=1/16 by norm_num] at hh
        exact hh
      have hsq := pow_le_pow_left₀ (show (0:ℝ)≤1/16 by norm_num) hw 2
      have hcoef : 1≤(lineScaleWeight i j)^2*256 := by norm_num at hsq; linarith
      simp only [nearbyInputPiece,ite_eq_left hij]
      calc
        _ = 1*(∫ x, ‖H j x‖^2) := by rw [one_mul]
        _ ≤ ((lineScaleWeight i j)^2*256)*(∫ x, ‖H j x‖^2) :=
          mul_le_mul_of_nonneg_right hcoef (integral_nonneg fun _ => sq_nonneg _)
        _ = _ := by ring
    · simp only [nearbyInputPiece,ite_eq_right hij,zero_apply,norm_zero,zero_pow (by decide : 2≠0),integral_zero]
      positivity
  have hs := line_geometric_energy_schur I J (fun i j x => nearbyInputPiece h i j x)
    (fun i _ j _ => (nearbyInputPiece h i j).memLp 2 volume)
    (fun j => 256*(∫ x, ‖H j x‖^2)) (fun j _ => by positivity) (fun i _ j _ => hp i j)
  have hf := lineSchwartzProjection_frame J (fun _ => dyadicDifference) scale (fun j => (scale_pos j).ne')
    12 (fun eta => dyadicDifference_square_sum J eta) h
  change (∑ j∈J, ∫ x, ‖H j x‖^2)≤_ at hf
  have he : (∑ i∈I, ∫ x, ‖nearbyInput J h i x‖^2)≤16*256*(∑ j∈J, ∫ x, ‖H j x‖^2) := by
    simpa only [nearbyInput,sum_apply,←Finset.mul_sum,mul_assoc] using hs
  exact he.trans (by nlinarith [hf])

end LipschitzHilbert.PacketRepresentation

end

end OAI
