import OAI.Analysis.LipschitzHilbert.Fourier.LineHighLowSpectrum
import OAI.Analysis.LipschitzHilbert.Fourier.LineGeometricSchur
import OAI.Analysis.LipschitzHilbert.Fourier.LineAnnularSum

namespace OAI

/-! The complete finite high/low sum: geometric Schur summation inside
each high-frequency output annulus, then finite Fourier overlap. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

def highLowPiece (m b h : SchwartzMap ℝ ℂ) (i j : ℤ) : SchwartzMap ℝ ℂ :=
  if i+5≤j then
    lineSchwartzCommutator m (lineSchwartzProjection dyadicDifference (scale i) (scale_pos i).ne' b)
      (schwartzDerivative 1 (lineSchwartzProjection dyadicDifference (scale j) (scale_pos j).ne' h))
  else 0

def highLowRow (J : Finset ℤ) (m b h : SchwartzMap ℝ ℂ) (i : ℤ) : SchwartzMap ℝ ℂ :=
  ∑ j∈J, highLowPiece m b h i j

theorem dyadic_scale_five_gap (i j : ℤ) (hij : i+5≤j) : 32*scale i≤scale j := by
  have hh : (2:ℝ)^(i+5)≤(2:ℝ)^j := zpow_le_zpow_right₀ (by norm_num) hij
  simpa only [zpow_add₀ (by norm_num : (2:ℝ)≠0),show (2:ℝ)^(5:ℤ)=32 by norm_num,
    scale,mul_comm] using hh

theorem highLowPiece_frequency (m b h : SchwartzMap ℝ ℂ) (i j : ℤ) :
    ∀ eta, (𝓕 (highLowPiece m b h i j) : SchwartzMap ℝ ℂ) eta≠0 →
      (11/12)/scale i≤|eta| ∧ |eta|≤(9/4)/scale i := by
  classical
  intro eta heta
  by_cases hij : i+5≤j
  · simp only [highLowPiece,ite_eq_left hij] at heta
    exact highLowCommutator_frequency m b h (scale i) (scale j) (scale_pos i) (scale_pos j)
      (dyadic_scale_five_gap i j hij) eta heta
  · simp only [highLowPiece,ite_eq_right hij,FourierTransform.fourier_zero,zero_apply,ne_eq,not_true_eq_false] at heta

theorem highLowRow_frequency (J : Finset ℤ) (m b h : SchwartzMap ℝ ℂ) (i : ℤ) :
    ∀ eta, (𝓕 (highLowRow J m b h i) : SchwartzMap ℝ ℂ) eta≠0 →
      (11/12)/scale i≤|eta| ∧ |eta|≤(9/4)/scale i := by
  intro eta heta
  by_contra hn
  apply heta
  simp only [highLowRow,FourierTransform.fourier_sum,sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_contra hj
  exact hn (highLowPiece_frequency m b h i j eta hj)

theorem highLowSum_energy (I J : Finset ℤ) (m b h : SchwartzMap ℝ ℂ) (A L : ℝ)
    (hm : ∀ eta, ‖m eta‖≤A) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    (∫ x, ‖(∑ i∈I, highLowRow J m b h i) x‖^2)≤
      576*(A*L*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*
        (26*Real.pi/3))^2*(∫ x, ‖h x‖^2) := by
  classical
  let C := A*L*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*(26*Real.pi/3)
  let H := fun j => lineSchwartzProjection dyadicDifference (scale j) (scale_pos j).ne' h
  have hpiece (i j : ℤ) : (∫ x, ‖highLowPiece m b h i j x‖^2)≤
      (lineScaleWeight i j)^2*(C^2*(∫ x, ‖H j x‖^2)) := by
    by_cases hij : i+5≤j
    · have hc := highLowCommutator_energy m b h (scale i) (scale j) A L (scale_pos i) (scale_pos j) hm hLip
      simp only [highLowPiece,ite_eq_left hij]
      apply hc.trans_eq
      rw [lineScaleWeight_ratio i j (by omega)]
      dsimp [C,H]
      ring
    · simp only [highLowPiece,ite_eq_right hij,zero_apply,norm_zero,zero_pow (by decide : 2≠0),integral_zero]
      positivity
  have hschur := line_geometric_energy_schur I J
    (fun i j x => highLowPiece m b h i j x)
    (fun i _ j _ => (highLowPiece m b h i j).memLp 2 volume)
    (fun j => C^2*(∫ x, ‖H j x‖^2)) (fun j _ => by positivity)
    (fun i _ j _ => hpiece i j)
  have hrows : (∑ i∈I, ∫ x, ‖highLowRow J m b h i x‖^2)≤
      16*C^2*(∑ j∈J, ∫ x, ‖H j x‖^2) := by
    simpa only [highLowRow,sum_apply,←Finset.mul_sum,mul_assoc] using hschur
  have hframe : (∑ j∈J, ∫ x, ‖H j x‖^2)≤12*(∫ x, ‖h x‖^2) :=
    lineSchwartzProjection_frame J (fun _ => dyadicDifference) scale (fun j => (scale_pos j).ne')
      12 (fun eta => dyadicDifference_square_sum J eta) h
  have hoverlap := line_annular_sum_energy I (highLowRow J m b h) (by
    intro i _ eta heta
    have hf := highLowRow_frequency J m b h i eta heta
    have hlo := (div_le_iff₀ (scale_pos i)).mp hf.1
    have hhi := (le_div_iff₀ (scale_pos i)).mp hf.2
    exact ⟨by simpa only [scale,mul_comm] using hlo,by simpa only [scale,mul_comm] using hhi⟩)
  calc
    _ ≤ 3*(∑ i∈I, ∫ x, ‖highLowRow J m b h i x‖^2) := hoverlap
    _ ≤ 3*(16*C^2*(∑ j∈J, ∫ x, ‖H j x‖^2)) :=
      mul_le_mul_of_nonneg_left hrows (by norm_num)
    _ ≤ 3*(16*C^2*(12*(∫ x, ‖h x‖^2))) := by
      gcongr
    _ = _ := by dsimp [C]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
