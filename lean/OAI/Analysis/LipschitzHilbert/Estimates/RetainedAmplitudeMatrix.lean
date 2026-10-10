import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeMatrixBound

namespace OAI

/-! The retained pair sum loses only one logarithmic factor, as in the
source amplitude reduction. This concerns the actual measurable levels. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

def retainedAmplitudeCost (C0 L : ℝ) : ℝ :=
  4*Real.sqrt 2*Real.sqrt (2*(L/Real.log 2)+5)*Real.sqrt (4*C0)

theorem retained_amplitude_matrix_bound {X κ : Type*} [MeasurableSpace X] [Fintype κ]
    (mu : Measure X) (f g : X → EuclideanSpace ℂ κ)
    (hfm : Measurable f) (hgm : Measurable g) (hf2 : MemLp f 2 mu) (hg2 : MemLp g 2 mu)
    (I J : Finset ℤ) (F E Cf Cg C L : ℝ)
    (hF : 0<F) (hE : 0<E) (hC : 0≤C) (hL : 0≤L)
    (henergyF : (∫ x, ‖f x‖^2 ∂mu)≤Cf*F) (henergyG : (∫ x, ‖g x‖^2 ∂mu)≤Cg*E)
    (hposF : ∀ i∈I, 0<mu.real (amplitudeLevel f i))
    (hposG : ∀ j∈J, 0<mu.real (amplitudeLevel g j))
    (hlogF : ∀ i∈I, |Real.log (mu.real (amplitudeLevel f i)/F)|≤L)
    (hlogG : ∀ j∈J, |Real.log (mu.real (amplitudeLevel g j)/E)|≤L)
    (pairing : ℤ → ℤ → ℂ)
    (hpair : ∀ i∈I, ∀ j∈J, ‖pairing i j‖≤
      C*Real.sqrt (mu.real (amplitudeLevel f i))*Real.sqrt (mu.real (amplitudeLevel g j))) :
    ‖∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • pairing i j‖≤
      C*retainedAmplitudeCost Cf L*retainedAmplitudeCost Cg L*Real.sqrt F*Real.sqrt E := by
  have hsumF := amplitudeLevel_retained_sum mu f hf2 hfm.norm I F Cf L hF hL henergyF hposF hlogF
  have hsumG := amplitudeLevel_retained_sum mu g hg2 hgm.norm J E Cg L hE hL henergyG hposG hlogG
  have h := finite_amplitude_matrix_bound I J
    (fun i => mu.real (amplitudeLevel f i)) (fun j => mu.real (amplitudeLevel g j)) pairing C hpair
  rw [amplitude_weight_sum_unnormalize I _ F hF (fun _ _ => measureReal_nonneg),
    amplitude_weight_sum_unnormalize J _ E hE (fun _ _ => measureReal_nonneg)] at h
  apply h.trans
  calc
    _≤C*(retainedAmplitudeCost Cf L*Real.sqrt F)*(retainedAmplitudeCost Cg L*Real.sqrt E) := by
      have hsG : 0≤∑ j∈J, (2:ℝ)^j*Real.sqrt (mu.real (amplitudeLevel g j)/E) := by positivity
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsumF (Real.sqrt_nonneg _)) hC
      · exact mul_le_mul_of_nonneg_right hsumG (Real.sqrt_nonneg _)
      · positivity
      · exact mul_nonneg hC (by unfold retainedAmplitudeCost; positivity)
    _=_ := by ring

end LipschitzHilbert

end

end OAI
