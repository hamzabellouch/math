import OAI.NumberTheory.Ostmann.HybridSieve.FourierPacket

namespace OAI

open MeasureTheory FourierTransform
open scoped FourierTransform Real
namespace Ostmann.HybridSieve

lemma continuous_fourierPhase (x : ℝ) : Continuous (fourierPhase x) := by
  change Continuous (fun t : ℝ => (Real.fourierChar (-(x*t)) : ℂ))
  simp only [Real.fourierChar_apply]
  fun_prop

lemma packet_integral_bound {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (freq : ι → ℝ) (f : SchwartzMap ℝ ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hf : ∀ t : ℝ, |t| ≤ 1 → c ≤ ‖𝓕 f t‖) :
    c^2 * (∫ t in Set.Icc (-1:ℝ) 1, ‖∑ j ∈ s, a j * fourierPhase (freq j) t‖^2) ≤
      ∫ x : ℝ, ‖∑ j ∈ s, a j * f (x-freq j)‖^2 := by
  let F := fourierPacket s a freq f
  have hi : Integrable (fun t : ℝ => ‖𝓕 F t‖^2) :=
    (SchwartzMap.memLp (𝓕 F) 2).integrable_norm_pow (by norm_num)
  have hs : IntegrableOn (fun t : ℝ =>
      ‖∑ j ∈ s, a j * fourierPhase (freq j) t‖^2) (Set.Icc (-1) 1) := by
    apply ContinuousOn.integrableOn_Icc
    apply Continuous.continuousOn
    apply Continuous.pow
    apply Continuous.norm
    exact continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_fourierPhase _))
  calc
    _ = ∫ t in Set.Icc (-1:ℝ) 1,
        c^2 * ‖∑ j ∈ s, a j * fourierPhase (freq j) t‖^2 := by
      rw [integral_const_mul]
    _ ≤ ∫ t in Set.Icc (-1:ℝ) 1, ‖𝓕 F t‖^2 := by
      apply setIntegral_mono_on (hs.const_mul _) hi.integrableOn measurableSet_Icc
      intro t ht
      rw [show 𝓕 F t = (∑ j ∈ s, a j * fourierPhase (freq j) t)*𝓕 f t from
        fourier_fourierPacket s a freq f t, norm_mul, mul_pow]
      have ht' : |t| ≤ 1 := abs_le.mpr ht
      nlinarith [sq_le_sq₀ hc (norm_nonneg (𝓕 f t)) |>.mpr (hf t ht'),
        sq_nonneg ‖∑ j ∈ s, a j * fourierPhase (freq j) t‖]
    _ ≤ ∫ t : ℝ, ‖𝓕 F t‖^2 :=
      integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall
        (fun _ => sq_nonneg _)) hi
    _ = _ := by
      simpa only [F, fourierPacket_apply] using SchwartzMap.integral_norm_sq_fourier F

end Ostmann.HybridSieve

end OAI
