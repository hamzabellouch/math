import OAI.Dynamics.EntropyCounterexample.Saturation
import OAI.Dynamics.EntropyCounterexample.RadialRegisterEntropy

namespace OAI

noncomputable section

namespace Problem340
namespace SaturationEntropy

open Set Dynamics

lemma saturation_radial (A : ℝ) (hA : 1 ≤ A) {r : ℝ}
    (hr : 0 ≤ r) {u : ℂ} (hu : ‖u‖ = 1) :
    saturation A hA (r • u) = saturationProfile A hA r • u := by
  by_cases hr0 : r = 0
  · subst r
    simp only [zero_smul, saturation_zero]
    rw [saturationProfile_eq_self A hA (by norm_num), zero_smul]
  · have hnorm : ‖r • u‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hu, mul_one]
    rw [saturation, hnorm, smul_smul, div_mul_cancel₀ _ hr0]

def radiusMap (L : ℝ) (hL : 1 ≤ L) :
    Set.Icc (0 : ℝ) (3 * L) → Set.Icc (0 : ℝ) (3 * L) :=
  fun r => ⟨L * saturationProfile (3 * L) (by linarith) r,
    mul_nonneg (by linarith) (saturationProfile_nonneg _ _ r.property.1), by
      have hp := saturationProfile_le_two (3 * L) (by linarith) r.property.1
      nlinarith⟩

lemma radiusMap_monotone (L : ℝ) (hL : 1 ≤ L) :
    Monotone (radiusMap L hL) := by
  intro r s hrs
  exact mul_le_mul_of_nonneg_left
    (saturationProfile_monotoneOn (3 * L) (by linarith) r.property s.property hrs)
    (by linarith)

theorem coverEntropy_scaled_saturation {X : Type*} [UniformSpace X]
    [CompactSpace X] [Nonempty X]
    (L : ℝ) (hL : 1 ≤ L) (embed : ℂ → X) (hembed : Continuous embed)
    (S : X → ℂ)
    (hSaffine : ∀ z, S (embed z) = saturation (3 * L) (by linarith) z)
    (hSbound : ∀ x, ‖S x‖ ≤ 2) (q : ℕ) :
    coverEntropy (RadialRegisterEntropy.coordinatewise
      (fun x => embed (L • S x)) q) Set.univ = 0 := by
  apply RadialRegisterEntropy.coverEntropy_coordinatewise_eq_zero
    (3 * L) (by linarith) embed hembed (fun x => embed (L • S x))
    (radiusMap L hL) (radiusMap_monotone L hL)
  · intro r u
    rw [hSaffine, saturation_radial _ _ r.property.1]
    · congr 1
      exact smul_smul L (saturationProfile (3 * L) _ r) (u : ℂ)
    · simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  · intro x
    refine ⟨L • S x, ?_, rfl⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ L)]
    have hnorm := hSbound x
    nlinarith

section OnePoint

local instance : UniformSpace (OnePoint ℂ) := uniformSpaceOfCompactR1

theorem coverEntropy_onePoint_saturation (L : ℝ) (hL : 1 ≤ L) (q : ℕ) :
    coverEntropy (RadialRegisterEntropy.coordinatewise
      (fun x : OnePoint ℂ => ((L • sphereSaturation (3 * L) (by linarith) x : ℂ) :
        OnePoint ℂ)) q) Set.univ = 0 := by
  apply coverEntropy_scaled_saturation L hL ((↑) : ℂ → OnePoint ℂ)
    OnePoint.continuous_coe (sphereSaturation (3 * L) (by linarith))
  · intro z
    rfl
  · exact norm_sphereSaturation_le_two (3 * L) (by linarith)

end OnePoint

end SaturationEntropy
end Problem340

end

end OAI
