import OAI.Analysis.Mahler.MassTarget
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace OAI

namespace Mahler
open Set MeasureTheory Filter
open scoped Topology ENNReal
variable {n N : ℕ}

noncomputable def massBelow (U : Set (ComplexEuclidean n))
    (f : Fin N → ComplexEuclidean n → ℂ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in U ∩ {z | tau f z < R}, ENNReal.ofReal (massDensity f z)

lemma massBelow_mono (U : Set (ComplexEuclidean n))
    (f : Fin N → ComplexEuclidean n → ℂ) : Monotone (massBelow U f) := by
  intro R S hRS
  apply lintegral_mono_set
  intro z hz
  exact ⟨hz.1,hz.2.trans_le hRS⟩

lemma massBelow_one (U : Set (ComplexEuclidean n))
    (f : Fin N → ComplexEuclidean n → ℂ) : massBelow U f 1 = massIntegral U f := rfl

/-- Lower bounds on a sublevel sequence tending to one
imply the mass bound, even if the final integral is infinite.
The sublevel bounds are explicit hypotheses. -/
theorem massIntegral_lower_of_sublevels (U : Set (ComplexEuclidean n))
    (f : Fin N → ComplexEuclidean n → ℂ) (m : ℕ) {R : ℕ → ℝ}
    (hR : Tendsto R atTop (𝓝 1)) (hR1 : ∀ k, R k ≤ 1)
    (hbound : ∀ k, ENNReal.ofReal ((R k)^n * (Real.pi * (m : ℝ))^n) ≤ massBelow U f (R k)) :
    ENNReal.ofReal ((Real.pi * (m : ℝ))^n) ≤ massIntegral U f := by
  have hlim : Tendsto (fun k => ENNReal.ofReal ((R k)^n * (Real.pi * (m : ℝ))^n))
      atTop (𝓝 (ENNReal.ofReal ((Real.pi * (m : ℝ))^n))) := by
    simpa only [one_pow,one_mul] using ENNReal.tendsto_ofReal
      ((hR.pow n).mul_const ((Real.pi * (m : ℝ))^n))
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro k
  exact (hbound k).trans ((massBelow_mono U f (hR1 k)).trans_eq (massBelow_one U f))

end Mahler

end OAI
