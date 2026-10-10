import OAI.Probability.InvariantIsing.Cavity.CavityRotationArray
import OAI.Probability.InvariantIsing.Arrays.TensorLimitingGG

namespace OAI

/-! Finite-volume perturbation minimizers provide exactly the natural-index
amplitudes used in the physical cavity model. The unused coordinates are one. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityBaseAmplitude {N : ℕ} (u : Fin N → ℝ) (j : ℕ) : ℝ :=
  if hj : j < N then u ⟨j,hj⟩ else 1

lemma cavityBaseAmplitude_fin {N : ℕ} (u : Fin N → ℝ) (j : Fin N) :
    cavityBaseAmplitude u j = u j := by
  simp only [cavityBaseAmplitude, dite_eq_left j.isLt]

lemma cavityBaseAmplitude_bound {N : ℕ} (u : Fin N → ℝ)
    (hu : ∀ j, u j ∈ Set.Icc (1 : ℝ) 2) (j : ℕ) :
    |cavityBaseAmplitude u j| ≤ 2 := by
  unfold cavityBaseAmplitude
  split_ifs with hj
  · exact abs_le.mpr ⟨by linarith [(hu ⟨j,hj⟩).1], (hu ⟨j,hj⟩).2⟩
  · norm_num

lemma cavityBaseAmplitude_restrict {N : ℕ} (u : Fin N → ℝ) :
    (fun j : Fin N => cavityBaseAmplitude u j) = u :=
  funext (cavityBaseAmplitude_fin u)

end InvariantIsing

end

end OAI
