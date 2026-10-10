import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.ScalarRieszTestLimit
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalDilationDerivative

namespace OAI

/-!
# Gradient identities for scalar Riesz tests

Summing directional Schwartz derivatives over an orthonormal basis recovers the
dilated fractional gradient kernel. Integrating this identity and passing to
vanishing capped truncations yields the fractional Schwartz integral with its
factor of negative one half.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set LineDeriv

abbrev scalarSchwartzDerivative {d : ℕ} (g : 𝓢(Ambient d, ℝ))
    (e : Ambient d) : 𝓢(Ambient d, ℝ) := ∂_{e} g

theorem sum_symmetricScalarRieszTestKernel_gradient {d : ℕ} {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ (Ambient d)) (m : ℕ)
    (g : 𝓢(Ambient d, ℝ)) (x h : Ambient d) :
    (∑ i, symmetricScalarRieszTestKernel m (b i) (scalarSchwartzDerivative g (b i)) x h) =
      dilatedFractionalGradientKernel m g x 1 h := by
  have hsum (A : Ambient d →L[ℝ] ℝ) :
      (∑ i, inner ℝ (b i) h * A (b i)) = A h := by
    simpa only [map_sum, map_smul, smul_eq_mul] using!
      congrArg (fun z => A z) (b.sum_repr' h)
  simp only [symmetricScalarRieszTestKernel, scalarSchwartzDerivative, lineDerivOp_apply_eq_fderiv,
    dilatedFractionalGradientKernel, one_smul, smul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib, hsum]

theorem sum_scalarRieszSchwartzTest_gradient (p : ℕ) {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ (Ambient (p + 1)))
    (g : 𝓢(Ambient (p + 1), ℝ)) (x : Ambient (p + 1)) :
    (∑ i, scalarRieszSchwartzTest (p + 1) (b i) (scalarSchwartzDerivative g (b i)) x) =
      (-1 / 2 : ℝ) * ∫ h, fractionalSchwartzKernel (p + 1) g x h := by
  have hI (i : ι) : Integrable
      (symmetricScalarRieszTestKernel (p + 1) (b i) (scalarSchwartzDerivative g (b i)) x) volume :=
    symmetricScalarRieszTestKernel_integrable p _ volume
      (volume_global_upper_growth (p + 1)) (b i) (scalarSchwartzDerivative g (b i)) x
  have hsum : (∫ h, ∑ i, symmetricScalarRieszTestKernel (p + 1) (b i) (scalarSchwartzDerivative g (b i)) x h) =
      ∑ i, ∫ h, symmetricScalarRieszTestKernel (p + 1) (b i) (scalarSchwartzDerivative g (b i)) x h :=
    integral_finsetSum Finset.univ (fun i _ => hI i)
  calc
    _ = (-1 / 2 : ℝ) *
        (∑ i, ∫ h, symmetricScalarRieszTestKernel (p + 1) (b i) (scalarSchwartzDerivative g (b i)) x h) := by
      simp only [scalarRieszSchwartzTest, Finset.mul_sum]
    _ = (-1 / 2 : ℝ) *
        (∫ h, ∑ i, symmetricScalarRieszTestKernel (p + 1) (b i) (scalarSchwartzDerivative g (b i)) x h) := by rw [hsum]
    _ = (-1 / 2 : ℝ) * ∫ h, dilatedFractionalGradientKernel (p + 1) g x 1 h := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall (sum_symmetricScalarRieszTestKernel_gradient b (p + 1) g x)
    _ = _ := by rw [(fractional_gradient_integral_identity p g x).2]

theorem sum_scalarCappedTransform_gradient_tendsto (p : ℕ) {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℝ (Ambient (p + 1)))
    (g : 𝓢(Ambient (p + 1), ℝ)) (x : Ambient (p + 1))
    (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => ∑ i, scalarCappedTransform (p + 1) volume (b i) (ε j) (scalarSchwartzDerivative g (b i)) x)
      atTop (𝓝 ((-1 / 2 : ℝ) * ∫ h, fractionalSchwartzKernel (p + 1) g x h)) := by
  have ht := tendsto_finsetSum Finset.univ (fun i _ =>
    scalarCappedTransform_tendsto_schwartz p (b i) (scalarSchwartzDerivative g (b i)) x ε hεpos hε)
  simpa only [sum_scalarRieszSchwartzTest_gradient p b g x] using! ht

end

end RieszRectifiability

end OAI
