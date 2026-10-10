import OAI.Probability.InvariantIsing.Spectral.SelectedAlphabetPressure
import OAI.Probability.InvariantIsing.Core.FiniteTypePressure

namespace OAI

/-! Finite spectral cell types along diverging dimensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Classical BigOperators
namespace InvariantIsing

theorem selected_finite_type_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput) {ι : Type*} [Fintype ι]
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (lam : ι → ℝ)
    (D : ℕ → ℕ) (hD : ∀ k, 0 < D k) (hDlim : Tendsto D atTop atTop)
    (g : (k : ℕ) → Fin (D k) → ι)
    (w : ι → ℝ) (hw : ∀ a, 0 < w a) (hsum : ∑ a, w a=1)
    (hlim : Tendsto (fun k a => (spectralLabelCount (g k) a : ℝ)/D k) atTop (𝓝 w))
    (aMax : ι) (hMax : ∀ a, lam a ≤ lam aMax) :
    Tendsto (fun k => ∫ V, rotatedPressure (fun i => lam (g k i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)) atTop
      (𝓝 (variationalFunctional (measureR (finiteSpectralMeasure w lam) (lam aMax))).toReal) := by
  let e := Fintype.equivFin ι
  let wf := w ∘ e.symm
  let lf := lam ∘ e.symm
  have hwp : ∀ a, 0 < wf a := fun a => hw (e.symm a)
  have hws : ∑ a, wf a=1 := (e.symm.sum_comp w).trans hsum
  have hl : Tendsto (fun N a =>
      ((cavitySpectralGroup (fun i => e (g N i)) a).card : ℝ)/D N) atTop (𝓝 wf) := by
    apply tendsto_pi_nhds.mpr
    intro a
    change Tendsto (fun N => ((cavitySpectralGroup (fun i => e (g N i)) a).card : ℝ)/D N)
      atTop (𝓝 (w (e.symm a)))
    convert (tendsto_pi_nhds.mp hlim) (e.symm a) using 1
    funext N
    congr 2
    apply congrArg Finset.card
    ext i
    simp only [cavitySpectralGroup,Finset.mem_filter,Finset.mem_univ,
      true_and,← e.eq_symm_apply]
  have hh := selected_finite_alphabet_pressure_tendsto hhaar hgauss hpub μ lf D hD hDlim
    (fun N i => e (g N i)) wf hwp hws hl
  have hR : measureR (finiteSpectralMeasure w lam) (lam aMax)=finiteR wf lf hwp hws := by
    funext x
    rw [← finiteSpectralMeasure_equiv e.symm w lam]
    have he := measureR_finiteSpectralMeasure wf lf hwp hws (e aMax)
      (fun a => by simpa only [lf,Function.comp_apply,e.symm_apply_apply] using hMax (e.symm a)) x
    simpa only [lf,Function.comp_apply,e.symm_apply_apply] using he
  rw [hR]
  convert hh using 1
  funext N
  simp only [lf,Function.comp_apply,e.symm_apply_apply]

end InvariantIsing

end

end OAI
