import OAI.Probability.InvariantIsing.Core.FiniteAlphabetPressure
import OAI.Probability.InvariantIsing.Spectral.SpectralLabelCounts

namespace OAI

/-! The finite-alphabet pressure theorem for a finite type of spectral cells. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Classical BigOperators

namespace InvariantIsing

lemma finiteSpectralMeasure_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (w lam : ι → ℝ) :
    finiteSpectralMeasure (w ∘ e) (lam ∘ e)=finiteSpectralMeasure w lam := by
  unfold finiteSpectralMeasure
  exact Measure.sum_comp_equiv e (fun i => ENNReal.ofReal (w i) • Measure.dirac (lam i))

theorem finite_type_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput) {ι : Type*} [Fintype ι]
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (lam : ι → ℝ)
    (g : (N : ℕ) → Fin N → ι)
    (w : ι → ℝ) (hw : ∀ a, 0 < w a) (hsum : ∑ a, w a=1)
    (hlim : Tendsto (fun N a => (spectralLabelCount (g N) a : ℝ)/N) atTop (𝓝 w))
    (aMax : ι) (hMax : ∀ a, lam a ≤ lam aMax) :
    Tendsto (fun N => ∫ V, rotatedPressure (fun i => lam (g N i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ N) atTop
      (𝓝 (variationalFunctional (measureR (finiteSpectralMeasure w lam) (lam aMax))).toReal) := by
  let e := Fintype.equivFin ι
  let wf := w ∘ e.symm
  let lf := lam ∘ e.symm
  have hwp : ∀ a, 0 < wf a := fun a => hw (e.symm a)
  have hws : ∑ a, wf a=1 := (e.symm.sum_comp w).trans hsum
  have hl : Tendsto (fun N a =>
      ((cavitySpectralGroup (fun i => e (g N i)) a).card : ℝ)/N) atTop (𝓝 wf) := by
    apply tendsto_pi_nhds.mpr
    intro a
    change Tendsto (fun N => ((cavitySpectralGroup (fun i => e (g N i)) a).card : ℝ)/N)
      atTop (𝓝 (w (e.symm a)))
    convert (tendsto_pi_nhds.mp hlim) (e.symm a) using 1
    funext N
    congr 2
    apply congrArg Finset.card
    ext i
    simp only [cavitySpectralGroup,Finset.mem_filter,Finset.mem_univ,
      true_and,← e.eq_symm_apply]
  have hh := finite_alphabet_pressure_tendsto hhaar hgauss hpub μ lf
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
