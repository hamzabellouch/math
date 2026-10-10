import OAI.Probability.InvariantIsing.Magnetic.MagneticFiniteAlphabet
import OAI.Probability.InvariantIsing.Core.FiniteTypePressure

namespace OAI

/-! The external-field formula with a general finite type of spectral labels. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Classical BigOperators
namespace InvariantIsing

theorem finite_type_field_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput) {ι : Type*} [Fintype ι]
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (lam : ι → ℝ)
    (g : (N : ℕ) → Fin N → ι)
    (w : ι → ℝ) (hw : ∀ a, 0 < w a) (hsum : ∑ a, w a=1)
    (hlim : Tendsto (fun N a => (spectralLabelCount (g N) a : ℝ)/N) atTop (𝓝 w))
    (aMax : ι) (hMax : ∀ a, lam a ≤ lam aMax)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : (N : ℕ) → Fin N → A) (γ b : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hgroup : Tendsto (fun N a => (spinGroupSize (group N) a : ℝ)/N) atTop (𝓝 γ)) :
    Tendsto (fun N => ∫ V, rotatedPressure (fun i => lam (g N i))
      (matrixRotation V⁻¹) (fun i => b (group N i)) ∂μ N) atTop
      (𝓝 (finiteMagneticFunctional (measureR (finiteSpectralMeasure w lam) (lam aMax)) γ b).toReal) := by
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
  have hh := finite_alphabet_field_pressure_tendsto hhaar hgauss hpub wf lf hwp hws μ
    (fun N i => e (g N i)) hl group γ b hγ hγsum hgroup
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
