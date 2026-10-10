import OAI.Probability.InvariantIsing.Cavity.CavitySelectedDimensions
import OAI.Probability.InvariantIsing.Spectral.FiniteSpectralMeasure

namespace OAI

/-! The finite-alphabet pressure theorem along diverging dimensions. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem selected_finite_alphabet_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput) {m : ℕ}
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (lam : Fin m → ℝ)
    (D : ℕ → ℕ) (hD : ∀ k, 0 < D k) (hDlim : Tendsto D atTop atTop)
    (g : (k : ℕ) → Fin (D k) → Fin m)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a=1)
    (hρlim : Tendsto (fun k a => ((cavitySpectralGroup (g k) a).card : ℝ)/D k) atTop (𝓝 ρ)) :
    Tendsto (fun k => ∫ V, rotatedPressure (fun i => lam (g k i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k)) atTop
      (𝓝 (variationalFunctional (finiteR ρ lam hρ hρsum)).toReal) := by
  by_cases hm : 2 ≤ m
  · exact cavity_selected_dimensions_pressure_tendsto hhaar hgauss hpub hm μ lam D hD hDlim g ρ hρ hρsum hρlim
  have hm0 : 0 < m := by
    obtain ⟨a,_⟩ := exists_pos_spectral_weight (fun a => (hρ a).le) hρsum
    exact Nat.pos_of_ne_zero (by intro hz; subst m; exact Fin.elim0 a)
  have hm1 : m=1 := by omega
  subst m
  have hlam : lam=fun _ => lam 0 := funext fun a => congrArg lam (Subsingleton.elim a 0)
  have hR : finiteR ρ lam hρ hρsum=fun _ => lam 0 := by
    funext x
    rw [hlam]
    exact finiteR_constant ρ hρ hρsum x (lam 0)
  rw [hR, variationalFunctional_constant, EReal.toReal_coe]
  have he : ∀ᶠ k in atTop, (∫ V, rotatedPressure (fun i => lam (g k i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ (D k))=lam 0/2 := by
    apply Filter.Eventually.of_forall
    intro k
    have hpos : 0 < D k := hD k
    have heig : (fun i => lam (g k i))=fun _ => lam 0 :=
      funext fun i => congrArg lam (Subsingleton.elim (g k i) 0)
    rw [heig]
    simp only [rotatedPressure_constant hpos,integral_const,measureReal_def,measure_univ,
      ENNReal.toReal_one,one_smul]
  exact tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)

end InvariantIsing

end

end OAI
