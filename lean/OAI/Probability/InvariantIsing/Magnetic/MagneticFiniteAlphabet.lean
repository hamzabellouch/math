import OAI.Probability.InvariantIsing.Magnetic.MagneticFinitePopulationLimit
import OAI.Probability.InvariantIsing.Spectral.FiniteSpectralMeasure

namespace OAI

/-! The finite-alphabet external-field formula also includes a one-point
spectral law, represented by two equal eigenvalue labels. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem finite_alphabet_field_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m : ℕ} (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (e : (M : ℕ) → Fin M → Fin m)
    (he : Tendsto (fun M a => (spinGroupSize (e M) a : ℝ)/M) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (g : (M : ℕ) → Fin M → A) (γ b : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ)) :
    Tendsto (fun M => ∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
      (fun i => b (g M i)) ∂μ M) atTop
      (𝓝 (finiteMagneticFunctional (finiteR ρ lam hρ hsum) γ b).toReal) := by
  by_cases hm : 2 ≤ m
  · exact finite_positive_field_pressure_tendsto hhaar hgauss hpub hm ρ lam hρ hsum μ e he
      g γ b hγ hγsum hg
  have hm0 : 0 < m := by
    by_contra hn
    have hz : m=0 := by omega
    subst m
    simp at hsum
  have hm1 : m=1 := by omega
  subst m
  have hlam : lam=fun _ => lam 0 := funext fun a => congrArg lam (Subsingleton.elim a 0)
  have hR : finiteR ρ lam hρ hsum=fun _ => lam 0 := by
    funext x
    rw [hlam]
    exact finiteR_constant ρ hρ hsum x (lam 0)
  let ρ' : Fin 2 → ℝ := fun _ => 1/2
  have hρ' a : 0 < ρ' a := by norm_num [ρ']
  have hsum' : ∑ a, ρ' a=1 := by norm_num [ρ',Fin.sum_univ_two]
  let s : Fin 2 → ℕ := fun _ => 1
  have hs : ∑ a, s a=2 := by norm_num [s,Fin.sum_univ_two]
  let e' := fun M => cavityResidueLabel (by omega : 0 < 2) s hs M
  have he' : Tendsto (fun M a => (spinGroupSize (e' M) a : ℝ)/M) atTop (𝓝 ρ') := by
    simpa only [s,ρ',Nat.cast_one,Nat.cast_ofNat,e',spinGroupSize,cavitySpectralGroup] using
      cavity_canonical_mass_tendsto (by omega : 0 < 2) (by omega : 0 < 2) s hs
  have hR' : finiteR ρ' (fun _ => lam 0) hρ' hsum'=fun _ => lam 0 := by
    funext x
    exact finiteR_constant ρ' hρ' hsum' x (lam 0)
  have hh := finite_positive_field_pressure_tendsto hhaar hgauss hpub (by omega : 2 ≤ 2)
    ρ' (fun _ => lam 0) hρ' hsum' μ e' he' g γ b hγ hγsum hg
  rw [hR'] at hh
  rw [hR]
  have heig M : (fun i => lam (e M i))=(fun _ : Fin M => lam 0) :=
    funext fun i => congrArg lam (Subsingleton.elim (e M i) 0)
  apply hh.congr
  intro M
  rw [heig M]

end InvariantIsing

end

end OAI
