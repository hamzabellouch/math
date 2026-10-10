import OAI.Probability.InvariantIsing.Magnetic.MagneticFullFieldUpper
import OAI.Probability.InvariantIsing.Cavity.CavityOrientedFamily
import OAI.Probability.InvariantIsing.Cavity.CavityGroupPartition

namespace OAI

/-! The finite-field upper bound for physical orthogonal Haar matrices,
with arbitrary finite eigenvalue and field labelings at every dimension. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem finite_physical_field_pressure_upper
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    {m : ℕ} (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (e : (M : ℕ) → Fin M → Fin m)
    (he : Tendsto (fun M a => (spinGroupSize (e M) a : ℝ)/M) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (g : (M : ℕ) → Fin M → A) (γ b : A → ℝ)
    (hγ : ∀ a, 0 < γ a) (hγsum : ∑ a, γ a=1)
    (hg : Tendsto (fun M a => (spinGroupSize (g M) a : ℝ)/M) atTop (𝓝 γ)) :
    ∀ ε > 0, ∀ᶠ M in atTop,
      (∫ V, rotatedPressure (fun i => lam (e M i)) (matrixRotation V⁻¹)
        (fun i => b (g M i)) ∂μ M) ≤
      (finiteMagneticFunctional (finiteR ρ lam hρ hsum) γ b).toReal+ε := by
  let N := fun k : ℕ => k+3
  have hN k : 0 < N k := by dsimp only [N]; omega
  let ν := fun k => cavityOrientedBaseLaw (hN k) (μ (N k))
  let K := 1+∑ a, |lam a|
  have hK : 0 < K := by dsimp only [K]; positivity
  have heig k i : |lam (e (N k) i)|≤K := by
    have hh := Finset.single_le_sum (f := fun a => |lam a|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ (e (N k) i))
    dsimp only [K]
    linarith
  have hh := finiteSpectrum_fullField_pressure_upper hhaar hgauss N (fun _ => by dsimp only [N]; omega)
    (tendsto_add_atTop_nat 3) m ν
    (fun k => cavityOrientedBaseLaw_leftInvariant _ _) (fun k i => lam (e (N k) i)) K hK heig
    (fun k => cavitySpectralGroup (e (N k))) (fun _ => cavitySpectralGroup_pairwiseDisjoint _)
    (fun _ => cavitySpectralGroup_cover _) lam
    (by intro k a i hi; rw [(Finset.mem_filter.mp hi).2]) ρ hρ hsum
    (he.comp (tendsto_add_atTop_nat 3)) (fun k => g (N k)) γ b hγ hγsum
    (hg.comp (tendsto_add_atTop_nat 3))
  intro ε hε
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (hh ε hε)
  apply eventually_atTop.mpr
  refine ⟨J+3,fun M hM => ?_⟩
  obtain ⟨k,rfl⟩ : ∃ k, M=k+3 := ⟨M-3,(Nat.sub_add_cancel (by omega)).symm⟩
  have hx := hJ k (by omega)
  rw [cavity_oriented_pressure] at hx
  exact hx

end InvariantIsing

end

end OAI
