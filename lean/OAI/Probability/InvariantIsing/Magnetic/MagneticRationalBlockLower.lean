import OAI.Probability.InvariantIsing.Cavity.ConsecutiveRationalConsistency
import OAI.Probability.InvariantIsing.Magnetic.MagneticBlockDiagonalLower

namespace OAI

/-! Actual rational-spectrum block laws supply the diagonal magnetic trial lower bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem magnetic_rational_block_diagonal_lower
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m : ℕ} (hm : 2 ≤ m) (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    (amax : Fin m) (hmax : ∀ a, lam a ≤ lam amax)
    (μ : (M : ℕ) → Measure (Orthogonal M)) [∀ M, IsProbabilityMeasure (μ M)]
    [∀ M, (μ M).IsMulRightInvariant]
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r) (hNlim : Tendsto N atTop atTop)
    (spec : ℕ → Fin m → ℕ) (hsp : ∀ r a, 0 < spec r a) (hspec : ∀ r, ∑ a, spec r a=N r)
    (hρspec : ∀ r a, (spec r a : ℝ)=(N r : ℝ)*ρ a)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : ∀ r, Fin (N r) → A) (k : ℕ → A → ℕ)
    (hk : ∀ r a, k r a ≤ spinGroupSize (group r) a)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ r a, (spinGroupSize (group r) a : ℝ)=N r*γ a)
    {s : ℝ} (hs : s < 1) (hmag : ∀ a, |mag a| ≤ s)
    (hc : ∀ r a, (k r a : ℝ)=spinGroupSize (group r) a*((1+mag a)/2)) :
    ∃ (base : ℕ → OverlapPath) (d φ : ℕ → ℕ), StrictMono d ∧ StrictMono φ ∧
      ∀ ε > 0, ∀ᶠ r in atTop,
        (magneticVariationalFunctional (finiteR ρ lam hρ hsum) γ mag).toReal-ε ≤ constrainedBlockValue (spinGroupSlice (group (φ r)) (k (φ r)))
            (cavityStrictUniformField ρ lam hρ hsum (base (φ r)) (d (φ r)))+
          fieldPairing (cavityStrictUniformPath (base (φ r)) (d (φ r)))
            (cavityStrictUniformField ρ lam hρ hsum (base (φ r)) (d (φ r)))/2+
          spectralFunctional (finiteR ρ lam hρ hsum)
            (cavityStrictUniformPath (base (φ r)) (d (φ r))) := by
  have htests (r : ℕ) : ∃ p : OverlapPath, ∀ Φ : ℝ →ᵇ ℝ,
      Tendsto (fun j => ∫ t, Φ (cavityStrictUniformPath p j t)*
        (restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
          (spinGroupSlice_nonempty (group r) (k r) (hk r))
          (cavityStrictUniformField ρ lam hρ hsum p j) t-cavityStrictUniformPath p j t)
          ∂pathMeasure) atTop (𝓝 0) := by
    have he : (fun a => (spec r a : ℝ)/(N r : ℝ))=ρ := by
      funext a
      rw [hρspec r a,mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (hN r).ne')]
    have hh := consecutive_rational_weak_self_consistency hhaar hgauss hpub hm (hN r)
      (spec r) (hsp r) (hspec r) (spinGroupSlice (group r) (k r))
      (spinGroupSlice_nonempty (group r) (k r) (hk r)) μ lam amax hmax
    simpa only [he] using hh
  choose base hb using htests
  obtain ⟨d,φ,hd,hφ,hlower⟩ := magnetic_block_diagonal_trial_lower
    ρ lam hρ hsum hK hlam N hN hNlim group k hk γ mag hγ hγsum hcount hs hmag hc base hb
  exact ⟨base,d,φ,hd,hφ,hlower⟩

end InvariantIsing

end

end OAI
