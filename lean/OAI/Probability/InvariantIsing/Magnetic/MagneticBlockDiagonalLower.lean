import OAI.Probability.InvariantIsing.Magnetic.MagneticDiagonalSelection
import OAI.Probability.InvariantIsing.Magnetic.MagneticBlockTrialLower

namespace OAI

/-! Weak tests on growing physical blocks yield the magnetic variational trial lower bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

theorem magnetic_block_diagonal_trial_lower {m : ℕ}
    (ρ lam : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    {K : ℝ} (hK : 0 ≤ K) (hlam : ∀ a, |lam a| ≤ K)
    {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ r, 0 < N r) (hNlim : Tendsto N atTop atTop)
    (group : ∀ r, Fin (N r) → A) (k : ℕ → A → ℕ)
    (hk : ∀ r a, k r a ≤ spinGroupSize (group r) a)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ r a, (spinGroupSize (group r) a : ℝ)=N r*γ a)
    {s : ℝ} (hs : s < 1) (hmag : ∀ a, |mag a| ≤ s)
    (hc : ∀ r a, (k r a : ℝ)=spinGroupSize (group r) a*((1+mag a)/2))
    (base : ℕ → OverlapPath)
    (htest : ∀ r (Φ : ℝ →ᵇ ℝ), Tendsto (fun j => ∫ t, Φ (cavityStrictUniformPath (base r) j t)*
        (restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
          (spinGroupSlice_nonempty (group r) (k r) (hk r))
          (cavityStrictUniformField ρ lam hρ hsum (base r) j) t-
          cavityStrictUniformPath (base r) j t) ∂pathMeasure) atTop (𝓝 0)) :
    ∃ d φ : ℕ → ℕ, StrictMono d ∧ StrictMono φ ∧
      ∀ ε > 0, ∀ᶠ r in atTop,
        (magneticVariationalFunctional (finiteR ρ lam hρ hsum) γ mag).toReal-ε ≤ constrainedBlockValue (spinGroupSlice (group (φ r)) (k (φ r)))
            (cavityStrictUniformField ρ lam hρ hsum (base (φ r)) (d (φ r)))+
          fieldPairing (cavityStrictUniformPath (base (φ r)) (d (φ r)))
            (cavityStrictUniformField ρ lam hρ hsum (base (φ r)) (d (φ r)))/2+
          spectralFunctional (finiteR ρ lam hρ hsum)
            (cavityStrictUniformPath (base (φ r)) (d (φ r))) := by
  obtain ⟨d,φ,p,hd,hφ,hq,hself⟩ := exists_magnetic_consistent_diagonal
    ρ lam hρ hsum hK hlam N hN hNlim group k hk (fun _ => mag) hs
      (fun _ => hmag) hc base htest
  refine ⟨d,φ,hd,hφ,?_⟩
  exact magnetic_block_trial_eventually_lower ρ lam hρ hsum
    (fun r => N (φ r)) (fun r => hN (φ r)) (hNlim.comp hφ.tendsto_atTop)
    (fun r => group (φ r)) (fun r => k (φ r)) (fun r => hk (φ r)) γ mag hγ hγsum
    (fun r => hcount (φ r)) hs hmag (fun r => hc (φ r))
    (fun r => cavityStrictUniformField ρ lam hρ hsum (base (φ r)) (d (φ r)))
    (fun r => cavityStrictUniformField_height_le ρ lam hρ hsum hK hlam
      (base (φ r)) (d (φ r)) (Fin.last (d (φ r)))) p
    (fun r => cavityStrictUniformPath (base (φ r)) (d (φ r))) hself hq

end InvariantIsing

end

end OAI
