import OAI.Probability.InvariantIsing.Magnetic.RationalConstrainedMinima

namespace OAI

/-! A conditional physical cavity-increment lower bound with the actual
perturbation minima constructed, rather than assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_physical_increment_eventually_lower
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
    (hc : ∀ r a, (k r a : ℝ)=spinGroupSize (group r) a*((1+mag a)/2))
    (L : ℝ) (hL : L < (magneticVariationalFunctional (finiteR ρ lam hρ hsum) γ mag).toReal) :
    ∃ (r : ℕ) (u : (j : ℕ) → Fin (cavityRationalSize (N r) (m*N r-N r) j) → ℝ)
      (v : ℕ → Fin m → ℝ),
      (∀ j i, u j i ∈ Set.Icc (1 : ℝ) 2) ∧ (∀ j a, v j a ∈ Set.Icc (1 : ℝ) 2) ∧
      (∀ j u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) → (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
        rationalConstrainedObjective hm (hN r) (spec r) (hspec r)
          (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
          μ lam j (u j) (v j) ≤
        rationalConstrainedObjective hm (hN r) (spec r) (hspec r)
          (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r)) μ lam j u' v') ∧
      ∀ᶠ j in atTop, L < (N r : ℝ)⁻¹*
        (rationalRestrictedIncrement hm (hN r) (spec r) (hspec r)
          (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
          μ lam u v j + (Real.log (spinGroupSlice (group r) (k r)).card-N r*Real.log 2)) := by
  choose u v hu hv hmin using fun r => rational_constrained_minimizers_exist hhaar hgauss hm
    (hN r) (spec r) (hspec r) (spinGroupSlice (group r) (k r))
    (spinGroupSlice_nonempty (group r) (k r) (hk r)) μ lam
  obtain ⟨r,hr⟩ := magnetic_rational_increment_eventually_lower hhaar hgauss hpub hm
    ρ lam hρ hsum hK hlam amax hmax μ N hN hNlim spec hsp hspec hρspec
    group k hk γ mag hγ hγsum hcount hs hmag hc u v hu hv hmin L hL
  exact ⟨r,u r,v r,hu r,hv r,hmin r,hr⟩

end InvariantIsing

end

end OAI
