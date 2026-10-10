import OAI.Probability.InvariantIsing.Cavity.OffsetAffineSubsequenceTrial
import OAI.Probability.InvariantIsing.Magnetic.MagneticTrialBarrier

namespace OAI

/-! A physical constrained block has eventually large cavity increments whenever
the proposed pressure level is below the magnetic variational value. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace InvariantIsing

def affineConstrainedObjective {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (spec c : Fin m → ℕ) (hspec : ∑ a, spec a=n)
    (R : Finset (Spin (∑ a, c a))) (hR : R.Nonempty)
    (Cset : Finset (Spin n)) (hCset : Cset.Nonempty)
    (μ : (M : ℕ) → Measure (Orthogonal M)) (lam : Fin m → ℝ) (j : ℕ)
    (u : Fin (cavityPrefixAffineSize n (m*n-n+n+3) c j) → ℝ) (v : Fin m → ℝ) : ℝ :=
  let M := cavityPrefixAffineSize n (m*n-n+n+3) c j
  let g := cavityAffineLabel (by omega : 0 < m) spec c hspec M
  priorPerturbationObjective (cavityOrientedBaseLaw (by
    have hh := cavityRationalSize_ge_three n (m*n-n) j hn;
    exact lt_of_lt_of_le (by norm_num : 0<3)
      (hh.trans (Nat.le_add_left _ (∑ a, c a)))) (μ M))
    (restrictedZeroTreePrior (offsetBlockConstraint (j+(m*n-n+n+3)) R Cset)
      (offsetBlockConstraint_nonempty R hR Cset hCset))
    (fun i => lam (g i)) (fun _ => 0) (cavitySpectralGroup g) 1 (fun _ => 0) u v

theorem magnetic_affine_increment_eventually_lower
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
    (c : ℕ → Fin m → ℕ)
    (R : (r : ℕ) → Finset (Spin (∑ a, c r a))) (hR : ∀ r, (R r).Nonempty)
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : ∀ r, Fin (N r) → A) (k : ℕ → A → ℕ)
    (hk : ∀ r a, k r a ≤ spinGroupSize (group r) a)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hcount : ∀ r a, (spinGroupSize (group r) a : ℝ)=N r*γ a)
    {s : ℝ} (hs : s < 1) (hmag : ∀ a, |mag a| ≤ s)
    (hc : ∀ r a, (k r a : ℝ)=spinGroupSize (group r) a*((1+mag a)/2))
    (u : (r j : ℕ) → Fin (cavityPrefixAffineSize (N r) (m*N r-N r+N r+3) (c r) j) → ℝ)
    (v : ℕ → ℕ → Fin m → ℝ)
    (hu : ∀ r j i, u r j i ∈ Set.Icc (1 : ℝ) 2)
    (hv : ∀ r j a, v r j a ∈ Set.Icc (1 : ℝ) 2)
    (hmin : ∀ r j u' v', (∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) →
      (∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) →
      affineConstrainedObjective hm (hN r) (spec r) (c r) (hspec r) (R r) (hR r)
        (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
        μ lam j (u r j) (v r j) ≤
      affineConstrainedObjective hm (hN r) (spec r) (c r) (hspec r) (R r) (hR r)
        (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r)) μ lam j u' v')
    (L : ℝ) (hL : L < (magneticVariationalFunctional (finiteR ρ lam hρ hsum) γ mag).toReal) :
    ∃ r, ∀ᶠ j in atTop, L < (N r : ℝ)⁻¹*
      (affineRestrictedIncrement hm (hN r) (spec r) (c r) (hspec r) (R r) (hR r)
        (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
        μ lam (u r) (v r) j +
        (Real.log (spinGroupSlice (group r) (k r)).card-N r*Real.log 2)) := by
  let Δ := fun r j => (N r : ℝ)⁻¹*
    (affineRestrictedIncrement hm (hN r) (spec r) (c r) (hspec r) (R r) (hR r)
      (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
      μ lam (u r) (v r) j + (Real.log (spinGroupSlice (group r) (k r)).card-N r*Real.log 2))
  change ∃ r, ∀ᶠ j in atTop, L < Δ r j
  by_contra hnone
  have hbad r : ∃ ι : ℕ → ℕ, StrictMono ι ∧ ∀ j, Δ r (ι j) ≤ L := by
    have hn : ¬∀ᶠ j in atTop, L < Δ r j := fun h => hnone ⟨r,h⟩
    have hf : ∃ᶠ j in atTop, ¬L < Δ r j := by
      simpa only [Filter.Frequently, not_not] using hn
    obtain ⟨ι,hι,hb⟩ := extraction_of_frequently_atTop hf
    exact ⟨ι,hι,fun j => not_lt.mp (hb j)⟩
  choose ι hι hbad using hbad
  have hpaths r : ∃ p : OverlapPath,
      (∀ Φ : ℝ →ᵇ ℝ, Tendsto (fun j => ∫ t, Φ (cavityStrictUniformPath p j t)*
        (restrictedBlockOverlapPath (hN r) (spinGroupSlice (group r) (k r))
          (spinGroupSlice_nonempty (group r) (k r) (hk r))
          (cavityStrictUniformField ρ lam hρ hsum p j) t-cavityStrictUniformPath p j t)
          ∂pathMeasure) atTop (𝓝 0)) ∧
      ∀ ε > 0, ∀ᶠ j in atTop,
        constrainedBlockValue (spinGroupSlice (group r) (k r)) (cavityStrictUniformField ρ lam hρ hsum p j)+
        fieldPairing (cavityStrictUniformPath p j) (cavityStrictUniformField ρ lam hρ hsum p j)/2+
        spectralFunctional (finiteR ρ lam hρ hsum) (cavityStrictUniformPath p j) ≤ L+ε := by
    have he : (fun a => (spec r a : ℝ)/(N r : ℝ))=ρ := by
      funext a
      rw [hρspec r a, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (hN r).ne')]
    have hReq : finiteR (fun a => (spec r a : ℝ)/(N r : ℝ)) lam
        (cavityRationalMass_positive (spec r) (hsp r) (hN r))
        (cavityRationalMass_sum (spec r) (hspec r) (hN r)) = finiteR ρ lam hρ hsum := by
      subst ρ
      rfl
    obtain ⟨p,φ,hφ,hself,htrial⟩ := offset_affine_subsequence_trial_witness
      hhaar hgauss hpub hm (hN r) (spec r) (c r) (hsp r) (hspec r) (R r) (hR r)
      (spinGroupSlice (group r) (k r)) (spinGroupSlice_nonempty (group r) (k r) (hk r))
      μ lam amax hmax (ι r) (hι r) (u r) (v r) (hu r) (hv r) (hmin r)
    simp only [hReq, he] at hself htrial
    refine ⟨p,hself,?_⟩
    intro ε hε
    filter_upwards [htrial ε hε] with j hj
    have hb := hbad r (φ j)
    dsimp only [Δ] at hb
    linarith
  choose base htest hupper using hpaths
  exact (not_le_of_gt hL) (magnetic_trial_barrier ρ lam hρ hsum hK hlam N hN hNlim
    group k hk γ mag hγ hγsum hcount hs hmag hc base htest L hupper)

end InvariantIsing

end

end OAI
