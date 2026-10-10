import OAI.Probability.InvariantIsing.Magnetic.MagneticPhysicalIncrementLower
import OAI.Probability.InvariantIsing.Cavity.ConsecutivePhysicalIncrement

namespace OAI

/-! Physical constrained pressures inherit the magnetic variational lower
bound from the proved block increment, with actual minimizing perturbations. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_physical_constrained_pressure_lower
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
    ∃ r, ∀ ε > 0, ∀ᶠ j in atTop,
      let q := m*N r-N r+N r+3
      let M := (q+j)*N r
      let g := cavityRationalLabel (by omega : 0 < m) (spec r) (hspec r) M
      L-ε ≤ ∫ V, restrictedRotatedPressure
        (consecutiveBlockConstraint (N r) (q+j) (spinGroupSlice (group r) (k r)))
        (fun i => lam (g i)) (matrixRotation V⁻¹) (fun _ => 0) ∂μ M := by
  let ν := cavityOrientedFamily μ
  have hν M : (ν M).IsMulLeftInvariant := cavityOrientedFamily_leftInvariant μ M
  let g := fun r M => cavityRationalLabel (by omega : 0 < m) (spec r) (hspec r) M
  let eig := fun r M i => lam (g r M i)
  let I := fun r M => cavitySpectralGroup (g r M)
  let C := fun r => spinGroupSlice (group r) (k r)
  have hC r : (C r).Nonempty := spinGroupSlice_nonempty (group r) (k r) (hk r)
  let q := fun r => m*N r-N r+N r+3
  choose U V hU hV hmin using fun r => repeated_prior_minimizing_sequence hhaar hgauss
    ν hν (eig r) (fun _ _ => 0) (I r) (C r) (hC r)
  let u : (r j : ℕ) → Fin (cavityRationalSize (N r) (m*N r-N r) j) → ℝ :=
    fun r j => U r (j+q r)
  let v := fun r j => V r (j+q r)
  have hum r j i : u r j i ∈ Set.Icc (1 : ℝ) 2 := hU r (j+q r) i
  have hvm r j a : v r j a ∈ Set.Icc (1 : ℝ) 2 := hV r (j+q r) a
  have hmm r j (u' : Fin (cavityRationalSize (N r) (m*N r-N r) j) → ℝ) (v' : Fin m → ℝ)
      (hu' : ∀ i, u' i ∈ Set.Icc (1 : ℝ) 2) (hv' : ∀ a, v' a ∈ Set.Icc (1 : ℝ) 2) :
      rationalConstrainedObjective hm (hN r) (spec r) (hspec r) (C r) (hC r) μ lam j (u r j) (v r j) ≤
        rationalConstrainedObjective hm (hN r) (spec r) (hspec r) (C r) (hC r) μ lam j u' v' := by
    have hdim : 3 ≤ (j+q r)*N r := cavityRationalSize_ge_three (N r) (m*N r-N r) j (hN r)
    have hh := hmin r (j+q r) hdim u' v' hu' hv'
    have hp : 0 < (j+q r)*N r := by omega
    simpa only [repeatedPriorObjective, rationalConstrainedObjective, ν,
      cavityOrientedFamily_pos μ hp, eig, I, g, u, v, q, cavityRationalSize] using hh
  obtain ⟨r,hr⟩ := magnetic_rational_increment_eventually_lower hhaar hgauss hpub hm
    ρ lam hρ hsum hK hlam amax hmax μ N hN hNlim spec hsp hspec hρspec
    group k hk γ mag hγ hγsum hcount hs hmag hc u v hum hvm hmm L hL
  have hdim j : 3 ≤ (q r+j)*N r := by
    simpa only [q, cavityRationalSize, Nat.add_comm] using cavityRationalSize_ge_three (N r) (m*N r-N r) j (hN r)
  have hh := consecutive_envelope_pressure_lower hhaar hgauss (hN r) (by simpa using hdim 0)
    ν (fun M _ => hν M) (eig r) (fun _ _ => 0) (I r) (C r) (hC r)
    (fun j => U r (q r+j)) (fun j => V r (q r+j))
    (fun j => hU r (q r+j)) (fun j => hV r (q r+j))
    (fun j => hmin r (q r+j) (hdim j)) L (by
      intro ε hε
      filter_upwards [hr] with j hj
      have he := consecutive_prior_increment_physical hhaar hgauss μ (eig r) (I r) (C r) (hC r)
        (fun j => U r (q r+j)) (fun j => V r (q r+j)) (fun j => hU r (q r+j)) j (hdim j)
      rw [he]
      have hi : rationalRestrictedIncrement hm (hN r) (spec r) (hspec r) (C r) (hC r) μ lam (u r) (v r) j =
          repeatedRotationIncrement μ (eig r) (I r) (C r) (hC r) (q r+j) (U r (q r+j)) (V r (q r+j)) := by
        change repeatedRotationIncrement μ (eig r) (I r) (C r) (hC r) (j+q r)
          (U r (j+q r)) (V r (j+q r)) = _
        rw [Nat.add_comm j (q r)]
      rw [hi] at hj
      have hj' := (sub_le_self L hε.le).trans hj.le
      simpa only [div_eq_mul_inv, mul_comm] using hj')
  refine ⟨r,?_⟩
  intro ε hε
  filter_upwards [hh ε hε] with j hj
  dsimp only [ν] at hj
  rw [cavityOrientedFamily_pos μ (by have := hdim j; omega), cavity_oriented_restricted_pressure] at hj
  exact hj

end InvariantIsing

end

end OAI
