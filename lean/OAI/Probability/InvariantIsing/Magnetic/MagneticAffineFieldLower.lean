import OAI.Probability.InvariantIsing.Magnetic.MagneticAffinePressureLower
import OAI.Probability.InvariantIsing.Cavity.OffsetFieldPressure

namespace OAI

/-! The magnetic variational lower bound contributes to the full physical
pressure along a sequence of repeated finite field blocks. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators
namespace InvariantIsing

theorem magnetic_affine_field_subsequence_lower
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
    (b : A → ℝ) (L : ℝ) (hL : L < (magneticVariationalFunctional (finiteR ρ lam hρ hsum) γ mag).toReal) :
    ∃ r, ∀ ε > 0, ∀ᶠ j in atTop,
      let q := m*N r-N r+N r+3
      let M := (∑ a, c r a)+(q+j)*N r
      let g := cavityAffineLabel (by omega : 0 < m) (spec r) (c r) (hspec r) M
      L+(∑ a, γ a*b a*mag a)-ε ≤ ∫ V, rotatedPressure
        (fun i => lam (g i)) (matrixRotation V⁻¹)
        (offsetBlockField (∑ a, c r a) (q+j) (fun i => b (group r i))) ∂μ M := by
  obtain ⟨r,hr⟩ := magnetic_affine_constrained_pressure_lower hhaar hgauss hpub hm
    ρ lam hρ hsum hK hlam amax hmax μ N hN hNlim spec hsp hspec hρspec c R hR
    group k hk γ mag hγ hγsum hcount hs hmag hc L hL
  refine ⟨r,?_⟩
  intro ε hε
  let q := m*N r-N r+N r+3
  let F := ∑ a, γ a*b a*mag a
  have hq0 : 0<q := by dsimp only [q]; omega
  have hflim := offset_field_fraction_tendsto (hN r) (∑ a, c r a) q hq0 F
  filter_upwards [hr (ε/2) (half_pos hε),
    Metric.tendsto_nhds.mp hflim (ε/2) (half_pos hε)] with j hj hfj
  have hq : 0 < q+j := by dsimp only [q]; omega
  have hM : ∀ σ ∈ spinGroupSlice (group r) (k r),
      fieldEnergy (fun i => b (group r i)) σ=(N r : ℝ)*F := by
    intro σ hσ
    rw [fieldEnergy_on_group_slice (group r) (k r) b hσ,
      spinGroupFieldConstant_magnetization (group r) (k r) b γ mag (hcount r) (hc r)]
  have hdim : 0<(∑ a, c r a)+(q+j)*N r :=
    Nat.add_pos_right _ (Nat.mul_pos hq (hN r))
  have hh := mean_offset_field_pressure_lower hdim (μ ((∑ a, c r a)+(q+j)*N r))
    (R r) (hR r) (spinGroupSlice (group r) (k r))
    (spinGroupSlice_nonempty (group r) (k r) (hk r))
    (fun i => b (group r i)) ((N r : ℝ)*F) hM
    (fun i => lam (cavityAffineLabel (by omega : 0 < m) (spec r) (c r) (hspec r)
      ((∑ a, c r a)+(q+j)*N r) i))
  change L-ε/2 ≤ _ at hj
  rw [Real.dist_eq] at hfj
  have hfj' := (abs_lt.mp hfj).1
  change L+F-ε ≤ _
  simp only [Nat.cast_add, mul_assoc] at hh hfj'
  linarith

end InvariantIsing

end

end OAI
