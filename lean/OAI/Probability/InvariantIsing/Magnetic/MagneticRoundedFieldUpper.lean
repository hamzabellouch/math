import OAI.Probability.InvariantIsing.Magnetic.MagneticConvergingFieldUpper
import OAI.Probability.InvariantIsing.Magnetic.MagneticGroupRounding
import OAI.Probability.InvariantIsing.Magnetic.MagneticFiniteTrial
import OAI.Probability.InvariantIsing.Core.FiniteVariationalBounds
import OAI.Probability.InvariantIsing.Fields.SpinGroupFieldPressure
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPressureFluctuation

namespace OAI

/-! The finite-spectrum pressure upper bound after taking the path infimum,
under Haar and Gaussian concentration hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem finiteSpectrum_magneticRoundedFieldPressure_upper
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : ∀ k, Fin (N k) → A)
    (γ b : A → ℝ) (hγ : ∀ a, 0<γ a) (hγsum : ∑ a, γ a=1)
    (hgroup : Tendsto (fun k a => (spinGroupSize (group k) a:ℝ)/(N k:ℝ)) atTop (𝓝 γ))
    (q : RationalMagnetization A) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ k in atTop,
      (∫ U, restrictedRotatedPressure (spinGroupSlice (group k)
        (fun a => magneticRoundedCount (spinGroupSize (group k) a) (q.val a:ℝ)))
        (eig k) (specialRotation U) (fun i => b (group k i)) ∂μ k) ≤
        (finiteMagneticFunctional (finiteR ρ lam hρpos hρsum) γ b).toReal+ε := by
  let mag := fun a => (q.val a:ℝ)
  let γs := fun k a => (spinGroupSize (group k) a:ℝ)/(N k:ℝ)
  let mags := fun k a => magneticRoundedValue (spinGroupSize (group k) a) (mag a)
  let cnt := fun k a => magneticRoundedCount (spinGroupSize (group k) a) (mag a)
  have hm : Tendsto mags atTop (𝓝 mag) := rounded_group_magnetizations_tendsto
    N hNlim group γ mag hγ (fun a => (q.property a).le) hgroup
  have hg k a : (spinGroupSize (group k) a:ℝ)=N k*γs k a := by
    dsimp only [γs]
    have hn : (N k:ℝ)≠0 := Nat.cast_ne_zero.mpr (by have := hN k; omega)
    field_simp
  have hu := finiteSpectrum_magneticFieldPressure_converging_upper hhaar hgauss
    N hN hNlim m μ hμinv eig K hK heig I hdis hcover lam hlam ρ hρpos hρsum hρ
    group cnt (fun k a => magneticRoundedCount_le _ (q.property a).le)
    γs mags γ mag hgroup hm (fun a => (hγ a).le) hγsum q.property
    (fun k a => magneticRoundedCount_value _ (q.property a).le) hg b
  intro ε hε
  filter_upwards [hu ε hε] with k hk
  have hb := finiteMagnetic_trial_le ρ lam hρpos hρsum γ b (fun a => (hγ a).le) hγsum q
  dsimp only [mag] at hk
  linarith

end InvariantIsing

end

end OAI
