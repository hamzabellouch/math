import OAI.NumberTheory.JointDickman.Amplification.PeriodCoarseVanishing
import OAI.NumberTheory.JointDickman.Amplification.GeometricArithmeticIdentity
import OAI.NumberTheory.JointDickman.Probability.GroupedKernelFeatures

namespace OAI

/-! # The separated arithmetic kernel has a finite-feature approximation -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem geometric_arithmetic_feature_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b l u t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl : 0 < l) (hlu : l ≤ u)
    (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ w₁' w₂' : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) (w' : ℝ → ℝ)
    {M D₁ D₂ M₀ D₀ : ℝ} (hMb : 0 ≤ M) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hM₀ : 0 ≤ M₀) (hD₀ : 0 ≤ D₀)
    (hw₁ : ∀ x, HasDerivAt w₁ (w₁' x) x) (hw₂ : ∀ x, HasDerivAt w₂ (w₂' x) x)
    (hwb₁ : ∀ x, |w₁ x| ≤ M) (hwb₂ : ∀ x, |w₂ x| ≤ M)
    (hwd₁ : ∀ x, |w₁' x| ≤ D₁) (hwd₂ : ∀ x, |w₂' x| ≤ D₂)
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0)
    (hw : ∀ x, HasDerivAt w (w' x) x) (hw' : Continuous w')
    (hwb : ∀ x, |w x| ≤ M₀) (hwd : ∀ x, |w' x| ≤ D₀)
    (hsupp : ∀ x, x ≤ l ∨ u < x → w x = 0) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
      (B : ℝ)^(2/5 : ℝ) ≤ Q →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      (∀ k ∈ S, Real.log (Real.exp ((k : ℝ)*t)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let d := fun k : ℤ => coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
      let K := geometricWindowKernel m B t (Real.log a) (Real.log b) S
        (endpointSpatialWeight m B t (T/j) d w₁ w₂ w)
      T*|geometricArithmeticSum B j a b l u T t S g h w₁ w₂ w-
        (singularSeries j/(j : ℝ))*
          (∑ x, ∑ y, fullPrimeMass (auxiliaryPrimes B) x*fullPrimeMass (auxiliaryPrimes B) y*
            g x*h y*primeCoarseKernel m B K x y)| ≤
        ε B+δ*(T/j)*singularSeries j := by
  obtain ⟨c,hc,hcpos,H,ε,hε,hcompare⟩ := geometric_period_coarse_vanishing
    hSD hSW hM hMP ha hab hl hlu ht hη w₁ w₂ w₁' w₂' w w'
    hMb hD₁ hD₂ hM₀ hD₀ hw₁ hw₂ hwb₁ hwb₂ hwd₁ hwd₂ hs₁ hs₂ hw hw' hwb hwd hsupp
  refine ⟨c,hc,hcpos,H,ε,hε,?_⟩
  intro δ hδ
  obtain ⟨m,hm,hcompareB⟩ := hcompare δ hδ
  refine ⟨m,hm,?_⟩
  filter_upwards [hcompareB,eventually_gt_atTop 0] with B hcB hB
  intro j _ Q hQ hscale hcut T hT hlag S hbox hlog g h hg hh
  dsimp only
  have he := hcB j Q hQ hscale hcut T hT hlag S hbox hlog g h hg hh
  dsimp only at he
  rw [geometricPeriodSum_eq_arithmeticSum B j hT hl hlu S g h w₁ w₂ w hsupp,
    coarseLogMassBilinear_eq_kernel_test hm hB] at he
  simpa only [← Complex.ofReal_natCast,← Complex.ofReal_div,← Complex.ofReal_mul,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using he

end JointDickman

end OAI
