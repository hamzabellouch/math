import OAI.NumberTheory.JointDickman.Amplification.WeightedPeriodCoarse
import OAI.NumberTheory.JointDickman.Amplification.SingularTailRate

namespace OAI

/-! # Uniform vanishing of the retained-denominator tail -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem weighted_geometric_period_coarse_vanishing
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b l u t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hl : 0 < l) (hlu : l ≤ u)
    (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ w₁' w₂' : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) (w' : ℝ → ℝ)
    {M D₁ D₂ M₀ D₀ R : ℝ} (hR : 0 ≤ R) (hMb : 0 ≤ M) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
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
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ R) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let d := fun k : ℤ => coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)
      let K := geometricWindowKernel m B t (Real.log a) (Real.log b) S
        (endpointSpatialWeight m B t (T/j) (fun k => r k*d k) w₁ w₂ w)
      T*‖weightedGeometricPeriodSum B j a b T t S r g h w₁ w₂ w-
        ((singularSeries j : ℂ)/j)*
          (cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K : ℂ)‖ ≤
        ε B+δ*(T/j)*singularSeries j := by
  obtain ⟨c,hc,hcpos,H,C,hC,ε₁,hε₁,hcompare⟩ := weighted_geometric_period_coarse_comparison
    hSD hSW hM hMP ha hab hl hlu ht hη w₁ w₂ w₁' w₂' w w'
    hR hMb hD₁ hD₂ hM₀ hD₀ hw₁ hw₂ hwb₁ hwb₂ hwd₁ hwd₂ hs₁ hs₂ hw hw' hwb hwd hsupp
  obtain ⟨ε₂,hε₂,htail⟩ := singularSeriesTail_uniform_vanishing hMP
  refine ⟨c,hc,hcpos,H,fun B => ε₁ B+(C/η)*ε₂ B,?_,?_⟩
  · simpa using hε₁.add (hε₂.const_mul (C/η))
  intro δ hδ
  obtain ⟨m,hm,hcompareB⟩ := hcompare δ hδ
  refine ⟨m,hm,?_⟩
  filter_upwards [hcompareB,htail] with B hcB htB
  intro j _ Q hQ hscale hcut T hT hlag S hbox hlog r hr g h hg hh
  dsimp only
  have hj : 0 < j := Nat.pos_of_ne_zero (NeZero.ne j)
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hjB : j ≤ B := (Nat.le_mul_of_pos_right j hQ).trans hscale
  have hratio : T/(j : ℝ) ≤ 1/η := by
    apply (div_le_div_iff₀ hjr hη).mpr
    simpa only [one_mul,mul_one,mul_comm] using hlag
  have ht' := htB j Q hj hjB hcut
  have hpos : 0 ≤ ((j : ℝ)/j.totient)*singularSeriesTail (Q+1) :=
    mul_nonneg (by positivity) (singularSeriesTail_nonneg _)
  have herror : C*(T/j)*((j : ℝ)/j.totient)*singularSeriesTail (Q+1) ≤ (C/η)*ε₂ B := by
    calc
      _ = C*(T/j)*(((j : ℝ)/j.totient)*singularSeriesTail (Q+1)) := by ring
      _ ≤ C*(1/η)*(((j : ℝ)/j.totient)*singularSeriesTail (Q+1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hC) hpos
      _ ≤ C*(1/η)*ε₂ B := mul_le_mul_of_nonneg_left ht' (by positivity)
      _ = _ := by ring
  have hfinal := hcB j Q hQ hscale hcut T hT hlag S hbox hlog r hr g h hg hh
  dsimp only at hfinal
  linarith

end JointDickman

end OAI
