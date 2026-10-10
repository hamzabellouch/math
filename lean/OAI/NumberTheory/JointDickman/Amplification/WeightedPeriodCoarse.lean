import OAI.NumberTheory.JointDickman.Amplification.WeightedPeriodLaw
import OAI.NumberTheory.JointDickman.Amplification.BoundedBoxCoarse

namespace OAI

/-! # From the original Fourier expression to the coarse spatial kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem weighted_geometric_period_coarse_comparison
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
      ∃ H : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
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
        ε B+C*(T/j)*((j : ℝ)/j.totient)*singularSeriesTail (Q+1)+δ*(T/j)*singularSeries j := by
  obtain ⟨c,hc,hcpos,H,ε₁,hε₁,hperiod⟩ := weighted_geometric_period_model_vanishing
    hSD hSW hM hMP ha hab hl hlu ht hη w₁ w₂ w w' hR hMb hM₀ hD₀
    hwb₁ hwb₂ hw hw' hwb hwd hsupp
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  obtain ⟨C,hC,ε₂,hε₂,hcoarse⟩ := bounded_box_coarse_comparison hSD hSW hM hMP
    (mul_nonneg hR hD) ha hab ht hη w₁ w₂ w₁' w₂' w hMb hMb hD₁ hD₂ hM₀
    hw₁ hw₂ hwb₁ hwb₂ hwd₁ hwd₂ hwb hs₁ hs₂
  refine ⟨c,hc,hcpos,H,C,hC,fun B => ε₁ B+ε₂ B,by simpa using hε₁.add hε₂,?_⟩
  intro δ hδ
  obtain ⟨m,hm,hcoarseB⟩ := hcoarse δ hδ
  refine ⟨m,hm,?_⟩
  filter_upwards [hperiod,hcoarseB,hden,eventually_ge_atTop 1] with B hp hcB hd hB
  intro j _ Q hQ hscale hcut T hT hlag S hbox hlog r hr g h hg hh
  dsimp only
  have hjB : j ≤ B := (Nat.le_mul_of_pos_right j hQ).trans hscale
  have hscale' : η*T ≤ (B : ℝ) := hlag.trans (by exact_mod_cast hjB)
  have hp' := hp T hT hscale' S hbox hlog r hr j Q hcut g h hg hh
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hrd : ∀ k ∈ S, |r k*coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)| ≤ R*D := by
    intro k hk
    rw [abs_mul]
    apply mul_le_mul (hr k hk) _ (abs_nonneg _) hR
    apply hd.1
    apply (le_div_iff₀ hBpos).mpr
    nlinarith [(hlog k hk).1]
  have hc' := hcB j Q hQ hscale T hT hlag S hbox
    (fun k => r k*coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)) hrd g h hg hh
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (weightedGeometricPeriodSum B j a b T t S r g h w₁ w₂ w)
    (geometricFullArcSum B j Q a b T t S
      (fun k => r k*coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B))
      g h w₁ w₂ w)
    (((singularSeries j : ℂ)/j)*
      (cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h)
        (geometricWindowKernel m B t (Real.log a) (Real.log b) S
          (endpointSpatialWeight m B t (T/j)
            (fun k => r k*coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B))
            w₁ w₂ w)) : ℂ))
  have he := (mul_le_mul_of_nonneg_left htri hT.le).trans_eq (mul_add _ _ _)
  exact (he.trans (add_le_add hp' hc')).trans_eq (by ring)

end JointDickman

end OAI
