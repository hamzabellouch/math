import OAI.NumberTheory.TwoPoint.Walks.SelectedCenteringIdentity
import OAI.NumberTheory.TwoPoint.Walks.SelectedRawLowerBound

namespace OAI

/-! The phase-selected raw lower bound holds at every sufficiently long
biased original cutoff, using exactly the graph's logarithmic bins. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical Topology

theorem selected_raw_bins_lower {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (D Q : Finset ℕ) (hD : ∀ d ∈ D, 0 < d) (hQ : ∀ p ∈ Q, p.Prime)
    (L η γ : ℝ) (hη : 0 < η) (hγ : 0 < γ)
    (A : Finset (ℕ × ℕ))
    (hA : A ⊆ eligibleComplexPairs D Q (PaddingPairEligible L η))
    (h : ℕ) (hmass : 0 < totalPaddingBinMass D Q L η)
    (hphase : totalPaddingBinMass D Q L η / 8 ≤ ‖selectedRawCoefficient A f g‖)
    (hcost : (∑ dq ∈ A, complexPairWeight dq *
      ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) ≤
        γ * totalPaddingBinMass D Q L η / 128)
    (hsmall : η ≤ γ / 128) :
    ∀ᶠ X : ℝ in atTop,
      γ ≤ ‖positivePrefix (fun n => f n * g (n + h)) ⌊X⌋₊ / (X : ℂ)‖ →
      γ * totalPaddingBinMass D Q L η / 16 ≤
        ‖selectedRawMean A (fun dq => X * Real.exp
          ((paddingBin η 0 (Real.log (dq.1 * dq.2 : ℕ)) : ℝ) * η)) f g h‖ := by
  let mass := totalPaddingBinMass D Q L η
  let K := mass + ∑ dq ∈ A,
    4 * actualPaddingCoefficient dq.2 * (dq.1 * dq.2).primeFactors.card
  have ht : Tendsto (fun X : ℝ => K / X) atTop (𝓝 0) := tendsto_id.const_div_atTop K
  have hε : 0 < γ * mass / 64 := by dsimp only [mass]; positivity
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)]
    with X hlong hX
  intro hbias
  have hprop (dq : ℕ × ℕ) (hdq : dq ∈ A) :
      0 < dq.1 ∧ 0 < dq.2 ∧ PaddingPairEligible L η dq.1 dq.2 ∧
        actualPaddingBin η (Real.log dq.1)
          (paddingBin η 0 (Real.log (dq.1 * dq.2 : ℕ))) dq.2 :=
    selectedPairBin_properties D Q hD hQ A L η hη hA ⟨hdq, rfl⟩
  apply selectedRawMean_lower_bound hfm hgm hf hg A _ h X η mass γ hX hη.le hmass.le hγ.le
    (fun dq hdq => Nat.mul_pos (hprop dq hdq).1 (hprop dq hdq).2.1)
    (fun dq hdq => (actualPaddingBin_cutoff dq.1 dq.2 (hprop dq hdq).1
      (hprop dq hdq).2.1 η X hX _ (hprop dq hdq).2.2.2).1)
    (fun dq hdq => (actualPaddingBin_cutoff dq.1 dq.2 (hprop dq hdq).1
      (hprop dq hdq).2.1 η X hX _ (hprop dq hdq).2.2.2).2)
    _ (selected_pair_mass_le D Q A L η hη hA) hphase hcost hsmall hlong.le hbias
  intro dq hdq
  have hi := (mem_paddingBinIndices_iff L η _ hη).mp
    (selectedPairBin_index D Q A L η hA hdq)
  have hiR : (0 : ℝ) ≤ paddingBin η 0 (Real.log (dq.1 * dq.2 : ℕ)) := by
    exact_mod_cast hi.1
  exact le_mul_of_one_le_right hX.le (Real.one_le_exp (mul_nonneg hiR hη.le))

end TwoPointCorrelations

end OAI
